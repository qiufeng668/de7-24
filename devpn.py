#!/usr/bin/env python3
import re
"""DeVPN 一键拉节点（单文件，拷走即可跑）

    python3 devpn.py

流程：自动注册新账号 → 绑邀请码 → 领免费时长
     → 各地区并发各拉 10 轮并激活 → 保存 nodes.txt / last_account.json

依赖：
  - Python 3
  - 能访问外网

Ed25519 已内嵌纯 Python 实现；cryptography / pynacl 仅作为可选加速，
在 Juno / iOS 中无需安装。

不需要其它本地文件、配置、数据库。
"""
import base64
import hashlib
import json
import os
import random
import ssl
import sys
import time
import uuid
import urllib.error
import urllib.parse
import urllib.request

try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass

# ================================================================
# 内嵌：SM3 + SM2 加密（dsfunique，从 Hermes 字节码逆向，C1C3C2）
# ================================================================
_SM3_IV = bytes.fromhex("7380166f4914b2b9172442d7da8a0600a96f30bc163138aae38dee4db0fb0e4e")

def _rotl(x, n):
    n %= 32
    return ((x << n) | (x >> (32 - n))) & 0xFFFFFFFF

def sm3(msg: bytes) -> bytes:
    """标准 SM3，返回 32 字节。"""
    ml = len(msg) * 8
    msg = msg + b"\x80"
    while len(msg) % 64 != 56:
        msg += b"\x00"
    msg += ml.to_bytes(8, "big")
    v = [int.from_bytes(_SM3_IV[j:j + 4], "big") for j in range(0, 32, 4)]
    for i in range(0, len(msg), 64):
        block = msg[i:i + 64]
        w = list(int.from_bytes(block[j:j + 4], "big") for j in range(0, 64, 4))
        for j in range(16, 68):
            x = w[j - 16] ^ w[j - 9] ^ _rotl(w[j - 3], 15)
            w.append((x ^ _rotl(x, 15) ^ _rotl(x, 23)) ^ _rotl(w[j - 13], 7) ^ w[j - 6])
        wp = [w[j] ^ w[j + 4] for j in range(64)]
        a, b, c, d, e, f, g, h = v
        for j in range(64):
            if j < 16:
                t = 0x79CC4519
                ff = a ^ b ^ c
                gg = e ^ f ^ g
            else:
                t = 0x7A879D8A
                ff = (a & b) | (a & c) | (b & c)
                gg = (e & f) | ((~e & 0xFFFFFFFF) & g)
            ss1 = _rotl((_rotl(a, 12) + e + _rotl(t, j)) & 0xFFFFFFFF, 7)
            ss2 = ss1 ^ _rotl(a, 12)
            tt1 = (ff + d + ss2 + wp[j]) & 0xFFFFFFFF
            tt2 = (gg + h + ss1 + w[j]) & 0xFFFFFFFF
            d = c
            c = _rotl(b, 9)
            b = a
            a = tt1
            h = g
            g = _rotl(f, 19)
            f = e
            e = (tt2 ^ _rotl(tt2, 9) ^ _rotl(tt2, 17)) & 0xFFFFFFFF
        v = [x ^ y for x, y in zip(v, [a, b, c, d, e, f, g, h])]
    return b"".join(x.to_bytes(4, "big") for x in v)

# SM2 曲线参数 (sm2p256v1)
_P = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF
_A = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFC
_B = 0x28E9FA9E9D9F5E344D5A9E4BCF6509A7F39789F515AB8F92DDBCBD414D940E93
_N = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFF7203DF6B21C6052B53BBF40939D54123
_GX = 0x32C4AE2C1F1981195F9904466A39C9948FE30BBFF2660BE1715A4589334C74C7
_GY = 0xBC3736A2F4F6779C59BDCEE36B692153D0A9877CC62A474002DF32E52139F0A0
# App 内嵌的 SM2 公钥(04 前缀 + 64 字节) —— dsfunique 加密用
_PUBKEY_HEX = ("04d882d23c6d01534de563f8b10539ac32edf1a4c986ca59044567b86d6c652b2d"
               "34483ba97f9ea3c0950f36697ea858c966af56cc8682c83b83f57c843823aeff")
_PX = int(_PUBKEY_HEX[2:66], 16)
_PY = int(_PUBKEY_HEX[66:130], 16)

def _inv(x):
    return pow(x, _P - 2, _P)

def _point_add(p1, p2):
    if p1 is None:
        return p2
    if p2 is None:
        return p1
    x1, y1 = p1
    x2, y2 = p2
    if x1 == x2 and (y1 + y2) % _P == 0:
        return None
    if p1 == p2:
        lam = (3 * x1 * x1 + _A) * _inv(2 * y1) % _P
    else:
        lam = (y2 - y1) * _inv(x2 - x1) % _P
    x3 = (lam * lam - x1 - x2) % _P
    y3 = (lam * (x1 - x3) - y1) % _P
    return (x3, y3)

def _scalar_mul(k, pt):
    k = k % _N
    r = None
    while k:
        if k & 1:
            r = _point_add(r, pt)
        pt = _point_add(pt, pt)
        k >>= 1
    return r

def _kdf(z: bytes, klen: int) -> bytes:
    ct = 1
    out = b""
    while len(out) < klen:
        out += sm3(z + ct.to_bytes(4, "big"))
        ct += 1
    return out[:klen]

def _sm2_encrypt(msg: bytes) -> bytes:
    """C1C3C2，C1 不带 0x04 前缀。返回原始字节。"""
    g = (_GX, _GY)
    p = (_PX, _PY)
    while True:
        k = random.randrange(1, _N)
        c1 = _scalar_mul(k, g)
        s = _scalar_mul(k, p)
        x2 = s[0].to_bytes(32, "big")
        y2 = s[1].to_bytes(32, "big")
        t = _kdf(x2 + y2, len(msg))
        if any(t):
            break
    c2 = bytes(a ^ b for a, b in zip(msg, t))
    c3 = sm3(x2 + msg + y2)
    return c1[0].to_bytes(32, "big") + c1[1].to_bytes(32, "big") + c3 + c2

def dsfunique_for(device_id: str) -> str:
    """device_id(16hex 字符串) → dsfunique 224-hex。"""
    return _sm2_encrypt(device_id.encode("ascii")).hex()

# ================================================================
# 内嵌：nativeBuildProof（make_proof，已用 hook ground truth 验证）
# ================================================================
MAGIC = "DVP2NID2026"
PKG = "com.desafa.devpn"
SIGN = ("CA:43:9D:8D:87:EB:ED:AD:FC:71:E1:DF:70:6B:54:D0:"
        "8B:46:6C:13:A2:2A:9C:D3:1E:20:88:1A:96:07:2F:00")
APP_VER = "2.1.17"

def make_proof(android_id, ts_ms, urandom_nonce):
    """nativeBuildProof 完整算法。"""
    key = hashlib.sha256(f"{PKG}|{SIGN}|{urandom_nonce}|{MAGIC}".encode()).digest()
    xor = bytes(a ^ k for a, k in zip(android_id.encode(), key[:16]))
    device_cipher = xor.hex()
    proof = hashlib.sha256(
        f"{device_cipher}|{PKG}|{SIGN}|{ts_ms}|{urandom_nonce}|{MAGIC}".encode()
    ).hexdigest()
    return {
        "version": 1,
        "packageName": PKG,
        "timestamp": ts_ms,
        "nonce": urandom_nonce,
        "deviceCipher": device_cipher,
        "proof": proof,
    }

# ================================================================
# 内嵌：base58（Solana 公钥 / 签名编码）
# ================================================================
_B58_ALPH = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"

def b58encode(data: bytes) -> str:
    n = int.from_bytes(data, "big")
    out = bytearray()
    while n > 0:
        n, r = divmod(n, 58)
        out.append(_B58_ALPH[r])
    pad = 0
    for b in data:
        if b == 0:
            pad += 1
        else:
            break
    return (b"1" * pad + out[::-1]).decode("ascii")

# ================================================================
# 内嵌：Ed25519（纯 Python 兜底，适配 Juno / iOS）
# ================================================================
# RFC 8032 Ed25519 参数。优先使用 cryptography / PyNaCl；若都不可用，
# 自动使用下面的纯 Python 实现，因此 Juno 无需再安装原生扩展包。
_ED_P = 2**255 - 19
_ED_L = 2**252 + 27742317777372353535851937790883648493
_ED_D = (-121665 * pow(121666, _ED_P - 2, _ED_P)) % _ED_P
_ED_I = pow(2, (_ED_P - 1) // 4, _ED_P)

def _ed_inv(x):
    return pow(x, _ED_P - 2, _ED_P)

def _ed_xrecover(y):
    xx = (y * y - 1) * _ed_inv(_ED_D * y * y + 1) % _ED_P
    x = pow(xx, (_ED_P + 3) // 8, _ED_P)
    if (x * x - xx) % _ED_P != 0:
        x = (x * _ED_I) % _ED_P
    if x & 1:
        x = _ED_P - x
    return x

_ED_BY = (4 * _ed_inv(5)) % _ED_P
_ED_BX = _ed_xrecover(_ED_BY)
_ED_B = (_ED_BX, _ED_BY)

def _ed_add(P, Q):
    x1, y1 = P
    x2, y2 = Q
    x1x2 = (x1 * x2) % _ED_P
    y1y2 = (y1 * y2) % _ED_P
    dxxyy = (_ED_D * x1x2 * y1y2) % _ED_P
    x3 = ((x1 * y2 + x2 * y1) * _ed_inv(1 + dxxyy)) % _ED_P
    y3 = ((y1y2 + x1x2) * _ed_inv(1 - dxxyy)) % _ED_P
    return x3, y3

def _ed_scalarmult(P, e):
    Q = (0, 1)
    while e > 0:
        if e & 1:
            Q = _ed_add(Q, P)
        P = _ed_add(P, P)
        e >>= 1
    return Q

def _ed_encode_point(P):
    x, y = P
    bits = y | ((x & 1) << 255)
    return bits.to_bytes(32, "little")

def _ed_hint(m):
    return int.from_bytes(hashlib.sha512(m).digest(), "little")

def _ed_expand_seed(seed):
    h = hashlib.sha512(seed).digest()
    a_bytes = bytearray(h[:32])
    a_bytes[0] &= 248
    a_bytes[31] &= 63
    a_bytes[31] |= 64
    a = int.from_bytes(a_bytes, "little")
    prefix = h[32:]
    return a, prefix

def _ed_public_from_seed(seed):
    a, _ = _ed_expand_seed(seed)
    return _ed_encode_point(_ed_scalarmult(_ED_B, a))

def _ed_sign(seed, public_key, msg):
    a, prefix = _ed_expand_seed(seed)
    r = _ed_hint(prefix + msg) % _ED_L
    R = _ed_encode_point(_ed_scalarmult(_ED_B, r))
    k = _ed_hint(R + public_key + msg) % _ED_L
    S = (r + k * a) % _ED_L
    return R + S.to_bytes(32, "little")

def ed25519_keypair():
    """返回 (public_raw_32, sign_fn)，sign_fn(msg:bytes)->sig64。

    在普通 Python 上优先使用 cryptography / PyNaCl；在 Juno/iOS 等
    无法安装原生扩展的环境里，自动退回内嵌的纯 Python Ed25519。
    """
    seed = os.urandom(32)

    try:
        from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
        sk = Ed25519PrivateKey.from_private_bytes(seed)
        try:
            pub = sk.public_key().public_bytes_raw()
        except AttributeError:
            # 兼容较旧 cryptography
            from cryptography.hazmat.primitives import serialization
            pub = sk.public_key().public_bytes(
                encoding=serialization.Encoding.Raw,
                format=serialization.PublicFormat.Raw,
            )
        return pub, (lambda msg, _sk=sk: _sk.sign(msg))
    except Exception:
        pass

    try:
        from nacl.signing import SigningKey
        sk = SigningKey(seed)
        pub = bytes(sk.verify_key)
        return pub, (lambda msg, _sk=sk: _sk.sign(msg).signature)
    except Exception:
        pass

    # Juno / iOS 兜底：不需要 pip 安装任何第三方包
    pub = _ed_public_from_seed(seed)
    return pub, (lambda msg, _seed=seed, _pub=pub: _ed_sign(_seed, _pub, msg))

# ================================================================
# 配置
# ================================================================
DEFAULT_INVITE = "TVX2A2N0"
OWNER_ID = "f53dbff288fc5090"
WS_PATH = "/ws-vmess"
DEVICE_BRAND = "motorola"
DEVICE_MODEL = "XT2201-2"
DEVICE_NAME = "motorola edge X30"
DEVICE_OS = "14"
DOMAINS = [
    "https://mpn.desafa.net",
    "https://news.devpn.vip",
    "https://book.devpn.vip",
    "https://abs.devpn.vip",
    "https://sports.devpn.vip",
]

_HERE = os.path.dirname(os.path.abspath(__file__))
if sys.platform.startswith("linux") and os.path.exists("/storage/emulated/0"):
    SAVE_DIR = "/storage/emulated/0/Download/"          # Android (Termux)
elif sys.platform == "win32":
    SAVE_DIR = os.path.join(os.path.expanduser("~"), "Downloads")
else:
    SAVE_DIR = _HERE

# 节点服务器是自签/非标准证书，关闭校验（与 App vpnBypassPost 行为一致）
_SSL_CTX = ssl.create_default_context()
_SSL_CTX.check_hostname = False
_SSL_CTX.verify_mode = ssl.CERT_NONE

# ================================================================
# 设备证明头（一次生成，全程复用同一份 requestid）
# ================================================================
def make_headers(token, device_id, proof=None):
    device = {
        "brand": DEVICE_BRAND,
        "deviceId": device_id,
        "systemName": "Android",
        "isTablet": "false",
        "deviceName": DEVICE_NAME,
        "deviceModel": DEVICE_MODEL,
        "osVersion": DEVICE_OS,
        "appVersion": APP_VER,
        "platform": "android",
    }
    fingerprint = hashlib.sha256(
        json.dumps(device, separators=(",", ":")).encode()
    ).hexdigest()
    dsfunique = dsfunique_for(device_id)
    if proof is None:
        ts_ms = str(int(time.time() * 1000))
        urandom_nonce = os.urandom(16).hex()
        proof = make_proof(device_id, ts_ms, urandom_nonce)
    return {
        "dsf-token": token,
        "Language": "zh_HK",
        "x-version": APP_VER,
        "fingerprint": fingerprint,
        "manufacturer": DEVICE_BRAND,
        "platform": "android",
        "devicemodel": DEVICE_MODEL,
        "osversion": DEVICE_OS,
        "appversion": APP_VER,
        "devicename": DEVICE_NAME,
        "dsfunique": dsfunique,
        "requestid": json.dumps(proof, separators=(",", ":")),
    }

def make_login_device_info(android_id):
    """App getDeviceInfo() 字段（用于登录 fingerprint / nonce 查询）。"""
    return {
        "brand": DEVICE_BRAND,
        "deviceId": DEVICE_MODEL,
        "systemName": "Android",
        "isTablet": "false",
        "hasNotch": "false",
        "totalMemory": str(8 * 1024 ** 3),
        "totalDiskCapacity": str(128 * 1024 ** 3),
        "manufacturer": DEVICE_BRAND,
        "deviceType": "Handset",
        "androidId": android_id,
    }

def pick_base(hdrs=None):
    hdrs = hdrs or {"Language": "zh_HK"}
    for d in DOMAINS:
        st, body = http("GET", f"{d}/api/dsf/home/getByCode?code=devpn_download", hdrs)
        if body and '"code":0' in body:
            return d
    return None

def register_account(invite=DEFAULT_INVITE, android_id=None, claim_free=True):
    """生成 Solana 密钥 → 登录拿新 dsf-token → 绑邀请码 → 领免费时长。

    返回 dict: token / android_id / wallet / base / user / proof
    """
    android_id = android_id or "".join(random.choice("0123456789abcdef") for _ in range(16))
    device_info = make_login_device_info(android_id)
    fingerprint = hashlib.sha256(
        json.dumps(device_info, separators=(",", ":")).encode()
    ).hexdigest()
    proof = make_proof(android_id, str(int(time.time() * 1000)), os.urandom(16).hex())
    pub, sign = ed25519_keypair()
    wallet = b58encode(pub)

    base = pick_base()
    if not base:
        raise RuntimeError("无法连接任何 API 域名")

    qs = urllib.parse.urlencode({
        "walletAddress": wallet,
        "fingerprint": fingerprint,
        **device_info,
    })
    hdrs = {
        "Language": "zh_HK",
        "Content-Type": "application/json",
        "x-version": APP_VER,
        "platform": "android",
        "dsf-token": "",
        "fingerprint": fingerprint,
        "manufacturer": DEVICE_BRAND,
        "requestid": json.dumps(proof, separators=(",", ":")),
        "devicemodel": DEVICE_MODEL,
        "osversion": DEVICE_OS,
        "appversion": APP_VER,
        "devicename": DEVICE_NAME,
        "dsfunique": dsfunique_for(android_id),
    }
    st, body = http("GET", f"{base}/api/dsf/wallet/login/user/nonce?{qs}", hdrs)
    try:
        nonce = json.loads(body)["data"]
    except Exception:
        raise RuntimeError(f"获取 nonce 失败: {body}")

    message = str(uuid.uuid4())
    signature = b58encode(sign(message.encode("utf-8")))
    verify_body = {
        **proof,
        "fingerprint": fingerprint,
        "walletAddress": wallet,
        "signature": signature,
        "nonce": nonce,
        "message": message,
        "sourceType": "deapp_android",
        "userId": "",
        "uuid": "",
        "device": json.dumps(device_info, separators=(",", ":")),
        "deviceType": "android",
        "deviceName": DEVICE_NAME,
        "deviceModel": DEVICE_MODEL,
        "osVersion": DEVICE_OS,
        "appVersion": APP_VER,
    }
    st, body = http("POST", f"{base}/api/dsf/wallet/login/user/verify", hdrs, body=verify_body)
    try:
        resp = json.loads(body)
        data = resp["data"]
        token = data["dsf-token"]
    except Exception:
        raise RuntimeError(f"登录/注册失败: {body}")

    hdrs["dsf-token"] = token
    bind_ok = None
    free_ok = None
    if invite:
        st, body = http(
            "POST",
            f"{base}/api/dsf/wallet/app/bind-code?inviteCode={urllib.parse.quote(invite)}",
            hdrs,
            body={},
        )
        try:
            bind_ok = json.loads(body).get("code") == 0
        except Exception:
            bind_ok = False

    if claim_free:
        flat = {"fingerprint": fingerprint, **device_info, **{k: str(v) for k, v in proof.items()}}
        q2 = urllib.parse.urlencode(flat)
        st, body = http(
            "GET",
            f"{base}/api/dsf/app/home/user/get-free-flow?{q2}",
            hdrs,
        )
        try:
            free_ok = json.loads(body).get("data") is True
        except Exception:
            free_ok = False

    return {
        "token": token,
        "android_id": android_id,
        "wallet": wallet,
        "base": base,
        "user": (data or {}).get("user") or {},
        "proof": proof,
        "session_id": (data or {}).get("sessionId"),
        "expire_time": (data or {}).get("expireTime"),
        "bind_ok": bind_ok,
        "free_ok": free_ok,
        "raw": data,
    }

# ================================================================
# API
# ================================================================
def http(method, url, headers=None, body=None, timeout=20):
    req = urllib.request.Request(url, method=method, headers=headers or {})
    if body is not None:
        req.add_header("Content-Type", "application/json")
        if isinstance(body, (dict, list)):
            req.data = json.dumps(body).encode()
        else:
            req.data = body.encode()
    try:
        with urllib.request.urlopen(req, timeout=timeout, context=_SSL_CTX) as r:
            return r.status, r.read().decode("utf-8", errors="replace")
    except urllib.error.HTTPError as e:
        return e.code, e.read().decode("utf-8", errors="replace")
    except Exception as e:
        return -1, str(e)

def fetch_nodes(base, token, hdrs, code, residence=False):
    path = "/app/equipment/with-account-home-v1" if residence else "/app/devpn/unified-with-account"
    st, body = http("POST", f"{base}/api/dsf{path}?code={code}&uuid={OWNER_ID}", hdrs, body=[])
    try:
        return json.loads(body)
    except Exception:
        return {"code": -1, "msg": "bad response"}

def get_countries(base, token, hdrs, residence=False):
    if residence:
        st, body = http("GET", f"{base}/api/dsf/app/equipment/list-home?language=zh_HK", hdrs)
    else:
        st, body = http("GET",
                        f"{base}/api/dsf/app/devpn/country-list?ownerId={OWNER_ID}&language=zh_HK&variant=0",
                        hdrs)
    try:
        return json.loads(body).get("data") or []
    except Exception:
        return []

def activate_node(node):
    """POST sm2ciphertext 到节点服务器的 /server/setAccount。
    返回 True 表示激活成功（data:true）。"""
    domain = node.get("domainName")
    port = node.get("appPort") or "443"
    sm2 = node.get("sm2ciphertext") or ""
    url = f"https://{domain}:{port}/server/setAccount"
    st, body = http("POST", url, {"Content-Type": "application/json"}, body={"data": sm2})
    try:
        return json.loads(body).get("data") is True
    except Exception:
        return False

# ================================================================
# VMess 分享链接
# ================================================================
COUNTRY_NAME_MAP = {
    "HK": "🇭🇰香港",
    "JP": "🇯🇵日本",
    "SG": "🇸🇬新加坡",
    "US": "🇺🇸美国",
    "KR": "🇰🇷韩国",
    "DE": "🇩🇪德国",
    "TW": "🇹🇼台湾",
    "GB": "🇬🇧英国",
    "UK": "🇬🇧英国",
    "FR": "🇫🇷法国",
    "CA": "🇨🇦加拿大",
    "AU": "🇦🇺澳大利亚",
    "ID": "🇮🇩印度尼西亚",
}

def vmess_name(code, index, total):
    base = COUNTRY_NAME_MAP.get(str(code).upper(), str(code))
    return f"{base}{index:02d}" if total > 1 else base


UUID_RE = re.compile(r"^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$")
DOMAIN_RE = re.compile(r"^(?=.{1,253}$)(?:[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?\.)+[A-Za-z]{2,63}$")

def normalize_uuid(value):
    """兼容标准 UUID、32 位无横杠 UUID，以及少量带空白/大括号的返回值。"""
    s = str(value or "").strip().strip("{}")
    if not s:
        return None

    # 标准 8-4-4-4-12
    if UUID_RE.match(s):
        return s.lower()

    # 32 位十六进制，自动补横杠
    compact = s.replace("-", "")
    if re.fullmatch(r"[0-9a-fA-F]{32}", compact):
        return (
            compact[0:8] + "-" +
            compact[8:12] + "-" +
            compact[12:16] + "-" +
            compact[16:20] + "-" +
            compact[20:32]
        ).lower()

    # 最后再交给 Python 自带 uuid 模块尝试解析
    try:
        return str(uuid.UUID(s))
    except Exception:
        return None

def node_uuid(node):
    # API 不同版本可能字段名不同，依次兼容
    for key in ("uuid", "userUuid", "userUUID", "accountUuid", "accountUUID", "vmessUuid", "vmessUUID", "id"):
        val = node.get(key)
        norm = normalize_uuid(val)
        if norm:
            return norm
    return None

def valid_vmess_node(node):
    domain = str(node.get("domainName") or "").strip()
    vm_uuid = node_uuid(node)
    port_raw = node.get("appPort") or 443

    if not domain or not DOMAIN_RE.match(domain):
        return False, "domainName 无效"
    if not vm_uuid:
        raw = node.get("uuid")
        return False, f"UUID 无效({raw!r})"

    try:
        port = int(port_raw)
    except Exception:
        return False, "端口不是数字"

    if port < 1 or port > 65535:
        return False, "端口超出范围"

    return True, ""

def vmess_link(node, name):
    ok, reason = valid_vmess_node(node)
    if not ok:
        raise ValueError(reason)

    domain = str(node.get("domainName")).strip()
    port = str(int(node.get("appPort") or 443))
    vm_uuid = node_uuid(node)

    cfg = {
        "v": "2",
        "ps": name,
        "add": domain,
        "port": port,
        "id": vm_uuid,
        "aid": "0",
        "scy": "auto",
        "net": "ws",
        "type": "none",
        "host": domain,
        "path": WS_PATH,
        "tls": "tls",
        "sni": domain,
    }

    raw = json.dumps(cfg, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    link = "vmess://" + base64.b64encode(raw).decode("ascii")

    # 自检
    payload = link[len("vmess://"):]
    check = json.loads(base64.b64decode(payload).decode("utf-8"))
    required = ("v", "ps", "add", "port", "id", "aid", "scy", "net", "type", "host", "path", "tls", "sni")
    if any(k not in check for k in required):
        raise ValueError("VMess 自检缺少必要字段")
    if check["add"] != check["host"] or check["add"] != check["sni"]:
        raise ValueError("add/host/sni 不一致")
    if not normalize_uuid(check["id"]):
        raise ValueError("VMess UUID 自检失败")

    return link

# ================================================================
# 一键并发拉取入口
# ================================================================
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed

INVITE = DEFAULT_INVITE
HERE = os.path.dirname(os.path.abspath(__file__)) or "."
OUT_FILE = os.path.join(HERE, "nodes.txt")
META_FILE = os.path.join(HERE, "last_account.json")
ROUNDS_PER_COUNTRY = 10
MAX_NODES_PER_COUNTRY = 3  # 每个国家最终最多保留 3 个可用节点
COUNTRY_WORKERS = 7
ACTIVATE_WORKERS = 16

_print_lock = threading.Lock()
_activate_pool = None


def log(msg: str) -> None:
    with _print_lock:
        print(msg, flush=True)


def activate_batch(nodes):
    ok = []
    if not nodes:
        return ok
    pool = _activate_pool
    if pool is None:
        with ThreadPoolExecutor(max_workers=ACTIVATE_WORKERS) as tmp:
            futs = {tmp.submit(activate_node, n): n for n in nodes}
            for fut in as_completed(futs):
                n = futs[fut]
                try:
                    if fut.result():
                        ok.append(n)
                except Exception:
                    pass
        return ok
    futs = {pool.submit(activate_node, n): n for n in nodes}
    for fut in as_completed(futs):
        n = futs[fut]
        try:
            if fut.result():
                ok.append(n)
        except Exception:
            pass
    return ok


def harvest_country(base, token, hdrs, code, rounds=ROUNDS_PER_COUNTRY, max_nodes=MAX_NODES_PER_COUNTRY):
    bucket = {}
    log(f"开始 {code} …（最多保留 {max_nodes} 条）")
    rounds_used = 0

    for round_i in range(1, rounds + 1):
        # 已经凑够就立即停止，不再继续请求后面的轮次
        if len(bucket) >= max_nodes:
            break

        rounds_used = round_i
        before = len(bucket)
        data = fetch_nodes(base, token, hdrs, code, residence=False)

        fresh = []
        seen_this_round = set()
        for n in data.get("data") or []:
            dn = n.get("domainName")
            if dn and dn not in bucket and dn not in seen_this_round:
                seen_this_round.add(dn)
                fresh.append(n)

        # 激活本轮新节点，只收够 max_nodes 为止
        remaining = max_nodes - len(bucket)
        for n in activate_batch(fresh):
            dn = n.get("domainName")
            if dn and dn not in bucket:
                bucket[dn] = n
                if len(bucket) >= max_nodes:
                    break

        gained = len(bucket) - before
        log(f"  {code}: 第{round_i}/{rounds}轮  累计{len(bucket)}/{max_nodes}  (+{gained})")

        if len(bucket) >= max_nodes:
            log(f"  {code}: 已凑够 {max_nodes} 条，提前停止")
            break

    log(f"  → {code} 完成 {len(bucket)} 条（实际跑 {rounds_used}/{rounds} 轮）")
    return code, bucket


def main():
    global _activate_pool
    t0 = time.time()

    log("===== 1/3 注册新账号 =====")
    acc = register_account(invite=INVITE, claim_free=True)
    token = acc["token"]
    device_id = acc["android_id"]
    log(f"token:  {token}")
    log(f"wallet: {acc['wallet']}")
    log(
        f"invite: {'ok' if acc.get('bind_ok') else 'fail'}  "
        f"free: {'ok' if acc.get('free_ok') else 'fail'}"
    )

    hdrs = make_headers(token, device_id)
    base = acc.get("base")
    if not base:
        for d in DOMAINS:
            r = fetch_nodes(d, token, hdrs, "HK")
            if r.get("code") == 0 and r.get("data"):
                base = d
                break
    if not base:
        log("无法连接 API")
        sys.exit(1)
    log(f"API: {base}")

    log("\n===== 2/3 并发拉取全部国家节点 =====")
    countries = get_countries(base, token, hdrs, residence=False)
    if not countries:
        log("国家列表为空")
        sys.exit(1)

    codes = [c.get("egName") for c in countries if c.get("egName")]
    log(
        f"国家 {len(codes)} 个，每国最多 {ROUNDS_PER_COUNTRY} 轮，"
        f"每国最多保留 {MAX_NODES_PER_COUNTRY} 条，"
        f"地区并发 {COUNTRY_WORKERS}，激活并发 {ACTIVATE_WORKERS}"
    )
    for c in countries:
        log(f"  - {c.get('egName')}: {c.get('name')} ({c.get('total', 0)})")

    collected = {}
    _activate_pool = ThreadPoolExecutor(max_workers=ACTIVATE_WORKERS)
    try:
        with ThreadPoolExecutor(max_workers=min(COUNTRY_WORKERS, len(codes) or 1)) as pool:
            futs = [
                pool.submit(harvest_country, base, token, hdrs, code)
                for code in codes
            ]
            for fut in as_completed(futs):
                code, bucket = fut.result()
                collected[code] = bucket
    finally:
        _activate_pool.shutdown(wait=True)
        _activate_pool = None

    ordered = {code: collected[code] for code in codes if code in collected}

    log("\n===== 3/3 保存 =====")
    links = []
    skipped = []
    for code, nodes in ordered.items():
        valid_nodes = []
        for n in nodes.values():
            ok, reason = valid_vmess_node(n)
            if ok:
                valid_nodes.append(n)
            else:
                skipped.append((code, n.get("domainName"), reason))

        total = len(valid_nodes)
        for i, n in enumerate(valid_nodes, 1):
            name = vmess_name(code, i, total)
            try:
                links.append(vmess_link(n, name))
            except Exception as e:
                skipped.append((code, n.get("domainName"), f"生成失败: {e}"))

    if skipped:
        print(f"跳过异常节点: {len(skipped)}")
        for code, domain, reason in skipped:
            print(f"  [{code}] {domain or '-'} -> {reason}")

    with open(OUT_FILE, "w", encoding="utf-8") as f:
        f.write("\n".join(links) + "\n")

    elapsed = time.time() - t0
    meta = {
        "token": token,
        "android_id": device_id,
        "wallet": acc["wallet"],
        "invite": INVITE,
        "rounds_per_country": ROUNDS_PER_COUNTRY,
        "max_nodes_per_country": MAX_NODES_PER_COUNTRY,
        "country_workers": COUNTRY_WORKERS,
        "activate_workers": ACTIVATE_WORKERS,
        "per_country": {k: len(val) for k, val in ordered.items()},
        "total_links": len(links),
        "elapsed_sec": round(elapsed, 1),
        "nodes_file": OUT_FILE,
    }
    with open(META_FILE, "w", encoding="utf-8") as f:
        json.dump(meta, f, ensure_ascii=False, indent=2)

    log(f"合计 {len(links)} 条 → {OUT_FILE}")
    log(f"账号信息 → {META_FILE}")
    log(f"耗时 {elapsed:.1f}s")
    for k, n in meta["per_country"].items():
        log(f"  {k}: {n}")


if __name__ == "__main__":
    main()
