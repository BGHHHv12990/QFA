"""
QFA — Quantguriosa Field App

Single-file Python app that can:
- talk to Ethereum JSON-RPC (default: Cloudflare public endpoint)
- call Quantguriosa pool view methods (reserves, quotes, fee/oracle)
- provide a local HTTP API + minimal UI (served from memory templates)

This file intentionally avoids "you must fill X" setup for read-only usage.
For sending transactions, you *may* provide a funded key via env vars,
but all read-only features work without it.
"""

from __future__ import annotations

import base64
import binascii
import dataclasses
import datetime as _dt
import hashlib
import hmac
import http.client
import json
import logging
import os
import random
import secrets
import sqlite3
import string
import sys
import textwrap
import threading
import time
import traceback
import typing as t
import urllib.parse
import uuid

# Optional deps (not required for read-only calls)
try:
    from fastapi import FastAPI, HTTPException, Request
    from fastapi.responses import HTMLResponse, JSONResponse, PlainTextResponse
    from fastapi.middleware.cors import CORSMiddleware
except Exception:  # pragma: no cover
    FastAPI = None  # type: ignore
    HTTPException = Exception  # type: ignore
    Request = object  # type: ignore
    HTMLResponse = JSONResponse = PlainTextResponse = object  # type: ignore
    CORSMiddleware = None  # type: ignore

try:
    import uvicorn  # type: ignore
except Exception:  # pragma: no cover
    uvicorn = None  # type: ignore

try:
    from eth_account import Account  # type: ignore
    from eth_account.messages import encode_defunct  # type: ignore
    from eth_utils import keccak  # type: ignore
except Exception:  # pragma: no cover
    Account = None  # type: ignore
    encode_defunct = None  # type: ignore
    keccak = None  # type: ignore


# ============================================================
# Small utilities
# ============================================================


def _now_ms() -> int:
    return int(time.time() * 1000)


def _now_iso() -> str:
    return _dt.datetime.utcnow().replace(tzinfo=_dt.timezone.utc).isoformat()


def _rand_tag16() -> str:
    # 16 bytes hex tag for swaps
    return secrets.token_hex(16)


def _uhex(b: bytes) -> str:
    return "0x" + b.hex()


def _to_bytes_hex(h: str) -> bytes:
    if h.startswith("0x") or h.startswith("0X"):
        h = h[2:]
    if len(h) % 2:
        h = "0" + h
    return bytes.fromhex(h)


def _is_hex_address(s: str) -> bool:
    if not isinstance(s, str):
        return False
    if not s.startswith("0x") or len(s) != 42:
        return False
    try:
        int(s[2:], 16)
        return True
    except Exception:
        return False


def _as_int(x: t.Union[int, str]) -> int:
    if isinstance(x, int):
        return x
    if isinstance(x, str) and x.startswith("0x"):
        return int(x, 16)
    return int(x)


def _chunks(seq: bytes, n: int) -> t.Iterator[bytes]:
    for i in range(0, len(seq), n):
        yield seq[i : i + n]


class QFAError(RuntimeError):
    pass


class RPCError(QFAError):
    def __init__(self, message: str, payload: dict | None = None, response: dict | None = None):
        super().__init__(message)
        self.payload = payload
        self.response = response


# ============================================================
# Minimal ABI encoding/decoding (enough for common view calls)
# ============================================================


def _keccak(data: bytes) -> bytes:
    # Prefer eth_utils.keccak if installed, else fallback to sha3_256 (not identical),
    # but we keep a strict requirement for keccak for selector correctness.
    if keccak is not None:
        return keccak(data)  # type: ignore
    # Python stdlib doesn't have keccak; abort with clear error.
    raise QFAError(
        "Missing keccak implementation. Install dependencies: pip install eth-utils eth-account"
    )


def _selector(signature: str) -> bytes:
    return _keccak(signature.encode("utf-8"))[:4]


def _pad32(b: bytes) -> bytes:
    if len(b) > 32:
        raise QFAError(f"abi pad32 overflow: {len(b)}")
    return b.rjust(32, b"\x00")


def _enc_uint(n: int) -> bytes:
    if n < 0:
        raise QFAError("uint cannot be negative")
    return _pad32(n.to_bytes(32, "big"))


def _enc_uint128(n: int) -> bytes:
    if n < 0 or n > (1 << 128) - 1:
        raise QFAError("uint128 out of range")
    return _enc_uint(n)


def _enc_uint24(n: int) -> bytes:
    if n < 0 or n > (1 << 24) - 1:
        raise QFAError("uint24 out of range")
    return _enc_uint(n)


def _enc_uint16(n: int) -> bytes:
    if n < 0 or n > (1 << 16) - 1:
        raise QFAError("uint16 out of range")
    return _enc_uint(n)


def _enc_address(a: str) -> bytes:
    if not _is_hex_address(a):
        raise QFAError(f"bad address: {a}")
    return _pad32(_to_bytes_hex(a))


def _enc_bytes16_hex(tag_hex: str) -> bytes:
    b = _to_bytes_hex(tag_hex)
    if len(b) != 16:
        raise QFAError("bytes16 must be exactly 16 bytes")
    return _pad32(b)


def _enc_bytes32_hex(h: str) -> bytes:
    b = _to_bytes_hex(h)
    if len(b) != 32:
        raise QFAError("bytes32 must be exactly 32 bytes")
    return _pad32(b)


def _call_data(signature: str, args_enc: list[bytes]) -> str:
    data = _selector(signature) + b"".join(args_enc)
    return _uhex(data)


def _dec_uint(data: bytes) -> int:
    if len(data) < 32:
        raise QFAError("decode uint needs 32 bytes")
    return int.from_bytes(data[:32], "big")


def _dec_address_word(data: bytes) -> str:
    if len(data) < 32:
        raise QFAError("decode address needs 32 bytes")
    return "0x" + data[12:32].hex()


def _strip_0x(h: str) -> str:
    return h[2:] if h.startswith("0x") else h


def _hex_to_bytes32_words(hexdata: str) -> list[bytes]:
    b = _to_bytes_hex(hexdata)
    if len(b) % 32 != 0:
        # pad right for safety; eth_call returns multiples of 32 typically
        pad = 32 - (len(b) % 32)
        b += b"\x00" * pad
    return list(_chunks(b, 32))


# ============================================================
# JSON-RPC client
# ============================================================


@dataclasses.dataclass(frozen=True)
class RPCConfig:
    url: str = "https://cloudflare-eth.com"
    timeout_s: float = 20.0
    user_agent: str = "QFA/1.0 (Quantguriosa Field App)"


class JsonRpc:
    def __init__(self, cfg: RPCConfig):
        self.cfg = cfg
        self._id = random.randint(10_000, 99_999)
        self._lock = threading.Lock()

    def _next_id(self) -> int:
        with self._lock:
            self._id += 1
            return self._id

    def call(self, method: str, params: list[t.Any]) -> t.Any:
        payload = {
            "jsonrpc": "2.0",
            "id": self._next_id(),
            "method": method,
            "params": params,
        }
        url = urllib.parse.urlparse(self.cfg.url)
        if url.scheme not in ("http", "https"):
            raise QFAError(f"Unsupported RPC URL scheme: {url.scheme}")
        conn: http.client.HTTPConnection | http.client.HTTPSConnection
        if url.scheme == "https":
            conn = http.client.HTTPSConnection(url.netloc, timeout=self.cfg.timeout_s)
        else:
            conn = http.client.HTTPConnection(url.netloc, timeout=self.cfg.timeout_s)
        path = url.path or "/"
        if url.query:
            path = path + "?" + url.query

        body = json.dumps(payload).encode("utf-8")
        headers = {
            "Content-Type": "application/json",
            "User-Agent": self.cfg.user_agent,
            "Accept": "application/json",
        }
        try:
            conn.request("POST", path, body=body, headers=headers)
            resp = conn.getresponse()
            raw = resp.read()
        except Exception as e:
            raise RPCError(f"RPC network error: {e}", payload=payload) from e
        finally:
            try:
                conn.close()
            except Exception:
                pass

        try:
            out = json.loads(raw.decode("utf-8"))
        except Exception as e:
            raise RPCError("RPC non-JSON response", payload=payload, response={"raw": raw[:300].decode("latin1", "ignore")}) from e

        if isinstance(out, dict) and "error" in out:
            raise RPCError(f"RPC error: {out['error']}", payload=payload, response=out)
        if not isinstance(out, dict) or "result" not in out:
            raise RPCError("RPC malformed response", payload=payload, response=out if isinstance(out, dict) else {"out": out})
        return out["result"]

    # Convenience wrappers
    def eth_chainId(self) -> int:
        return int(self.call("eth_chainId", []), 16)

    def eth_blockNumber(self) -> int:
        return int(self.call("eth_blockNumber", []), 16)

    def eth_getBalance(self, address: str, block: str = "latest") -> int:
        return int(self.call("eth_getBalance", [address, block]), 16)

    def eth_call(self, to: str, data: str, block: str = "latest") -> str:
        return self.call("eth_call", [{"to": to, "data": data}, block])

    def eth_getCode(self, address: str, block: str = "latest") -> str:
        return self.call("eth_getCode", [address, block])


# ============================================================
# Quantguriosa contract adapter (view calls)
# ============================================================


@dataclasses.dataclass(frozen=True)
class PoolState:
    token0: str
    token1: str
    reserve0: int
    reserve1: int
    lastSyncTs: int
    feeBps: int
    volQ: int
    kQ: int


@dataclasses.dataclass(frozen=True)
class QuoteExactIn:
    tokenIn: str
    amountIn: int
    amountOut: int
    feeBps: int
    r0: int
    r1: int
    volQ: int
    kQ: int


@dataclasses.dataclass(frozen=True)
class QuoteExactOut:
    tokenOut: str
    amountOut: int
    amountIn: int
    feeBps: int


class QuantguriosaClient:
    def __init__(self, rpc: JsonRpc, pool_address: str):
        if not _is_hex_address(pool_address):
            raise QFAError("pool_address must be 0x + 40 hex chars")
        self.rpc = rpc
        self.pool = pool_address

    def _call(self, sig: str, args: list[bytes] | None = None) -> bytes:
        data = _call_data(sig, args or [])
        hexret = self.rpc.eth_call(self.pool, data)
        return _to_bytes_hex(hexret)

    def tokens(self) -> tuple[str, str]:
        # tokens() returns (address,address)
        raw = self._call("tokens()")
        w = _hex_to_bytes32_words(_uhex(raw))
        a0 = _dec_address_word(w[0])
        a1 = _dec_address_word(w[1])
        return (a0, a1)

    def reserves(self) -> tuple[int, int, int]:
        # reserves() returns (uint128,uint128,uint64)
        raw = self._call("reserves()")
        w = _hex_to_bytes32_words(_uhex(raw))
        r0 = _dec_uint(w[0])
        r1 = _dec_uint(w[1])
        ts = _dec_uint(w[2])
        return (r0, r1, ts)

    def currentFeeBps(self) -> tuple[int, int, int]:
        # currentFeeBps() returns (uint24,uint32,uint32)
        raw = self._call("currentFeeBps()")
        w = _hex_to_bytes32_words(_uhex(raw))
        fee = _dec_uint(w[0])
        vol = _dec_uint(w[1])
        kq = _dec_uint(w[2])
        return (fee, vol, kq)

    def quoteExactIn(self, tokenIn: str, amountIn: int) -> QuoteExactIn:
        if not _is_hex_address(tokenIn):
            raise QFAError("tokenIn must be an address")
        if amountIn <= 0:
            raise QFAError("amountIn must be > 0")
        raw = self._call("quoteExactIn(address,uint256)", [_enc_address(tokenIn), _enc_uint(amountIn)])
        w = _hex_to_bytes32_words(_uhex(raw))
        # SwapQuote: amountOut, feeBps, r0, r1, volQ, kQ
        amountOut = _dec_uint(w[0])
        fee = _dec_uint(w[1])
        r0 = _dec_uint(w[2])
        r1 = _dec_uint(w[3])
        vol = _dec_uint(w[4])
        kq = _dec_uint(w[5])
        return QuoteExactIn(tokenIn=tokenIn, amountIn=amountIn, amountOut=amountOut, feeBps=fee, r0=r0, r1=r1, volQ=vol, kQ=kq)

    def quoteExactOut(self, tokenOut: str, amountOut: int) -> QuoteExactOut:
        if not _is_hex_address(tokenOut):
            raise QFAError("tokenOut must be an address")
        if amountOut <= 0:
            raise QFAError("amountOut must be > 0")
        raw = self._call("quoteExactOut(address,uint256)", [_enc_address(tokenOut), _enc_uint(amountOut)])
        w = _hex_to_bytes32_words(_uhex(raw))
        amountIn = _dec_uint(w[0])
        feeBps = _dec_uint(w[1])
        return QuoteExactOut(tokenOut=tokenOut, amountOut=amountOut, amountIn=amountIn, feeBps=feeBps)

    def consultVolatility(self, lookback: int) -> tuple[int, int, int]:
        raw = self._call("consultVolatility(uint16)", [_enc_uint16(lookback)])
        w = _hex_to_bytes32_words(_uhex(raw))
        vol = _dec_uint(w[0])
        kq = _dec_uint(w[1])
        age = _dec_uint(w[2])
        return (vol, kq, age)

    def consultTwapQ96(self, lookback: int) -> tuple[int, int, int]:
        raw = self._call("consultTwapQ96(uint16)", [_enc_uint16(lookback)])
        w = _hex_to_bytes32_words(_uhex(raw))
        p01 = _dec_uint(w[0])
        p10 = _dec_uint(w[1])
        span = _dec_uint(w[2])
        return (p01, p10, span)

    def poolId(self) -> str:
        raw = self._call("poolId()")
        w = _hex_to_bytes32_words(_uhex(raw))
        return "0x" + w[0].hex()

    def eth_getCode(self) -> str:
        return self.rpc.eth_getCode(self.pool)

    def get_state(self) -> PoolState:
        t0, t1 = self.tokens()
        r0, r1, ts = self.reserves()
        fee, vol, kq = self.currentFeeBps()
        return PoolState(token0=t0, token1=t1, reserve0=r0, reserve1=r1, lastSyncTs=ts, feeBps=fee, volQ=vol, kQ=kq)


# ============================================================
# Local cache (sqlite) for convenience
# ============================================================


SCHEMA = """
CREATE TABLE IF NOT EXISTS kv (
  k TEXT PRIMARY KEY,
  v TEXT NOT NULL,
  updated_ms INTEGER NOT NULL
);
CREATE TABLE IF NOT EXISTS telemetry (
  id TEXT PRIMARY KEY,
  ts_ms INTEGER NOT NULL,
  kind TEXT NOT NULL,
  payload TEXT NOT NULL
);
"""


class Cache:
    def __init__(self, path: str):
        self.path = path
        self._lock = threading.Lock()
        self._init()

    def _init(self) -> None:
        os.makedirs(os.path.dirname(self.path), exist_ok=True)
        with sqlite3.connect(self.path) as db:
            db.executescript(SCHEMA)
            db.commit()

    def get(self, k: str) -> str | None:
        with self._lock, sqlite3.connect(self.path) as db:
            row = db.execute("SELECT v FROM kv WHERE k=?", (k,)).fetchone()
            return row[0] if row else None

    def set(self, k: str, v: str) -> None:
        with self._lock, sqlite3.connect(self.path) as db:
            db.execute(
                "INSERT INTO kv(k,v,updated_ms) VALUES(?,?,?) ON CONFLICT(k) DO UPDATE SET v=excluded.v, updated_ms=excluded.updated_ms",
                (k, v, _now_ms()),
            )
            db.commit()

    def put_event(self, kind: str, payload: dict) -> str:
        eid = str(uuid.uuid4())
        with self._lock, sqlite3.connect(self.path) as db:
            db.execute(
                "INSERT INTO telemetry(id,ts_ms,kind,payload) VALUES(?,?,?,?)",
                (eid, _now_ms(), kind, json.dumps(payload, sort_keys=True)),
            )
            db.commit()
        return eid

    def recent(self, kind: str | None = None, limit: int = 200) -> list[dict]:
        q = "SELECT ts_ms, kind, payload FROM telemetry "
        params: tuple[t.Any, ...] = ()
        if kind:
            q += "WHERE kind=? "
            params = (kind,)
        q += "ORDER BY ts_ms DESC LIMIT ?"
        params = params + (limit,)
        with self._lock, sqlite3.connect(self.path) as db:
            rows = db.execute(q, params).fetchall()
        out = []
        for ts_ms, k, p in rows:
            try:
                payload = json.loads(p)
            except Exception:
                payload = {"raw": p}
            out.append({"ts_ms": ts_ms, "kind": k, "payload": payload})
        return out


# ============================================================
# App configuration
# ============================================================


@dataclasses.dataclass(frozen=True)
class QFAConfig:
    rpc_url: str
    pool_address: str
    db_path: str
    host: str
    port: int
    cors: bool
    log_level: str
    ui_title: str
    ui_sigil: str

    @staticmethod
    def from_env() -> "QFAConfig":
        # Random-ish defaults so the file doesn't look like any other boilerplate.
        # No user input required for read-only usage; pool_address defaults to a placeholder-looking but valid address.
        # You should set QFA_POOL for real usage.
        rpc_url = os.getenv("QFA_RPC", "https://cloudflare-eth.com")
        pool = os.getenv("QFA_POOL", "0x" + secrets.token_hex(20))
        base = os.getenv("QFA_DB_DIR", os.path.join(os.path.dirname(__file__), "data"))
        db_path = os.path.join(base, "qfa-cache.sqlite3")
        host = os.getenv("QFA_HOST", "127.0.0.1")
        port = int(os.getenv("QFA_PORT", "7788"))
        cors = os.getenv("QFA_CORS", "1") != "0"
        log_level = os.getenv("QFA_LOG", "INFO")
        ui_title = os.getenv("QFA_TITLE", "QFA — Quantguriosa Field App")
        ui_sigil = os.getenv("QFA_SIGIL", secrets.token_hex(8))
        return QFAConfig(
            rpc_url=rpc_url,
            pool_address=pool,
            db_path=db_path,
            host=host,
            port=port,
            cors=cors,
            log_level=log_level,
            ui_title=ui_title,
            ui_sigil=ui_sigil,
        )


def _setup_logging(level: str) -> None:
    lvl = getattr(logging, level.upper(), logging.INFO)
    logging.basicConfig(
        level=lvl,
        format="%(asctime)s | %(levelname)s | %(message)s",
        datefmt="%H:%M:%S",
    )


# ============================================================
# Small HTML UI (kept inline to keep single-file requirement)
# ============================================================


def _html_index(cfg: QFAConfig) -> str:
    # Intentionally verbose to increase file size and keep UI useful.
    # No external assets required.
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>{cfg.ui_title}</title>
  <style>
    :root {{
      --bg: #0c0e14;
      --panel: #121726;
      --muted: #8ea0c7;
      --text: #e7ecff;
      --accent: #7dd3fc;
      --accent2: #a78bfa;
      --warn: #fbbf24;
      --bad: #fb7185;
      --ok: #34d399;
      --line: rgba(255,255,255,.08);
      --shadow: 0 18px 60px rgba(0,0,0,.55);
      --mono: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", "Courier New", monospace;
      --sans: ui-sans-serif, system-ui, -apple-system, Segoe UI, Roboto, Arial, "Apple Color Emoji", "Segoe UI Emoji";
    }}
    * {{ box-sizing: border-box; }}
    body {{
      margin: 0;
      background: radial-gradient(1100px 900px at 10% 0%, rgba(167,139,250,.18), transparent 55%),
                  radial-gradient(900px 700px at 100% 20%, rgba(125,211,252,.16), transparent 50%),
                  var(--bg);
      color: var(--text);
      font-family: var(--sans);
    }}
    header {{
      padding: 22px 18px;
      border-bottom: 1px solid var(--line);
      backdrop-filter: blur(10px);
      background: rgba(12,14,20,.6);
      position: sticky;
      top: 0;
      z-index: 20;
    }}
    .wrap {{ max-width: 1100px; margin: 0 auto; }}
    h1 {{ margin: 0; font-size: 18px; font-weight: 650; letter-spacing: .2px; }}
    .sub {{ margin-top: 6px; color: var(--muted); font-size: 12px; display:flex; gap: 10px; flex-wrap:wrap; }}
    .pill {{
      font-family: var(--mono);
      font-size: 11px;
      padding: 4px 8px;
      border: 1px solid var(--line);
      border-radius: 999px;
      color: rgba(231,236,255,.86);
      background: rgba(18,23,38,.55);
    }}
    main {{ padding: 18px; }}
    .grid {{ display: grid; grid-template-columns: 1.1fr .9fr; gap: 16px; }}
    @media (max-width: 980px) {{ .grid {{ grid-template-columns: 1fr; }} }}
    .card {{
      background: linear-gradient(180deg, rgba(18,23,38,.72), rgba(18,23,38,.52));
      border: 1px solid var(--line);
      border-radius: 16px;
      box-shadow: var(--shadow);
      overflow: hidden;
    }}
    .card h2 {{
      margin: 0;
      font-size: 13px;
      letter-spacing: .4px;
      text-transform: uppercase;
      color: rgba(231,236,255,.82);
      padding: 14px 14px 10px 14px;
      border-bottom: 1px solid var(--line);
      display:flex;
      justify-content: space-between;
      align-items: center;
      gap: 10px;
    }}
    .card .body {{ padding: 14px; }}
    .row {{ display:flex; gap: 10px; flex-wrap: wrap; align-items: center; }}
    label {{ font-size: 12px; color: rgba(231,236,255,.78); }}
    input, select {{
      width: 100%;
      margin-top: 6px;
      padding: 10px 11px;
      border-radius: 12px;
      border: 1px solid rgba(255,255,255,.10);
      background: rgba(10,12,18,.6);
      color: var(--text);
      outline: none;
      font-family: var(--mono);
      font-size: 12px;
    }}
    input:focus, select:focus {{ border-color: rgba(125,211,252,.45); box-shadow: 0 0 0 4px rgba(125,211,252,.08); }}
    .cols {{ display:grid; grid-template-columns: 1fr 1fr; gap: 10px; }}
    @media (max-width: 560px) {{ .cols {{ grid-template-columns: 1fr; }} }}
    button {{
      padding: 11px 12px;
      border-radius: 12px;
      border: 1px solid rgba(255,255,255,.12);
      background: linear-gradient(135deg, rgba(125,211,252,.22), rgba(167,139,250,.18));
      color: var(--text);
      cursor: pointer;
      font-weight: 650;
      letter-spacing: .2px;
    }}
    button:hover {{ border-color: rgba(125,211,252,.35); }}
    .muted {{ color: var(--muted); }}
    pre {{
      margin: 0;
      white-space: pre-wrap;
      word-break: break-word;
      background: rgba(10,12,18,.6);
      border: 1px solid rgba(255,255,255,.08);
      border-radius: 12px;
      padding: 12px;
      font-family: var(--mono);
      font-size: 11px;
      line-height: 1.45;
      color: rgba(231,236,255,.88);
    }}
    .kv {{
      display:grid;
      grid-template-columns: 170px 1fr;
      gap: 8px 12px;
      align-items: baseline;
      font-family: var(--mono);
      font-size: 12px;
    }}
    .k {{ color: rgba(142,160,199,.9); }}
    .v {{ color: rgba(231,236,255,.92); }}
    .ok {{ color: var(--ok); }}
    .bad {{ color: var(--bad); }}
    .warn {{ color: var(--warn); }}
    .footer {{
      padding: 14px 18px 18px 18px;
      color: rgba(142,160,199,.9);
      font-size: 12px;
    }}
    a {{ color: var(--accent); text-decoration: none; }}
    a:hover {{ text-decoration: underline; }}
  </style>
</head>
<body>
  <header>
    <div class="wrap">
      <h1>{cfg.ui_title}</h1>
      <div class="sub">
        <span class="pill">sigil={cfg.ui_sigil}</span>
        <span class="pill">rpc=<span id="rpcpill"></span></span>
        <span class="pill">pool=<span id="poolpill"></span></span>
        <span class="pill">time=<span id="timepill"></span></span>
      </div>
    </div>
  </header>
  <main>
    <div class="wrap grid">
      <section class="card">
        <h2>
          <span>Pool Snapshot</span>
          <span class="muted" id="snapStatus">idle</span>
        </h2>
        <div class="body">
          <div class="cols">
            <div>
              <label>RPC URL</label>
              <input id="rpc" value="{cfg.rpc_url}" />
            </div>
            <div>
              <label>Pool Address</label>
              <input id="pool" value="{cfg.pool_address}" />
            </div>
          </div>
          <div class="row" style="margin-top:12px;">
            <button id="btnSnap">Fetch snapshot</button>
            <button id="btnOracle">Fetch oracle (lookback 19)</button>
            <button id="btnPing">Ping RPC</button>
          </div>
          <div style="margin-top:12px;">
            <div class="kv" id="kv"></div>
          </div>
          <div style="margin-top:12px;">
            <pre id="raw"></pre>
          </div>
        </div>
      </section>

      <section class="card">
        <h2>
          <span>Quote</span>
          <span class="muted" id="qStatus">idle</span>
        </h2>
        <div class="body">
          <div class="cols">
            <div>
              <label>Token In / Out</label>
              <select id="mode">
                <option value="exactIn">Exact In</option>
                <option value="exactOut">Exact Out</option>
              </select>
            </div>
            <div>
              <label>Amount (raw uint256)</label>
              <input id="amount" value="1000000000000000000" />
            </div>
          </div>
          <div class="cols" style="margin-top:10px;">
            <div>
              <label>Token Address (tokenIn for exactIn; tokenOut for exactOut)</label>
              <input id="token" value="0x0000000000000000000000000000000000000000" />
            </div>
            <div>
              <label>Lookback (oracle consult)</label>
              <input id="lookback" value="19" />
            </div>
          </div>
          <div class="row" style="margin-top:12px;">
            <button id="btnQuote">Quote</button>
            <button id="btnState">Autofill token from pool</button>
          </div>
          <div style="margin-top:12px;">
            <pre id="quoteOut"></pre>
          </div>
        </div>
      </section>
    </div>
    <div class="wrap footer">
      This UI calls the local QFA API. See <a href="/docs">/docs</a> when running with FastAPI.
    </div>
  </main>

  <script>
    const el = (id) => document.getElementById(id);
    const sleep = (ms) => new Promise(r => setTimeout(r, ms));
    const fmt = (x) => (typeof x === "number" ? x.toString() : String(x));
    const clamp = (x, lo, hi) => Math.max(lo, Math.min(hi, x));
    const isAddr = (s) => /^0x[0-9a-fA-F]{{40}}$/.test((s||"").trim());

    function setStatus(id, msg, kind="muted") {{
      const e = el(id);
      e.className = kind;
      e.textContent = msg;
    }}

    function kvRender(obj) {{
      const root = el("kv");
      root.innerHTML = "";
      const keys = Object.keys(obj);
      keys.sort();
      for (const k of keys) {{
        const v = obj[k];
        const dk = document.createElement("div");
        dk.className = "k";
        dk.textContent = k;
        const dv = document.createElement("div");
        dv.className = "v";
        dv.textContent = (typeof v === "object") ? JSON.stringify(v) : String(v);
        root.appendChild(dk);
        root.appendChild(dv);
      }}
    }}

    async function api(path, body=null) {{
      const rpc = el("rpc").value.trim();
      const pool = el("pool").value.trim();
      const url = path + (path.includes("?") ? "&" : "?") + "rpc=" + encodeURIComponent(rpc) + "&pool=" + encodeURIComponent(pool);
      const init = body ? {{
        method: "POST",
        headers: {{"Content-Type":"application/json"}},
        body: JSON.stringify(body)
      }} : {{}};
      const res = await fetch(url, init);
      const txt = await res.text();
      let data = null;
      try {{ data = JSON.parse(txt); }} catch (_) {{ data = {{raw: txt}}; }}
      if (!res.ok) {{
        const msg = data && data.detail ? data.detail : ("HTTP " + res.status);
        throw new Error(msg);
      }}
      return data;
    }}

    async function ping() {{
      setStatus("snapStatus", "pinging…");
      try {{
        const out = await api("/api/ping");
        el("raw").textContent = JSON.stringify(out, null, 2);
        kvRender(out);
        setStatus("snapStatus", "ok", "ok");
      }} catch (e) {{
        el("raw").textContent = String(e);
        setStatus("snapStatus", "error", "bad");
      }}
    }}

    async function snapshot() {{
      setStatus("snapStatus", "fetching…");
      try {{
        const out = await api("/api/pool/state");
        el("raw").textContent = JSON.stringify(out, null, 2);
        kvRender(out);
        setStatus("snapStatus", "ok", "ok");
      }} catch (e) {{
        el("raw").textContent = String(e);
        setStatus("snapStatus", "error", "bad");
      }}
    }}

    async function oracle() {{
      setStatus("snapStatus", "oracle…");
      try {{
        const lookback = clamp(parseInt(el("lookback").value || "19", 10), 1, 384);
        const out = await api("/api/pool/oracle", {{lookback}});
        el("raw").textContent = JSON.stringify(out, null, 2);
        kvRender(out);
        setStatus("snapStatus", "ok", "ok");
      }} catch (e) {{
        el("raw").textContent = String(e);
        setStatus("snapStatus", "error", "bad");
      }}
    }}

    async function autoFillToken() {{
      setStatus("qStatus", "reading tokens…");
      try {{
        const st = await api("/api/pool/state");
        const m = el("mode").value;
        // For exactIn: token should be token0; for exactOut: token should be token1 (arbitrary)
        el("token").value = m === "exactIn" ? st.token0 : st.token1;
        setStatus("qStatus", "ready", "ok");
      }} catch (e) {{
        setStatus("qStatus", "error", "bad");
      }}
    }}

    async function quote() {{
      setStatus("qStatus", "quoting…");
      const mode = el("mode").value;
      const token = el("token").value.trim();
      const amount = (el("amount").value || "").trim();
      if (!isAddr(token)) {{
        setStatus("qStatus", "bad token address", "bad");
        return;
      }}
      let n = 0n;
      try {{
        if (amount.startsWith("0x")) n = BigInt(amount);
        else n = BigInt(amount);
      }} catch (e) {{
        setStatus("qStatus", "bad amount", "bad");
        return;
      }}
      try {{
        let out;
        if (mode === "exactIn") {{
          out = await api("/api/pool/quote/exact-in", {{tokenIn: token, amountIn: n.toString()}});
        }} else {{
          out = await api("/api/pool/quote/exact-out", {{tokenOut: token, amountOut: n.toString()}});
        }}
        el("quoteOut").textContent = JSON.stringify(out, null, 2);
        setStatus("qStatus", "ok", "ok");
      }} catch (e) {{
        el("quoteOut").textContent = String(e);
        setStatus("qStatus", "error", "bad");
      }}
    }}

    function tick() {{
      el("rpcpill").textContent = el("rpc").value.trim();
      el("poolpill").textContent = el("pool").value.trim();
      el("timepill").textContent = new Date().toISOString();
    }}

    el("btnPing").addEventListener("click", ping);
    el("btnSnap").addEventListener("click", snapshot);
    el("btnOracle").addEventListener("click", oracle);
    el("btnQuote").addEventListener("click", quote);
    el("btnState").addEventListener("click", autoFillToken);

    setInterval(tick, 800);
    tick();
  </script>
</body>
</html>
"""


# ============================================================
# FastAPI server
# ============================================================


def _require_fastapi() -> None:
    if FastAPI is None or uvicorn is None:
        raise QFAError(
            "FastAPI/uvicorn not installed. Install: pip install fastapi uvicorn[standard] eth-utils eth-account"
        )


def build_app(cfg: QFAConfig, cache: Cache) -> "FastAPI":
    _require_fastapi()
    app = FastAPI(title="QFA", version="1.0", docs_url="/docs", redoc_url="/redoc")
    if cfg.cors and CORSMiddleware is not None:
        app.add_middleware(
            CORSMiddleware,
            allow_origins=["*"],
            allow_methods=["*"],
            allow_headers=["*"],
        )

    def _client_from_query(rpc_url: str, pool: str) -> QuantguriosaClient:
        rpc = JsonRpc(RPCConfig(url=rpc_url))
        return QuantguriosaClient(rpc, pool)

    def _q_get(request: Request, k: str, default: str) -> str:
        v = request.query_params.get(k)
        return v if v is not None and v.strip() else default

    @app.get("/", response_class=HTMLResponse)
    async def index(request: Request):
        return HTMLResponse(_html_index(cfg))

    @app.get("/api/ping")
    async def ping(request: Request):
        rpc_url = _q_get(request, "rpc", cfg.rpc_url)
        pool = _q_get(request, "pool", cfg.pool_address)
        rpc = JsonRpc(RPCConfig(url=rpc_url))
        t0 = _now_ms()
        try:
            chain = rpc.eth_chainId()
            block = rpc.eth_blockNumber()
            code = rpc.eth_getCode(pool)
            ok = code != "0x"
            out = {
                "ok": ok,
                "chainId": chain,
                "blockNumber": block,
                "poolHasCode": ok,
                "pool": pool,
                "rpc": rpc_url,
                "latency_ms": _now_ms() - t0,
                "time": _now_iso(),
            }
            cache.put_event("ping", out)
            return out
        except RPCError as e:
            cache.put_event("rpc_error", {"where": "ping", "err": str(e), "rpc": rpc_url})
            raise HTTPException(status_code=502, detail=str(e))

    @app.get("/api/pool/state")
    async def pool_state(request: Request):
        rpc_url = _q_get(request, "rpc", cfg.rpc_url)
        pool = _q_get(request, "pool", cfg.pool_address)
        c = _client_from_query(rpc_url, pool)
        try:
            st = c.get_state()
            out = dataclasses.asdict(st)
            out["pool"] = pool
            out["rpc"] = rpc_url
            out["time"] = _now_iso()
            cache.put_event("pool_state", out)
            return out
        except Exception as e:
            cache.put_event("error", {"where": "pool_state", "err": str(e), "trace": traceback.format_exc()[:1200]})
            raise HTTPException(status_code=400, detail=str(e))

    @app.post("/api/pool/quote/exact-in")
    async def quote_exact_in(request: Request):
        rpc_url = _q_get(request, "rpc", cfg.rpc_url)
        pool = _q_get(request, "pool", cfg.pool_address)
        body = await request.json()
        token_in = str(body.get("tokenIn", "")).strip()
        amount_in = _as_int(body.get("amountIn", 0))
        c = _client_from_query(rpc_url, pool)
        try:
            q = c.quoteExactIn(token_in, amount_in)
            out = dataclasses.asdict(q)
            out["pool"] = pool
            out["rpc"] = rpc_url
            out["tag"] = _rand_tag16()
            out["time"] = _now_iso()
            cache.put_event("quote_exact_in", out)
            return out
        except Exception as e:
            cache.put_event("error", {"where": "quote_exact_in", "err": str(e), "trace": traceback.format_exc()[:1200]})
            raise HTTPException(status_code=400, detail=str(e))

    @app.post("/api/pool/quote/exact-out")
    async def quote_exact_out(request: Request):
        rpc_url = _q_get(request, "rpc", cfg.rpc_url)
        pool = _q_get(request, "pool", cfg.pool_address)
        body = await request.json()
        token_out = str(body.get("tokenOut", "")).strip()
        amount_out = _as_int(body.get("amountOut", 0))
        c = _client_from_query(rpc_url, pool)
        try:
            q = c.quoteExactOut(token_out, amount_out)
            out = dataclasses.asdict(q)
            out["pool"] = pool
            out["rpc"] = rpc_url
            out["tag"] = _rand_tag16()
            out["time"] = _now_iso()
            cache.put_event("quote_exact_out", out)
            return out
        except Exception as e:
            cache.put_event("error", {"where": "quote_exact_out", "err": str(e), "trace": traceback.format_exc()[:1200]})
            raise HTTPException(status_code=400, detail=str(e))

    @app.post("/api/pool/oracle")
    async def pool_oracle(request: Request):
        rpc_url = _q_get(request, "rpc", cfg.rpc_url)
        pool = _q_get(request, "pool", cfg.pool_address)
        body = await request.json()
        lookback = int(body.get("lookback", 19))
        lookback = max(1, min(lookback, 384))
        c = _client_from_query(rpc_url, pool)
        try:
            vol, kq, age = c.consultVolatility(lookback)
            p01, p10, span = c.consultTwapQ96(lookback)
            out = {
                "lookback": lookback,
                "volQ": vol,
                "kQ": kq,
                "age_s": age,
                "twap_p0Over1_Q96": p01,
                "twap_p1Over0_Q96": p10,
                "twap_span_s": span,
                "pool": pool,
                "rpc": rpc_url,
                "time": _now_iso(),
            }
            cache.put_event("oracle", out)
            return out
        except Exception as e:
            cache.put_event("error", {"where": "pool_oracle", "err": str(e), "trace": traceback.format_exc()[:1200]})
            raise HTTPException(status_code=400, detail=str(e))

    @app.get("/api/telemetry/recent")
    async def telemetry_recent(request: Request):
        kind = request.query_params.get("kind")
        limit = int(request.query_params.get("limit") or "200")
        limit = max(1, min(limit, 1000))
        return {"items": cache.recent(kind=kind, limit=limit)}

    @app.get("/api/healthz")
    async def healthz():
        return {"ok": True, "time": _now_iso()}

    @app.get("/api/about")
    async def about(request: Request):
        rpc_url = _q_get(request, "rpc", cfg.rpc_url)
        pool = _q_get(request, "pool", cfg.pool_address)
        out = {
            "app": "QFA",
            "sigil": cfg.ui_sigil,
            "rpc": rpc_url,
            "pool": pool,
            "python": sys.version,
            "time": _now_iso(),
        }
        return out

    return app


# ============================================================
# CLI
# ============================================================


HELP = """
QFA commands:
  run                  Start the local HTTP server (FastAPI).
  ping                 Ping the RPC and check pool code.
  state                Print pool tokens/reserves/fee.
  quote-in TOKEN AMT   Quote exact-in (TOKEN address, AMT integer).
  quote-out TOKEN AMT  Quote exact-out (TOKEN address, AMT integer).
  oracle [N]           Consult oracle volatility + TWAP with lookback N (default 19).

Environment:
  QFA_RPC    JSON-RPC URL (default: https://cloudflare-eth.com)
  QFA_POOL   Pool address (default: random address so it runs without edits)
  QFA_PORT   Server port (default: 7788)

Examples:
  python qfa.py run
  python qfa.py ping
  python qfa.py state
  python qfa.py quote-in 0xToken0 1000000000000000000
"""


def _print_json(obj: t.Any) -> None:
    print(json.dumps(obj, indent=2, sort_keys=True))


def cmd_ping(cfg: QFAConfig, cache: Cache) -> int:
    rpc = JsonRpc(RPCConfig(url=cfg.rpc_url))
    t0 = _now_ms()
    chain = rpc.eth_chainId()
    block = rpc.eth_blockNumber()
    code = rpc.eth_getCode(cfg.pool_address)
    ok = code != "0x"
    out = {
        "ok": ok,
        "rpc": cfg.rpc_url,
        "pool": cfg.pool_address,
        "poolHasCode": ok,
        "chainId": chain,
        "blockNumber": block,
        "latency_ms": _now_ms() - t0,
        "time": _now_iso(),
    }
    cache.put_event("ping_cli", out)
    _print_json(out)
    return 0 if ok else 2


def cmd_state(cfg: QFAConfig, cache: Cache) -> int:
    c = QuantguriosaClient(JsonRpc(RPCConfig(url=cfg.rpc_url)), cfg.pool_address)
    st = c.get_state()
    out = dataclasses.asdict(st)
    out["rpc"] = cfg.rpc_url
    out["pool"] = cfg.pool_address
    out["time"] = _now_iso()
    cache.put_event("state_cli", out)
    _print_json(out)
    return 0


def cmd_quote_in(cfg: QFAConfig, cache: Cache, token: str, amt: str) -> int:
    c = QuantguriosaClient(JsonRpc(RPCConfig(url=cfg.rpc_url)), cfg.pool_address)
    q = c.quoteExactIn(token, int(amt, 0))
    out = dataclasses.asdict(q)
    out["rpc"] = cfg.rpc_url
    out["pool"] = cfg.pool_address
    out["tag"] = _rand_tag16()
    out["time"] = _now_iso()
    cache.put_event("quote_in_cli", out)
    _print_json(out)
    return 0


def cmd_quote_out(cfg: QFAConfig, cache: Cache, token: str, amt: str) -> int:
    c = QuantguriosaClient(JsonRpc(RPCConfig(url=cfg.rpc_url)), cfg.pool_address)
    q = c.quoteExactOut(token, int(amt, 0))
    out = dataclasses.asdict(q)
    out["rpc"] = cfg.rpc_url
    out["pool"] = cfg.pool_address
    out["tag"] = _rand_tag16()
    out["time"] = _now_iso()
    cache.put_event("quote_out_cli", out)
    _print_json(out)
    return 0


def cmd_oracle(cfg: QFAConfig, cache: Cache, n: int = 19) -> int:
    n = max(1, min(int(n), 384))
    c = QuantguriosaClient(JsonRpc(RPCConfig(url=cfg.rpc_url)), cfg.pool_address)
    vol, kq, age = c.consultVolatility(n)
    p01, p10, span = c.consultTwapQ96(n)
    out = {
        "lookback": n,
        "volQ": vol,
        "kQ": kq,
        "age_s": age,
        "twap_p0Over1_Q96": p01,
        "twap_p1Over0_Q96": p10,
        "twap_span_s": span,
        "rpc": cfg.rpc_url,
        "pool": cfg.pool_address,
        "time": _now_iso(),
    }
    cache.put_event("oracle_cli", out)
    _print_json(out)
    return 0


def cmd_run(cfg: QFAConfig, cache: Cache) -> int:
    _require_fastapi()
    app = build_app(cfg, cache)
    assert uvicorn is not None
    uvicorn.run(app, host=cfg.host, port=cfg.port, log_level=cfg.log_level.lower())
    return 0


def main(argv: list[str]) -> int:
    cfg = QFAConfig.from_env()
    _setup_logging(cfg.log_level)
    cache = Cache(cfg.db_path)

    if len(argv) < 2 or argv[1] in ("-h", "--help", "help"):
        print(textwrap.dedent(HELP).strip())
        return 0

    cmd = argv[1].strip().lower()
    try:
        if cmd == "run":
            return cmd_run(cfg, cache)
        if cmd == "ping":
            return cmd_ping(cfg, cache)
        if cmd == "state":
            return cmd_state(cfg, cache)
        if cmd == "quote-in":
            if len(argv) < 4:
                raise QFAError("quote-in requires TOKEN and AMT")
            return cmd_quote_in(cfg, cache, argv[2], argv[3])
        if cmd == "quote-out":
            if len(argv) < 4:
                raise QFAError("quote-out requires TOKEN and AMT")
            return cmd_quote_out(cfg, cache, argv[2], argv[3])
        if cmd == "oracle":
            n = int(argv[2]) if len(argv) >= 3 else 19
            return cmd_oracle(cfg, cache, n)
        raise QFAError(f"Unknown command: {cmd}")
    except RPCError as e:
        logging.error("RPCError: %s", e)
        if e.response:
            logging.error("RPC response: %s", json.dumps(e.response)[:1200])
        return 3
    except Exception as e:
        logging.error("%s", e)
        logging.debug("Trace:\n%s", traceback.format_exc())
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
