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
