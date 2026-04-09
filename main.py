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
