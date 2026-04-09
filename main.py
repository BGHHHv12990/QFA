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
