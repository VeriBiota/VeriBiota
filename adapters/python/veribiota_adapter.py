"""Minimal Python adapter that streams simulation snapshots through libveribiota_checks."""

from __future__ import annotations

import ctypes as C
import os
from pathlib import Path
from typing import Iterable, Sequence


_LIB_PATH = os.environ.get("VERIBIOTA_CHECKS_LIB", "libbiosim_checks.so")
LIB = C.CDLL(_LIB_PATH)


class Snapshot(C.Structure):
    _fields_ = [
        ("t", C.c_double),
        ("counts", C.POINTER(C.c_longlong)),
        ("counts_len", C.c_size_t),
        ("conc", C.POINTER(C.c_double)),
        ("conc_len", C.c_size_t),
    ]


class Outcome(C.Structure):
    _fields_ = [
        ("t", C.c_double),
        ("any_neg", C.c_bool),
        ("violated", C.c_bool),
        ("max_abs_drift", C.c_double),
        ("max_rel_drift", C.c_double),
    ]


LIB.veribiota_checks_init.argtypes = [C.c_char_p, C.c_char_p, C.c_int]
LIB.veribiota_checks_init.restype = C.c_int
LIB.veribiota_checks_eval.argtypes = [C.POINTER(Snapshot), C.POINTER(Outcome)]
LIB.veribiota_checks_eval.restype = C.c_int


def init_checks(checks_path: str, sig_mode: int = 0) -> None:
    payload = Path(checks_path).read_text(encoding="utf-8").encode("utf-8")
    rc = LIB.veribiota_checks_init(None, C.c_char_p(payload), sig_mode)
    if rc != 0:
        raise RuntimeError("veribiota_checks_init failed")


def eval_stream(samples: Iterable[tuple[float, Sequence[float]]]) -> None:
    for t, conc in samples:
        arr = (C.c_double * len(conc))(*conc)
        snap = Snapshot(t, None, 0, arr, len(conc))
        out = Outcome()
        rc = LIB.veribiota_checks_eval(C.byref(snap), C.byref(out))
        if rc == 2 or out.violated:
            raise RuntimeError(
                f"Invariant violated at t={t:.3f}: abs={out.max_abs_drift:.3e} "
                f"rel={out.max_rel_drift:.3e}"
            )


__all__ = ["init_checks", "eval_stream", "Outcome"]
