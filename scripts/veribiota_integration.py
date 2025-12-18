#!/usr/bin/env python3
"""
Minimal helper for Helix/OGN to call VeriBiota and capture snapshot signatures.
Usage:
    from scripts.veribiota_integration import run_veribiota_check
    result = run_veribiota_check("alignment", "global_affine_v1", "input.json")
"""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Optional


VERIBIOTA_BIN = os.getenv("HELIX_VERIBIOTA_BIN", "veribiota")


@dataclass
class VeriBiotaResult:
    verified: bool
    profile: str
    status: str
    snapshot: Optional[dict]
    error: Optional[str]
    raw_output: str


def run_veribiota_check(domain: str, profile: str, input_path: str, compact: bool = True) -> VeriBiotaResult:
    """Run `veribiota check ...` with snapshot emission and return parsed results."""
    snapshot_path = Path(tempfile.gettempdir()) / f"{profile}.snapshot.json"
    args = [
        VERIBIOTA_BIN,
        "check",
        domain,
        profile,
        input_path,
        "--snapshot-out",
        str(snapshot_path),
    ]
    if compact:
        args.append("--compact")
    proc = subprocess.run(args, capture_output=True, text=True)
    stdout = proc.stdout.strip()
    snapshot = None
    error = None
    try:
        verdict = json.loads(stdout)
    except json.JSONDecodeError:
        verdict = None
        error = f"Failed to parse veribiota output: {stdout or proc.stderr}"
    if snapshot_path.exists():
        try:
            snapshot = json.loads(snapshot_path.read_text())
        except json.JSONDecodeError:
            error = f"Snapshot parse error at {snapshot_path}"
    verified = verdict is not None and verdict.get("status") == "passed" and proc.returncode == 0
    return VeriBiotaResult(
        verified=verified,
        profile=profile,
        status=verdict.get("status") if verdict else "error",
        snapshot=snapshot,
        error=error or (proc.stderr.strip() if proc.returncode != 0 else None),
        raw_output=stdout,
    )
