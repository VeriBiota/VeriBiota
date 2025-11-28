from __future__ import annotations

import json
import os
import subprocess
from typing import Any, Dict


def _run(args: list[str], payload: Dict[str, Any]) -> Dict[str, Any]:
  exe = os.environ.get("VERIBIOTA_EXE", "veribiota")
  proc = subprocess.run(
    [exe, *args, "-"],
    input=json.dumps(payload),
    text=True,
    capture_output=True,
  )
  try:
    data = json.loads(proc.stdout or "{}")
  except json.JSONDecodeError as exc:
    raise RuntimeError(f"VeriBiota produced non JSON output:\n{proc.stdout}\n{proc.stderr}") from exc
  data["exit_code"] = proc.returncode
  return data


def check_alignment_global_affine_v1(instance: Dict[str, Any]) -> Dict[str, Any]:
  return _run(["check", "alignment", "global_affine_v1"], instance)


def check_edit_script_v1(instance: Dict[str, Any]) -> Dict[str, Any]:
  return _run(["check", "edit", "edit_script_v1"], instance)


__all__ = [
  "check_alignment_global_affine_v1",
  "check_edit_script_v1",
]
