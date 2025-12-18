from __future__ import annotations

import json
import subprocess
import tempfile
from pathlib import Path
from typing import Any, Dict, Sequence


def _run_veribiota(args: Sequence[str], *, exe: str = "veribiota") -> subprocess.CompletedProcess[str]:
  return subprocess.run(
    [exe, *args],
    check=False,
    text=True,
    capture_output=True,
  )


def check_alignment_global_affine_v1(
  instance: Dict[str, Any], *, exe: str = "veribiota", compact: bool = False
) -> Dict[str, Any]:
  """
  Run the `global_affine_v1` profile with a JSON payload.

  Parameters
  ----------
  instance:
      Dict following `schemas/align/global_affine_v1.schema.json`.
  exe:
      Path to the `veribiota` CLI (default: assumes it is on $PATH).
  compact:
      If True, request compact JSON output (`--compact`).

  Returns
  -------
  Dict[str, Any]
      Parsed JSON verdict, augmented with `exit_code` and `raw_output`.
  """

  with tempfile.TemporaryDirectory(prefix="veribiota_profile_") as tmpdir:
    tmp_path = Path(tmpdir) / "input.json"
    tmp_path.write_text(json.dumps(instance), encoding="utf-8")

    args = ["check", "alignment", "global_affine_v1", str(tmp_path)]
    if compact:
      args.append("--compact")

    result = _run_veribiota(args, exe=exe)
    raw_out = result.stdout.strip()
    parsed: Dict[str, Any]
    try:
      parsed = json.loads(raw_out)
    except json.JSONDecodeError as exc:  # pragma: no cover - surfaced directly to caller
      raise RuntimeError(f"veribiota produced non-JSON output: {raw_out}") from exc

    parsed["exit_code"] = result.returncode
    parsed["raw_output"] = raw_out
    return parsed


__all__ = ["check_alignment_global_affine_v1"]
