from __future__ import annotations

import argparse
import json
from pathlib import Path

from veribiota_adapter import eval_stream, init_checks

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_CHECKS = ROOT / "examples/checks.mass.json"
DEFAULT_TRAJ = ROOT / "examples/trajectory.sample.jsonl"


def load_trajectory(path: Path):
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        point = json.loads(line)
        yield float(point["t"]), point.get("conc") or point.get("counts", [])


def main() -> None:
    parser = argparse.ArgumentParser(description="VeriBiota ctypes streaming demo")
    parser.add_argument("--checks", type=Path, default=DEFAULT_CHECKS)
    parser.add_argument(
        "--trajectory",
        type=Path,
        default=DEFAULT_TRAJ,
    )
    args = parser.parse_args()

    init_checks(str(args.checks))
    eval_stream(load_trajectory(args.trajectory))
    print("All invariants respected ✔")
if __name__ == "__main__":
    main()
