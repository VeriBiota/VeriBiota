#!/usr/bin/env python3
"""
Validate snapshot_signature_v1 documents in a directory:
- Schema validation against schemas/provenance/snapshot_signature_v1.schema.json
- verification_result == "passed"
- Required hashes/theorem_ids present

Usage:
  python3 .github/scripts/validate_snapshots.py <dir_with_sig_json>
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

try:
    import jsonschema
except ImportError:
    sys.stderr.write("jsonschema is required (pip install jsonschema)\n")
    sys.exit(1)


def load_schema(repo_root: Path) -> dict:
    schema_path = repo_root / "schemas" / "provenance" / "snapshot_signature_v1.schema.json"
    with schema_path.open("r", encoding="utf-8") as f:
        return json.load(f)


def find_repo_root(start: Path) -> Path:
    current = start
    while True:
        candidate = current / "schemas" / "provenance" / "snapshot_signature_v1.schema.json"
        if candidate.is_file():
            return current
        if current.parent == current:
            raise FileNotFoundError("Unable to locate schemas/provenance/snapshot_signature_v1.schema.json")
        current = current.parent


def validate_signature(schema: dict, path: Path) -> None:
    with path.open("r", encoding="utf-8") as f:
        payload = json.load(f)
    jsonschema.validate(instance=payload, schema=schema)
    if payload.get("verification_result") != "passed":
        raise ValueError(f"{path}: verification_result != 'passed'")
    if not payload.get("snapshot_hash"):
        raise ValueError(f"{path}: missing snapshot_hash")
    if not payload.get("schema_hash"):
        raise ValueError(f"{path}: missing schema_hash")
    theorems = payload.get("theorem_ids") or []
    if not isinstance(theorems, list) or len(theorems) == 0:
        raise ValueError(f"{path}: theorem_ids missing or empty")


def main() -> int:
    if len(sys.argv) != 2:
        sys.stderr.write("Usage: validate_snapshots.py <dir>\n")
        return 1
    target_dir = Path(sys.argv[1]).resolve()
    try:
        repo_root = find_repo_root(Path(__file__).resolve().parent)
    except FileNotFoundError as err:
        sys.stderr.write(f"{err}\n")
        return 1
    schema = load_schema(repo_root)
    if not target_dir.is_dir():
        sys.stderr.write(f"Not a directory: {target_dir}\n")
        return 1
    sigs = sorted(target_dir.glob("*.json"))
    if not sigs:
        sys.stderr.write(f"No *.json signatures in {target_dir}\n")
        return 1
    for sig in sigs:
        try:
            validate_signature(schema, sig)
            print(f"[ok] {sig.name}")
        except Exception as exc:  # noqa: BLE001
            sys.stderr.write(f"[fail] {sig.name}: {exc}\n")
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
