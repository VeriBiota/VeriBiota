#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SIG_DIR="$ROOT/ci_signatures"

mkdir -p "$SIG_DIR"

veribiota check alignment global_affine_v1 "$ROOT/ci_inputs/global_affine_v1.json" \
  --snapshot-out "$SIG_DIR/global_affine_v1.sig.json"

veribiota check prime prime_edit_plan_v1 "$ROOT/ci_inputs/prime_edit_plan_v1.json" \
  --snapshot-out "$SIG_DIR/prime_edit_plan_v1.sig.json"

echo "Signatures written to $SIG_DIR:"
ls -1 "$SIG_DIR" || true
