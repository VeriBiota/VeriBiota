#!/usr/bin/env bash
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel)"
JWKS="$ROOT/security/jwks.json"
SAMPLE="$ROOT/security/jwks.sample.json"

if [ ! -f "$JWKS" ]; then
  echo "[veribiota] no security/jwks.json found; copying sample for local verify"
  cp "$SAMPLE" "$JWKS"
fi
