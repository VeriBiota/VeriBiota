#!/usr/bin/env bash
set -euo pipefail

if [[ -z "${VERIBIOTA_SIG_KEY:-}" ]]; then
  echo "[sign-key-path] VERIBIOTA_SIG_KEY environment variable is required." >&2
  exit 1
fi

INPUT="$VERIBIOTA_SIG_KEY"

if [[ -f "$INPUT" ]]; then
  python3 - <<'PY' "$INPUT"
import os, sys
print(os.path.abspath(sys.argv[1]))
PY
  exit 0
fi

if [[ "$INPUT" == -----BEGIN* ]]; then
  mkdir -p security
  TARGET="security/.veribiota_signing.key"
  printf '%s\n' "$INPUT" > "$TARGET"
  chmod 600 "$TARGET"
  python3 - <<'PY' "$TARGET"
import os, sys
print(os.path.abspath(sys.argv[1]))
PY
  echo "[sign-key-path] Wrote inline signing key material to $TARGET" >&2
  exit 0
fi

echo "[sign-key-path] VERIBIOTA_SIG_KEY must be a file path or PEM-formatted key content." >&2
exit 1
