#!/usr/bin/env bash
set -euo pipefail
# Usage: scripts/minisign_sidecar.sh <json> <key> [<comment>]
# Produces <json>.minisig signing the *canonical* bytes of <json>.
JSON="${1:?json path required}"
KEY="${2:?minisign secret key (.key) required}"
COMMENT="${3:-VeriBiota signed artifact}"

# Check minisign
if ! command -v minisign >/dev/null 2>&1; then
  echo "[minisign] minisign not found in PATH" >&2
  exit 127
fi

# Ensure we sign canonical bytes (LF + trailing newline, sorted)
# If a .canon.json exists alongside, prefer it; else canonize in place (safe).
CANON="${JSON}"
if [[ "${JSON}" != *.canon.json ]]; then
  CANON="${JSON%.json}.canon.json"
  ./veribiota --canon "${JSON}" --out "${CANON}"
fi

# Sign and place sidecar next to JSON (not the canon copy)
OUT="${JSON}.minisig"
minisign -Sm "${CANON}" -s "${KEY}" -x "${OUT}" -m -H -c "${COMMENT}"
echo "[minisign] wrote ${OUT}"

