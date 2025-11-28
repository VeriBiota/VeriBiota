#!/usr/bin/env bash
set -euo pipefail

INPUT="${1:-examples/profiles/global_affine_v1/match.json}"
BUILD_ID="${VERIBIOTA_BUILD_ID:-cli}"

echo "[veribiota] ensuring build is up to date..."
lake build > /dev/null

echo "[veribiota] running global_affine_v1 on ${INPUT}"
OUTPUT="$(VERIBIOTA_BUILD_ID="${BUILD_ID}" ./veribiota check alignment global_affine_v1 "${INPUT}")"
EXIT=$?

echo "${OUTPUT}"

if [ "${EXIT}" -eq 0 ]; then
  echo "[veribiota] global_affine_v1 passed."
else
  echo "[veribiota] global_affine_v1 failed (exit ${EXIT})."
fi

exit "${EXIT}"
