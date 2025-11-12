#!/usr/bin/env bash
set -euo pipefail

if [[ -z "${VERIBIOTA_SIG_KEY:-}" ]]; then
  echo "[sign-preflight] VERIBIOTA_SIG_KEY environment variable is required." >&2
  exit 1
fi
if [[ -z "${VERIBIOTA_SIG_KID:-}" ]]; then
  echo "[sign-preflight] VERIBIOTA_SIG_KID environment variable is required." >&2
  exit 1
fi
if [[ ! -f "$VERIBIOTA_SIG_KEY" ]]; then
  echo "[sign-preflight] Signing key not found: $VERIBIOTA_SIG_KEY" >&2
  exit 1
fi

JWKS_PATH="security/jwks.json"
if [[ ! -f "$JWKS_PATH" ]]; then
  echo "[sign-preflight] Missing JWKS file at $JWKS_PATH" >&2
  exit 1
fi

tmp_pub="$(mktemp)"
trap 'rm -f "$tmp_pub"' EXIT
if ! openssl pkey -in "$VERIBIOTA_SIG_KEY" -pubout -outform DER -out "$tmp_pub" >/dev/null 2>&1; then
  echo "[sign-preflight] Failed to derive public key via OpenSSL (is the key Ed25519 and unencrypted?)." >&2
  exit 1
fi

calc_x="$(
  python3 - <<'PY' "$tmp_pub"
import base64, sys
from pathlib import Path
data = Path(sys.argv[1]).read_bytes()
if len(data) < 32:
    raise SystemExit("Derived DER payload is too short to contain an Ed25519 key")
raw = data[-32:]
print(base64.urlsafe_b64encode(raw).decode().rstrip("="))
PY
)"

if [[ -z "$calc_x" ]]; then
  echo "[sign-preflight] Unable to compute base64url public key from signing key." >&2
  exit 1
fi

if ! command -v jq >/dev/null 2>&1; then
  echo "[sign-preflight] jq is required to inspect JWKS metadata." >&2
  exit 1
fi

x_jwks="$(jq -er --arg kid "$VERIBIOTA_SIG_KID" '.keys[] | select(.kid==$kid) | .x' "$JWKS_PATH" 2>/dev/null || true)"
if [[ -z "$x_jwks" ]]; then
  echo "[sign-preflight] JWKS is missing an entry for kid=$VERIBIOTA_SIG_KID" >&2
  exit 2
fi

if [[ "$calc_x" != "$x_jwks" ]]; then
  echo "[sign-preflight] Public key mismatch for kid=$VERIBIOTA_SIG_KID (JWKS does not match the provided private key)." >&2
  exit 3
fi

shopt -s nullglob
for artifact in build/artifacts/checks/*.json build/artifacts/certificates/*.json; do
  jq -e '
    .canonicalization.scheme == "veribiota-canon-v1"
    and (.canonicalization.newlineTerminated == true)
  ' "$artifact" >/dev/null || {
    echo "[sign-preflight] Canonicalization metadata check failed for $artifact" >&2
    exit 4
  }
done
shopt -u nullglob

echo "[sign-preflight] OK (kid=$VERIBIOTA_SIG_KID)"
