#!/usr/bin/env bash
set -euo pipefail

if [[ -z "${VERIBIOTA_STRIPE_PILOT_URL:-}" ]]; then
  echo "VERIBIOTA_STRIPE_PILOT_URL environment variable is not set." >&2
fi

make emit
VERIBIOTA_SIG_MODE=signed-soft make sign-soft
make verify

echo "Artifacts ready under build/artifacts"
if [[ -n "${VERIBIOTA_STRIPE_PILOT_URL:-}" ]]; then
  echo "Stripe link: ${VERIBIOTA_STRIPE_PILOT_URL}"
fi
