# VeriBiota Pilot Demo Pack (v1)

This folder is the exact bundle we send to pilot customers. It contains:

- `build/artifacts/` – canonical SIR model, certificate, and checks bundles plus SHA256 sidecars.
- `jwks.sample.json` – sample public key document for signature verification drills.
- `Makefile` + `scripts/pilot_demo.sh` – frozen helpers that run the emit → sign-soft → verify workflow.

## Verification cookbook (1‑pager)

Run from repository root. Artifacts land in `build/artifacts/`.

1) Emit and sign (soft):
```bash
VERIBIOTA_SIG_MODE=signed-soft \
VERIBIOTA_SIG_KEY=/path/to/ed25519.pem \
VERIBIOTA_SIG_KID=veribiota-prod-2025-q1 \
  ./veribiota --emit-all --out build/artifacts \
    --sign-key "$VERIBIOTA_SIG_KEY" --sign-kid "$VERIBIOTA_SIG_KID"
```

2) Verify checks and certificate:
```bash
./veribiota verify checks build/artifacts/checks/sir-demo.json \
  --jwks security/jwks.json --print-details
./veribiota verify cert   build/artifacts/certificates/sir-demo.json \
  --jwks security/jwks.json --print-details
```

3) Canonicalize (optional) and compare:
```bash
./veribiota --canon build/artifacts/checks/sir-demo.json \
  --out build/artifacts/checks/sir-demo.canon.json
diff -u build/artifacts/checks/sir-demo.json \
       build/artifacts/checks/sir-demo.canon.json
```

What “good” looks like
- SHA lines print with stable values across reruns/OS.
- `verify … --print-details` shows `signature.kid=…`, matching your JWKS.
- No errors; exit code 0.

Common failure modes (and quick fixes)
- Wrong `kid` or JWKS mismatch → ensure `security/jwks.json` contains the Ed25519 public key matching `VERIBIOTA_SIG_KEY` (see docs key‑gen recipe).
- Non‑canonical bytes / CRLF → run `veribiota --canon <file> --out <file>` to enforce LF + stable ordering.
- Missing signature in enforced mode → set `VERIBIOTA_SIG_MODE=signed-enforced` and provide `--sign-key/--sign-kid`.
- Header mismatch (SPKI vs raw key) → JWKS `x` must be the 32‑byte raw Ed25519 public key, base64url‑encoded (no padding).

Tip: deterministic output means the schema contract is locked. Re‑emit later and compare SHA256 lines to confirm nothing drifted.
