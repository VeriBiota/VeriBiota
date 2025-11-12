# Verification Workflow

A model’s journey from JSON to verified, signed artifacts and runtime checks.

## 1) Author or import the model
Start from your model JSON or import an example:
```bash
./veribiota import --in Biosim/Examples/Model/sir.model.json \
  --emit-all --out build/artifacts
```
This produces canonicalized model JSON plus a proof‑backed certificate and invariant checks.

## 2) Canonicalize for determinism
Enforce LF endings, stable ordering, and trailing newline for byte‑for‑byte equality:
```bash
./veribiota --canon build/artifacts/checks/sir-demo.json \
  --out build/artifacts/checks/sir-demo.json
```

## 3) Sign with Ed25519 (JWKS)
Attach authenticity and provenance using Ed25519 and JWKS:
```bash
export VERIBIOTA_SIG_MODE=signed-soft
export VERIBIOTA_SIG_KEY=/path/to/ed25519.pem
export VERIBIOTA_SIG_KID=your-key-id
make sign-soft
```
The signature block records `kid`, `issuedAt`, `payloadHash` (SHA‑256), and canonicalization settings.

Preflight checks (CI/local):
- `scripts/sign_preflight.sh` verifies JWKS matches the private key and that artifacts advertise `canonicalization: { scheme: "veribiota-canon-v1", newlineTerminated: true }`.
- Signing is refused if canonicalization mismatches or header/payload metadata diverge.

## 4) Verify certificates and checks
Consumers verify both canonicalization and signature:
```bash
./veribiota verify checks build/artifacts/checks/sir-demo.json \
  --jwks security/jwks.json --print-details
./veribiota verify cert   build/artifacts/certificates/sir-demo.json \
  --jwks security/jwks.json --print-details
```
Exit codes differentiate canonical mismatch, signature failure, and enforcement gaps. See Canonicalization & Signing (docs/canonicalization.md).

## 5) Verify simulation results
Runtime engines evaluate invariant drift and positivity against the signed checks JSON:
```bash
./veribiota verify results build/artifacts/checks/sir-demo.json results.jsonl \
  --jwks security/jwks.json --print-details
```

## Provenance chain
```
model.json → certificate.json → checks.json → signature → JWKS
```

Treat schemas under `schema/` as immutable for a given major version. All artifacts carry their `scheme` and canonicalization policy explicitly.

## Minisign sidecars (optional)
For Unix‑friendly detached signatures, you can create `*.minisig` files that sign the same canonical bytes used for JWS.

```bash
# Sign (assumes VERIBIOTA_MINISIGN_SEC points to your .key)
make minisign

# Verify (assumes VERIBIOTA_MINISIGN_PUB points to your .pub)
make verify-minisign
```

Notes: canonicalize before signing (the helper does this automatically), never commit keys, and keep this optional on Windows. See the “Minisign sidecars (optional)” section in the repository README for details.
