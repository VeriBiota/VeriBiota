# VeriBiota CLI

## Install & Build
```bash
elan toolchain install $(cat lean-toolchain)
lake update && lake build
./veribiota --help
```

## Emit Artifacts
```bash
./veribiota --emit-all --out build/artifacts
# Writes:
#   build/artifacts/models/sir-demo.json
#   build/artifacts/certificates/sir-demo.json (+ .sha256)
#   build/artifacts/checks/sir-demo.json (+ .sha256)
```

## Canonicalization Utilities
```bash
./veribiota --canon build/artifacts/checks/sir-demo.json \
  --out build/artifacts/checks/sir-demo.json
./veribiota --checks-schema
# prints: veribiota.checks.v1 / canonicalization: veribiota-canon-v1 (newlineTerminated)
```

## Signing Modes (dev → soft → enforced)
```bash
# dev (unsigned) — default:
./veribiota --emit-all --out build/artifacts

# signed-soft (CI/staging):
export BIOLEAN_SIG_MODE=signed-soft
export BIOLEAN_SIG_KID=veribiota-prod-2025-q1
export BIOLEAN_SIG_KEY="$(cat ~/veribiota-secrets/veribiota_ed25519.pem)"
./veribiota --emit-all --out build/artifacts

# signed-enforced (prod):
export BIOLEAN_SIG_MODE=signed-enforced
./veribiota --emit-all --out build/artifacts
```

## Import external model → full bundle
```bash
./veribiota import --in Biosim/Examples/Model/sir.model.json \
  --emit-all --out build/artifacts
# honors --sig-mode / --sign-key / --sign-kid just like --emit-all
```

## Verify Certificates & Checks
```bash
# JWKS must contain public key w/ kid=veribiota-prod-2025-q1
./veribiota verify checks build/artifacts/checks/sir-demo.json \
  --jwks security/jwks.json --print-details
./veribiota verify cert   build/artifacts/certificates/sir-demo.json \
  --jwks security/jwks.json --print-details
```

## Results Verification
```bash
# newline-delimited snapshots (JSONL) -> drift/positivity checks
./veribiota verify results build/artifacts/checks/sir-demo.json results.jsonl \
  --jwks security/jwks.json --print-details
```
