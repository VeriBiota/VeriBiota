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
export VERIBIOTA_SIG_MODE=signed-soft
export VERIBIOTA_SIG_KID=veribiota-prod-2025-q1
export VERIBIOTA_SIG_KEY="$(cat ~/veribiota-secrets/veribiota_ed25519.pem)"
./veribiota --emit-all --out build/artifacts

# signed-enforced (prod):
export VERIBIOTA_SIG_MODE=signed-enforced
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

## Simulate (demo)
```bash
# Generate a small SIR trajectory (JSONL) and verify metadata
./veribiota simulate --steps 50 --dt 0.25 --out build/results/sir-sim.jsonl
./veribiota verify results build/artifacts/checks/sir-demo.json build/results/sir-sim.jsonl

# SSA-like trajectory (stubbed) instead of ODE stepping
./veribiota simulate --ssa --steps 50 --dt 0.25 --out build/results/sir-ssa.jsonl
./veribiota verify results build/artifacts/checks/sir-demo.json build/results/sir-ssa.jsonl

# Optional: evaluate drift/positivity with Rust helper (if built)
cargo build --manifest-path engine/biosim-checks/Cargo.toml --bin biosim-eval
./target/debug/biosim-eval --checks build/artifacts/checks/sir-demo.json --results build/results/sir-sim.jsonl
./target/debug/biosim-eval --json --checks build/artifacts/checks/sir-demo.json --results build/results/sir-sim.jsonl

# Makefile shortcuts
make simulate   # emit ODE trajectory + verify metadata
make eval       # build biosim-eval and print text + JSON summaries
```
