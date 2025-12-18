# VeriBiota CLI & Adapter

This repository ships two entrypoints:

- `./veribiota` — the Lean-built CLI (wrapper around `lake exe veribiota`).
- `veribiota` — the Python EditDAG adapter CLI (installed via `python -m pip install .`).

If you install the Python package, use `./veribiota` for the Lean CLI examples below to avoid name conflicts.

For stable exit codes and how failures surface in CI, see [`docs/FAILURE_MODES.md`](FAILURE_MODES.md).

## Install & Build (Lean CLI)
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
./veribiota --version
# prints: veribiota <toolkit> (<Lean-version>)
./veribiota --schema-info
# prints canonical schema IDs + canonicalization scheme
```

## Signing Modes (dev → soft → enforced)
```bash
# dev (unsigned) — default:
./veribiota --emit-all --out build/artifacts

# signed-soft (CI/staging):
export VERIBIOTA_SIG_MODE=signed-soft
export VERIBIOTA_SIG_KID=veribiota-prod-2025-q1
export VERIBIOTA_SIG_KEY=~/veribiota-secrets/veribiota_ed25519.pem
./veribiota --emit-all --out build/artifacts

# signed-enforced (prod):
export VERIBIOTA_SIG_MODE=signed-enforced
export VERIBIOTA_SIG_KID=veribiota-prod-2025-q1
export VERIBIOTA_SIG_KEY=~/veribiota-secrets/veribiota_ed25519.pem
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

If you emitted **unsigned** artifacts (default), verify in unsigned mode:

```bash
./veribiota verify checks build/artifacts/checks/sir-demo.json --sig-mode unsigned
./veribiota verify cert   build/artifacts/certificates/sir-demo.json --sig-mode unsigned
```

## Results Verification
Requires the Rust helper (`biosim-eval`). Build it once with:
```bash
cargo build --manifest-path engine/biosim-checks/Cargo.toml --bin biosim-eval --release
```

```bash
# newline-delimited snapshots (JSONL) -> drift/positivity checks
./veribiota verify results build/artifacts/checks/sir-demo.json results.jsonl

# Exit codes
#   0 = ok
#   1 = invalid results JSON / mismatch / biosim-eval missing or failed
#   2 = empty results file
#   3 = checks digest mismatch
#   4 = invalid checks JSON (schema/parse error)
```

The verifier requires `biosim-eval` under `target/{release,debug}`. If you just
want the “build it if needed then run” path, use `make verify-results`. See
`docs/simulator-integration.md` for adapter options.

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
make simulate        # emit ODE trajectory + verify metadata
make eval            # build biosim-eval and print text + JSON summaries
make verify-results  # build biosim-eval if available, then run CLI verify
make check           # validate checks & certificate JSON against schemas
```

## Python adapter & JSON-only checks

The Python package `veribiota` provides a lightweight, Lean-free adapter for
structural checks and Lean suite generation.

### Install
From this repository:
```bash
python -m pip install .
veribiota --help
```

### JSON-only checks (Tier 1)
```bash
veribiota check-json --input 'veribiota_work/*.dag.json'
```

This validates DAGs against the normalized EditDAG schema
(`schema/veribiota.edit_dag.v1.json`) and enforces structural invariants
(acyclicity, root uniqueness, depth monotonicity, probability conservation).
No Lean or Lake is required.

### Lean-aware checks & suite generation (Tier 2)
```bash
veribiota lean-check --input 'veribiota_work/*.dag.json' \
  --out veribiota_work/

veribiota generate-suite \
  --input 'veribiota_work/*.dag.json' \
  --project Helix \
  --suite DAGs
```

`lean-check` emits `*.lean-check.json` summaries; `generate-suite` writes a Lean
module under `Biosim.VeriBiota.<Project>.<Suite>` plus a `Generated` aggregator
exposing `Generated.allDags`, which is then consumed by `lake exe veribiota-check`.
