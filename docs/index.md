# VeriBiota™ — Mathematically Proven Biology

VeriBiota transforms biological and biochemical models into cryptographically signed, formally verified artifacts. Every reaction, rate law, and invariant is backed by theorem‑proven logic and a reproducible audit trail — turning biological simulation into a compliance‑grade science.

- Open standard for proof‑backed biological simulation
- Deterministic JSON schemas for models, certificates, and checks
- Ed25519 signatures + JWKS verification for authenticity
- Formal proofs in Lean 4 with executable semantics on the roadmap

See Why VeriBiota (docs/why.md) to understand the problems we solve and who benefits.

## Quickstart
```bash
# 1) Install Lean toolchain and build
elan toolchain install $(cat lean-toolchain)
lake update && lake build

# 2) Emit a complete demo bundle (model + certificate + checks)
./veribiota --emit-all --out build/artifacts

# 3) Verify signed artifacts with your JWKS
./veribiota verify checks build/artifacts/checks/sir-demo.json \
  --jwks security/jwks.json --print-details
./veribiota verify cert   build/artifacts/certificates/sir-demo.json \
  --jwks security/jwks.json --print-details
```

Tip: For a full signing round‑trip with a disposable local key, see Getting Started (docs/getting-started.md).

## Explore the docs
- Why VeriBiota (docs/why.md)
- Getting Started (docs/getting-started.md)
- Verification Workflow (docs/verification-workflow.md)
- Architecture (docs/architecture.md)
- CLI Reference (docs/cli.md)
- Canonicalization & Signing (docs/canonicalization.md)
- Model IR (docs/model-ir.md)
- Invariants (docs/invariants.md)
- Runtime Checks (docs/runtime_checks.md)
- QA Checklist (docs/qa_checklist.md)
- Roadmap (docs/roadmap.md)

## Try a simulation
```bash
# ODE-like demo (conc values)
./veribiota simulate --steps 50 --out build/results/sir-sim.jsonl
./veribiota verify results build/artifacts/checks/sir-demo.json build/results/sir-sim.jsonl

# SSA-like demo (stubbed)
./veribiota simulate --ssa --steps 50 --out build/results/sir-ssa.jsonl
./veribiota verify results build/artifacts/checks/sir-demo.json build/results/sir-ssa.jsonl
```

## Mission
Make verified computation the default for life sciences.

VeriBiota unifies Lean proofs, deterministic schemas, cryptographic signatures, and an executable runtime (roadmap) so that every model is provable, auditable, and portable — from a graduate thesis to FDA submissions.
