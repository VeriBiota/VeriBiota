# VeriBiota — Verification Contracts + Attestation for Biology

VeriBiota turns biological / bioinformatics checks into **deterministic, auditable artifacts**: versioned JSON schemas, reproducible verdicts, and optional snapshot signatures for provenance.

Some profile surfaces are backed by non‑placeholder Lean theorem anchors today; others are contract-checked and fixture-tested while their theorem IDs remain reserved anchors. See `docs/PROFILE_SPEC.md` and `Biosim/VeriBiota/Theorems.lean` for the current map.

- Open standard for verification bundles and profile checks
- Deterministic JSON schemas for models, certificates, and checks
- Ed25519 signatures + JWKS verification for authenticity
- Lean 4 contracts for profile checks (proof depth varies by profile)

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

## Verification tiers

- **Tier 0 – raw JSON**: emit model/trajectory/DAG JSON with no structural checks (not recommended for CI).
- **Tier 1 – JSON-only checks**: run the Python adapter (`veribiota check-json`) on `veribiota.edit_dag.v1` DAGs for fast structural sanity without Lean.
- **Tier 2 – JSON + Lean**: generate a Lean EditDAG suite (`veribiota generate-suite`) and run `lake exe veribiota-check` (or the reusable GitHub Action) to typecheck the generated suite against `EditDAG`.

## Explore the docs
- Why VeriBiota (docs/why.md)
- Getting Started (docs/getting-started.md)
- Verification Workflow (docs/verification-workflow.md)
- Architecture (docs/architecture.md)
- CLI & Adapter Reference (docs/cli.md)
- Canonicalization & Signing (docs/canonicalization.md)
- Model IR (docs/model-ir.md)
- Invariants (docs/invariants.md)
- Runtime Checks (docs/runtime_checks.md)
- DAG Schema (docs/schema/edit_dag.md)
- Code Scanning (CodeQL) (docs/code_scanning.md)
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

VeriBiota unifies Lean contracts, deterministic schemas, cryptographic signatures, and runtime evaluation so results are auditable and portable — from a graduate thesis to regulated pipelines.
