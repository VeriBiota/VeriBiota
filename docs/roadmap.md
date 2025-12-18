# Roadmap

## Now (v0.2.x)
- Ship a credible adoption wedge: releases (linux/macos) + GHCR container + CI templates.
- Keep “proven vs contract-checked” brutally explicit (see `docs/PROFILE_SPEC.md` + `Biosim/VeriBiota/Theorems.lean`).
- Grow the library of ready-to-run examples and CI “drop-in” templates.

## Next proofs (highest leverage)
- `pair_hmm_bridge_v1`: replace `VB_HMM_001`/`VB_HMM_002` placeholders with real mapping + equivalence theorems (OGN/variant-calling leverage).
- `vcf_normalization_v1`: replace `VB_VCF_001`/`VB_VCF_002` placeholders with real semantics-preservation + normalization uniqueness/idempotence.

## Later
- Pipeline invariants (`read_set_conservation_v1`) and additional domain checks (off-target scoring, etc.).
- Runtime engine checks (Rust/CUDA) for scalable enforcement, driven by real user demand.

## Compatibility policy
Schemas under `schema/` and `schemas/` are treated as immutable within a major version. Changes ship as `v2` alongside `v1` until migration.
