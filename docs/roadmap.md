# Roadmap

## Now (v0.2.x)
- Ship a credible adoption wedge: releases (linux/macos) + GHCR container + CI templates.
- Keep “proven vs contract-checked” brutally explicit (see `docs/PROFILE_SPEC.md` + `Biosim/VeriBiota/Theorems.lean`).
- Grow the library of ready-to-run examples and CI “drop-in” templates.

## Next proofs (highest leverage)
- `pair_hmm_bridge_v1`: replace `VB_HMM_001`/`VB_HMM_002` placeholders with real mapping + equivalence theorems (OGN/variant-calling leverage).
- `vcf_normalization_v1`: replace `VB_VCF_001`/`VB_VCF_002` placeholders with real semantics-preservation + normalization uniqueness/idempotence.

## PairHMM proof sprint blueprint (`pair_hmm_bridge_v1`)

Current reality: `pair_hmm_bridge_v1` is routed in the CLI (`veribiota check hmm pair_hmm_bridge_v1 …`), but its theorem anchors (`VB_HMM_001`, `VB_HMM_002`) are placeholders today (`Biosim/VeriBiota/Theorems.lean`).

### Sprint goal

Replace placeholder PairHMM bridge anchors with non-placeholder Lean theorems that meaningfully bind:

- the DP recurrence semantics,
- the bridge mapping between “spec DP” and “engine DP” representations,
- and a clear statement of numeric-domain assumptions.

Ship a release where “Proven” includes `pair_hmm_bridge_v1` in a narrow, explicitly stated scope.

### Scope discipline

Do **not** try to prove full floating-point behavior for all lengths on day one. Ship a layered proof:

- **Layer A:** pure DP in an exact semiring (mathematical spec).
- **Layer B:** log-space transformation correctness.
- **Layer C:** bounded rounding model *or* an “exact rational” reference path for small cases.

### Work packages

**WP0: Define the spec precisely**

Artifacts:
- A formal DP spec function with explicit states and base cases.
- A statement of the bridge mapping between witness format and the DP grid.

Acceptance:
- The spec is executable in Lean for small sequences (so you can test it).

**WP1: `VB_HMM_001` – DP recurrence correctness**

Theorem idea:
- For given parameters and sequences, the DP computed by the recurrence equals the spec definition.

Deliver:
- Theorem + supporting lemmas for init/step invariants (structured for maintainability).

Acceptance:
- Theorem is non-placeholder and referenced from the theorem registry (`Biosim/VeriBiota/Theorems.lean`).

**WP2: `VB_HMM_002` – bridge mapping correctness**

Theorem idea:
- If the witness claims “DP matches spec” under the bridge mapping, then:
  - the decoded witness grid corresponds to spec DP values, and
  - any reported final score equals the spec final score.

Acceptance:
- The theorem explicitly binds the witness representation to the spec.

**WP3: Tighten the runtime check to the proof boundary**

If the runtime check compares floats, define an explicit policy aligned to what the theorems cover:
- log-space tolerance (explicit epsilon), and/or
- exact rational reference for small cases.

Acceptance:
- Deterministic failure reasons; the check matches the proof scope.

**WP4: Add regression fixtures**

Add three fixture classes under `Tests/profiles/pair_hmm_bridge_v1/`:

- `passes`: small sequences with known scores
- `fails`: one cell perturbed / mapping broken
- `errors`: malformed witness shape

Acceptance:
- CI runs them and enforces stable exit codes (`docs/FAILURE_MODES.md`).

### Definition of done

- `VB_HMM_001` and `VB_HMM_002` are non-placeholder and imported in `Biosim/VeriBiota/Theorems.lean`.
- `profiles/manifest.json` references the non-placeholder theorems for `pair_hmm_bridge_v1`.
- The CLI profile runner binds to the same metadata pattern used by snapshot signatures.
- Docs list `pair_hmm_bridge_v1` under “Proven” with a precise scope statement (and remain explicit about what’s *not* proven yet).

## Later
- Pipeline invariants (`read_set_conservation_v1`) and additional domain checks (off-target scoring, etc.).
- Runtime engine checks (Rust/CUDA) for scalable enforcement, driven by real user demand.

## Compatibility policy
Schemas under `schema/` and `schemas/` are treated as immutable within a major version. Changes ship as `v2` alongside `v1` until migration.
