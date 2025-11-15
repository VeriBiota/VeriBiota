# VERIBIOTA-0001 — Runtime Checks Contract (Draft)

**Status:** Draft  
**Schema IDs:** `veribiota.checks.v1`, `veribiota.certificate.v1`

## Problem
Consumers need deterministic, engine-agnostic verification of trajectories.

## Proposal
- Positivity checks for `counts` and `conc`.
- Linear invariants: `weights: number[]`, `tolerance_abs?: number`, `tolerance_rel?: number`.
- Outcome: `{ violated: boolean, max_abs_drift: number, max_rel_drift: number, ... }`.
- Signature: Ed25519 over canonicalized payload; JWKS-distributed public keys.

## Rationale
Aligns formal proofs (Lean) with runtime enforcement at scale.

## Backwards Compatibility
Tolerances are optional; default is strict conservation.

## Test Vectors
- See `tests/runtime/positivity.json`, `tests/runtime/lininv.json`.

## KPIs
- Determinism failure rate: must be 0% on release builds.
- Runtime coverage: unit + property tests cover ≥90% of runtime code paths.
- Spec drift: no schema change without an RFC PR and approved compatibility note.
- Performance: evaluation ≥1M species‑weights ops/sec/core for linear invariants (target).

## Research agenda
- Beyond linear invariants: interval arithmetic & log‑domain stability; conserved moieties for non‑ideal systems; stochastic bounds.
- Partial observability: project invariants into measured subspaces and bound drift.
- Streaming verification: online invariant tracking and time‑windowed tolerances.
- Formal → runtime linkage: generate invariant JSON directly from Lean proofs to eliminate human transcription.

## Next steps
Implement the Rust checks and the schema cleanup first; these two unlock credibility and integrations.

Cut a v0.2.0 with version flags + fixed validator.

Then ship Python/Node wrappers and wire VeriBiota bundles into your engine pipeline so every run leaves a certificate trail.
