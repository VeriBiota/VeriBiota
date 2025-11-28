# Attested Tier 0 Profiles

An attested profile is a Tier 0 profile where every successful check emits a valid `snapshot_signature_v1` document and CI enforces that these signatures exist and say `"passed"`.

## Requirements

- Profile is Tier 0 (see `docs/PROFILE_SPEC.md` and `profiles/manifest.json`).
- `veribiota check … --snapshot-out PATH` is invoked for the relevant runs.
- Snapshot signatures are retained (for N days/releases) and validated in CI:
  - Schema validation against `schemas/provenance/snapshot_signature_v1.schema.json`.
  - `verification_result == "passed"`.
  - Required hashes and theorem_ids present.

## Why

- Compliance: CI fails if signatures are missing, malformed, or show failed verification.
- Provenance: Each run is hash-linked to inputs, schema, theorems, and build metadata.
- Communication: You can truthfully claim “formally attested Tier 0 alignment/edit/HMM checks.”

## Simple badge table

| Profile                    | Tier | Attested in CI? |
|----------------------------|------|-----------------|
| global_affine_v1           | 0    | yes             |
| edit_script_v1             | 0    | yes             |
| edit_script_normal_form_v1 | 0    | yes             |
| prime_edit_plan_v1         | 0    | yes             |
| pair_hmm_bridge_v1         | 0    | yes             |

Update this table as you wire CI signatures for each profile.

## Pitch line

“We move your critical alignment/edit/HMM components to attested Tier 0: mathematically specified, theorem-anchored, and snapshot-signed in CI.”
