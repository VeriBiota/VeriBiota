# Snapshot Signatures

Snapshot signatures let you bind a Tier 0 verification to its inputs, schema, theorems, and build metadata. Every `veribiota check …` command can emit a `snapshot_signature_v1` JSON document via `--snapshot-out <path>`.

## Quick flow

```bash
# 1) Run the check normally
veribiota check alignment global_affine_v1 input.json

# 2) Run again and emit a snapshot signature
veribiota check alignment global_affine_v1 input.json --snapshot-out sig.json
```

Example signature shape (values illustrative; actual theorem IDs align with the manifest and `Biosim/VeriBiota/Theorems.lean`):

```json
{
  "snapshot_profile": "global_affine_v1",
  "snapshot_profile_version": "1.0.0",
  "snapshot_hash": "sha256:...input.json...",
  "schema_hash": "sha256:...global_affine_v1.schema.json...",
  "schema_id": "schemas/align/global_affine_v1.schema.json",
  "theorem_ids": ["VB_ALIGN_CORE_001", "VB_ALIGN_CORE_002"],
  "veribiota_build_id": "veribiota-2025-11-28-01",
  "veribiota_version": "0.1.0",
  "lean_version": "4.9.0",
  "timestamp_utc": "2025-11-28T02:15:00Z",
  "verification_result": "passed",
  "instance_summary": {
    "seqA_length": 151,
    "seqB_length": 151,
    "dp_score": -37
  },
  "provenance": {
    "pipeline_id": "demo_alignment_pipeline",
    "run_id": "run-0001"
  }
}
```

Archive `input.json` and `sig.json` together, or archive the signature separately and rely on the hash to attest to the payload you store elsewhere.

## CI pattern

1) Run Tier 0 checks and emit signatures:

```bash
mkdir -p ci_signatures
veribiota check alignment global_affine_v1 ci_inputs/global_affine_v1.json \
  --snapshot-out ci_signatures/global_affine_v1.sig.json --compact
veribiota check prime prime_edit_plan_v1 ci_inputs/prime_plan_v1.json \
  --snapshot-out ci_signatures/prime_plan_v1.sig.json --compact
```

2) Validate signatures:

- Validate each `*.sig.json` against `schemas/provenance/snapshot_signature_v1.schema.json`.
- Assert `verification_result == "passed"`.
- Assert required fields (hashes, theorem_ids) are present.

A tiny helper (see `.github/scripts/validate_snapshots.py`) loops over a directory, loads the schema, and enforces these rules. Failing validation should fail CI. See `.github/workflows/tier0_snapshots.yml` for a complete GitHub Actions example.

## Tips

- Use `--snapshot-out` for any Tier 0 profile: alignment, edit_script_v1, edit_script_normal_form_v1, prime_edit_plan_v1, pair_hmm_bridge_v1.
- Signatures are deterministic: they include schema hash, theorem IDs from the manifest, and a SHA-256 of the exact input bytes.
- Keep signatures alongside artifacts for long-lived provenance or audits.
