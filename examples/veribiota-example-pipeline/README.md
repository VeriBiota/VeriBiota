# VeriBiota Example Pipeline

This example shows how to integrate VeriBiota Tier 0 checks and snapshot signatures into CI.

It assumes `veribiota` is available on your PATH (build with `lake build` in the main repo).

## What this repo demonstrates

- Running Tier 0 checks over small example inputs.
- Emitting `snapshot_signature_v1` documents via `--snapshot-out`.
- Validating snapshots in CI using the shared validator script.
- Failing CI when a snapshot is missing or indicates a failed verification.
 - Tier 1 example (VCF normalization) to show semantic invariants.

## Run locally

```bash
# From repo root (VeriBiota already built)
cd examples/veribiota-example-pipeline
./scripts/run_verification.sh
```

You should see normal JSON verdicts on stdout and signature documents under `ci_signatures/` in `snapshot_signature_v1` format. The script covers:

- Tier 0: `global_affine_v1`, `prime_edit_plan_v1`
- Tier 1: `vcf_normalization_v1`

## CI integration

See `.github/workflows/veribiota_tier0.yml` for a GitHub Actions workflow that:

- Runs Tier 0 checks over the sample inputs.
- Runs the Tier 1 VCF normalization check.
- Emits snapshot signatures into `ci_signatures/`.
- Validates signatures with `.github/scripts/validate_snapshots.py` from the main repo.

To adapt:

1. Replace `ci_inputs/*.json` with your own instances.
2. Point the workflow to your VeriBiota location (clone or submodule).
3. Keep the validation step to fail CI if signatures are missing/invalid or `verification_result != "passed"`.
