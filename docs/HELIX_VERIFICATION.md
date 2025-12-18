# Verified by VeriBiota (Helix/OGN integration)

Goal: make verification visible in Helix Studio/OGN by calling `veribiota` behind the scenes and surfacing a “Verified by VeriBiota” chip on results.

## Backend helper (sketch)

- Provide a small helper (e.g., `helix/veribiota_integration.py`) that:
  - Accepts an input JSON for a profile (alignment, prime plan, VCF normalization, etc.).
  - Runs `VERIBIOTA_BIN check <domain> <profile> <input> --snapshot-out <tmp>` (default `VERIBIOTA_BIN=veribiota`).
  - Returns `{verified: bool, snapshot: dict | None, error: str | None}` by parsing the verdict and optional `snapshot_signature_v1`.
- Config:
  - `HELIX_VERIBIOTA_BIN` env or config path to `veribiota`.
  - Toggle to disable verification in debug mode.

## UI widget

- In result panels (alignment preview, CRISPR/prime plans, VCF normalization):
  - Show a chip: `✅ Verified by VeriBiota` or `⚠️ Verification failed/not run`.
  - Display `profile_id`, `tier` (0 or 1), `attested` (yes/no).
  - Hover/click: show snapshot hash, theorem IDs, timestamp (pulled from the snapshot signature).

## Minimal flow to wire first

- Start with `prime_edit_plan_v1` (Tier 0) or `vcf_normalization_v1` (Tier 1).
- On compute/preview:
  1. Write the candidate JSON input to a temp file.
  2. Call the helper to run `veribiota check ... --snapshot-out ...`.
  3. Store `snapshot_signature_v1` alongside the result; mark verified status.
  4. Render the chip in the UI.

## Docs link-out

- Link Helix docs to VeriBiota verification docs:
  - `docs/TIER0_COMPLIANCE.md`
  - `docs/ATTESTED_PROFILES.md`
  - `docs/SNAPSHOTS.md`
  - `docs/VCF_NORMALIZATION.md`
