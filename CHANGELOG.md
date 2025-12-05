# Changelog

## v0.1.0 – Attested Tier 0

Highlights
- Introduced a formal Tier 0 profile model and documented guarantees in `docs/TIER0_COMPLIANCE.md`.
- Added a profile catalog in `docs/PROFILE_SPEC.md` and a theorem registry at `Biosim/VeriBiota/Theorems.lean`.
- Expanded `profiles/manifest.json` with hashes and theorem anchors for Tier 0 schemas (alignment, edit scripts, prime plans, Pair-HMM bridge, and provenance).

Snapshot signatures
- Defined `snapshot_signature_v1` under `schemas/provenance` and wired manifest hashes.
- Added CLI support for snapshot emission: all `veribiota check` routes accept `--snapshot-out` to write a `snapshot_signature_v1` document.
- Implemented a reusable validator script at `.github/scripts/validate_snapshots.py` and a GitHub Actions workflow `.github/workflows/tier0_snapshots.yml`.
- Documented signed snapshots in `docs/SNAPSHOTS.md` and attested status in `docs/ATTESTED_PROFILES.md`.

CLI and robustness
- Hardened Tier 0 CLI behavior with snake_case summary fields and structured JSON errors.
- Added malformed input fixtures and exit code coverage for Tier 0 profiles.
- Ensured tests remain green via `lake exe biosim_tests`.

## v0.2.0 – Tier 1 Semantics & Helix Integration

Tier 1 semantics
- Added `vcf_normalization_v1`: expanded schema, Lean checker, CLI route, golden fixtures, and documentation.
- Snapshot support for VCF normalization via `--snapshot-out`.

Helix integration scaffolding
- Added `scripts/veribiota_integration.py` helper and `docs/HELIX_VERIFICATION.md` for backend/UI wiring.
- Example pipeline updated to showcase snapshot signatures.

Docs & positioning
- Verification/Integration services and attested profile visibility expanded in README and docs.
