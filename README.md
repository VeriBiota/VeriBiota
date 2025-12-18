# VeriBiota
[![Docs](https://img.shields.io/badge/docs-MkDocs%20Material-7A6BB2)](https://omnisgenomics.github.io/VeriBiota/)
[![CI](https://github.com/OmnisGenomics/VeriBiota/actions/workflows/ci.yml/badge.svg?label=ci)](https://github.com/OmnisGenomics/VeriBiota/actions/workflows/ci.yml)

VeriBiota is a verification toolchain for biological / bioinformatics computation: it turns checks into deterministic, auditable artifacts (schemas, hashes, signatures) and makes them **re-runnable and hard to fake**.

It combines:
- **Profiles**: tiered checkers for specific domains (alignment, edit scripts, prime edit plans, Pair-HMM bridges, VCF normalization).
- **Artifacts**: canonical `model` / `certificate` / `checks` JSON bundles.
- **Provenance**: `snapshot_signature_v1` provenance records (hash/manifest binding; not cryptographic) plus optional Ed25519 (JWS) signing verified via JWKS.
- **Runtime enforcement**: a Rust evaluator (`biosim-eval`) plus adapters for integrating invariant checks into engines.
- **EditDAG integration**: a Lean-free Python adapter for JSON-only checks + Lean suite generation, plus a reusable GitHub Action.

## CLI surfaces
- **Lean CLI** (this repo / releases): `./veribiota …` (or `veribiota …` from a release bundle)
  - Emit/import artifacts, canonicalize, sign, verify, run profile checks, simulate, and verify results.
- **Python adapter CLI**: `python -m pip install .` → `veribiota …`
  - EditDAG JSON validation (`check-json`), normalization summaries (`lean-check`), suite generation (`generate-suite`), and a convenience `run`.

Note: both CLIs are named `veribiota`. In a checkout, use `./veribiota` for the Lean CLI; after `pip install .`, `veribiota` refers to the Python adapter.

## What you can do today
### Tier 0/Tier 1 profile checks (Lean CLI)
- `veribiota check alignment global_affine_v1`
- `veribiota check edit edit_script_v1`
- `veribiota check edit edit_script_normal_form_v1`
- `veribiota check prime prime_edit_plan_v1`
- `veribiota check hmm pair_hmm_bridge_v1`
- `veribiota check vcf vcf_normalization_v1`

Each route:
- Validates input against the profile contract (typed decoding + executable checks). Schemas are published/hashed for determinism and provenance.
- Emits a machine-readable JSON verdict + deterministic exit code.
- Optionally emits a `snapshot_signature_v1` provenance document via `--snapshot-out` (not a cryptographic signature).

Profiles listed but not yet routed in `veribiota check`: `read_set_conservation_v1`, `offtarget_score_sanity_v1` (schema/manifest only).

### Emit / import / verify canonical artifacts (Lean CLI)
- Emit demo bundle (model + certificate + checks): `./veribiota --emit-all --out build/artifacts`
- Import a model then emit: `./veribiota import --in <model.json> --emit-all --out build/artifacts`
- Canonicalize artifacts: `./veribiota --canon <checks-or-cert.json> [--out out.json]`
- Verify checks/certs: `./veribiota verify (checks|cert) <path> [--sig-mode MODE] [--jwks jwks.json]`

Artifact schema IDs: `veribiota.model.v1`, `veribiota.certificate.v1`, `veribiota.checks.v1`  
Canonicalization scheme: `veribiota-canon-v1`

### Results verification + engine integration
- Verify results metadata (and, if `biosim-eval` is available, positivity/invariant drift): `./veribiota verify results <checks.json> <results.jsonl>`
- Integrate runtime checks into other engines via `engine/biosim-checks` and the ready-to-run demos in `adapters/` (C++ / Python / Rust).

### EditDAG verification tiers (Python adapter)
- Tier 1 (JSON-only): `veribiota check-json --input 'veribiota_work/*.dag.json'`
- Tier 2 (JSON + Lean): `veribiota generate-suite …` then `lake exe veribiota-check`
- Reusable GitHub Action: `.github/actions/veribiota-check`

## Proof + attestation status
Profiles are tied to theorem IDs in `profiles/manifest.json`, and registered in `Biosim/VeriBiota/Theorems.lean`. Some theorem IDs are proof-backed today; others are reserved anchors while checks are enforced by executable contracts + CI fixtures.

- Proof-backed anchors today: `global_affine_v1`, `edit_script_v1`, `edit_script_normal_form_v1`, `snapshot_signature_v1` (binding)
- Snapshot-attested Tier 0 status: `docs/ATTESTED_PROFILES.md`

## Quickstart
Option A: use a release bundle (recommended for CI/users).

- Download and extract `veribiota-<tag>-<platform>.tar.gz`.
- Run `./veribiota --version` from the extracted directory (it includes `schemas/` + `profiles/manifest.json`).

Option B: run in CI via the container (no Lean toolchain install).

Copy/paste GitHub Actions snippet (pin the tag; don’t use floating `latest` in regulated pipelines):

```yaml
- uses: actions/checkout@v4

- name: VeriBiota (container) — check + snapshot
  run: |
    set -euo pipefail
    docker pull ghcr.io/omnisgenomics/veribiota:v0.2.1
    mkdir -p ci_signatures
    docker run --rm -v "$PWD":/work -w /work ghcr.io/omnisgenomics/veribiota:v0.2.1 \
      check alignment global_affine_v1 examples/profiles/global_affine_v1/match.json \
      --snapshot-out ci_signatures/global_affine_v1.sig.json --compact
```

Option C: build from source (Lean CLI).

```bash
elan toolchain install $(cat lean-toolchain)
lake update
lake exe cache get || true
lake build
./veribiota --help
```

Emit + verify (unsigned dev mode):

```bash
./veribiota --emit-all --out build/artifacts
./veribiota verify checks build/artifacts/checks/sir-demo.json --sig-mode unsigned
./veribiota verify cert   build/artifacts/certificates/sir-demo.json --sig-mode unsigned
```

Run a profile check (and emit a snapshot signature):

```bash
./veribiota check alignment global_affine_v1 examples/profiles/global_affine_v1/match.json \
  --snapshot-out build/snapshots/global_affine_v1.sig.json --compact
```

Run the Lean test suite used in CI:

```bash
lake exe biosim_tests
```

## What fails when things are wrong (exit codes)
VeriBiota Tier 0 exit codes are deterministic (see `docs/TIER0_COMPLIANCE.md`):

- `0`: passed obligations
- `2`: checked but failed obligations (contract violation)
- `1`: malformed input or internal error

Examples:

```bash
# Failed obligations (exit 2)
./veribiota check alignment global_affine_v1 examples/profiles/global_affine_v1/mismatch_fail.json --compact
echo $?

# Malformed JSON (exit 1)
echo '{' | ./veribiota check alignment global_affine_v1 -
echo $?
```

## Signing (Ed25519 + JWKS) and snapshots (optional)
For signed artifacts, set signing mode + key material:

```bash
export VERIBIOTA_SIG_MODE=signed-soft   # or signed-enforced
export VERIBIOTA_SIG_KEY=/path/to/ed25519.pem
export VERIBIOTA_SIG_KID=your-key-id

./veribiota --emit-all --out build/artifacts
./veribiota verify checks build/artifacts/checks/sir-demo.json --jwks security/jwks.json --print-details
./veribiota verify cert   build/artifacts/certificates/sir-demo.json --jwks security/jwks.json --print-details
```

Makefile shortcuts:

```bash
make emit
make sign-soft
make verify
```

Snapshot signatures for profile runs:
- Add `--snapshot-out <path>` to any `veribiota check …` command.
- Validate snapshot files in CI with `.github/scripts/validate_snapshots.py` (see `docs/SNAPSHOTS.md`).

Minisign detached signatures are also supported:

```bash
make minisign
make verify-minisign
```

## Runtime checks (Rust helper + adapters)
Build the Rust evaluator once:

```bash
cargo build --manifest-path engine/biosim-checks/Cargo.toml --bin biosim-eval --release
```

Then:

```bash
make simulate        # emit ODE trajectory + verify results metadata
make verify-results  # run CLI verify (uses biosim-eval if available)
```

See `docs/runtime_checks.md` and `docs/simulator-integration.md` for integration patterns.

## Python adapter (EditDAG)
Install from this repo:

```bash
python -m pip install .
veribiota --help
```

Validate DAGs (Tier 1):

```bash
veribiota check-json --input 'veribiota_work/*.dag.json'
```

Generate a Lean suite (Tier 2):

```bash
veribiota generate-suite --input 'veribiota_work/*.dag.json' --project MyProject --suite DAGs --verbose
lake build
lake exe veribiota-check
```

## Releases
On `v*` tags, CI publishes:
- **Prebuilt CLI bundles** (binary + `schemas/` + `profiles/manifest.json`) so `veribiota check … --snapshot-out …` works from the extracted directory.

Tag to release:

```bash
git tag vX.Y.Z
git push origin vX.Y.Z
```

## Docs
- `docs/QUICKSTART.md` (the fastest “try it” path)
- `docs/cli.md` (Lean CLI + Python adapter reference)
- `docs/verification-workflow.md` (end-to-end bundle → signing → verification)
- `docs/PROFILE_SPEC.md` (profiles, theorem IDs, fixtures)
- `docs/TIER0_COMPLIANCE.md` (what “Tier 0” means here)
- `docs/SNAPSHOTS.md` (snapshot signatures / attestation)
- `docs/ATTESTED_PROFILES.md` (current snapshot-attested profile list)
- `CONTRIBUTING.md` (build, test, PR workflow)
- `SECURITY.md` (vulnerability reporting)

## Repo map
- `Biosim/` — Lean library, CLI, and theorem registry
- `schema/` — stable JSON Schemas for core artifacts + EditDAG
- `schemas/` — profile/provenance/task schemas
- `profiles/` — profile manifest (schema hashes + theorem anchors)
- `engine/` — Rust runtime checks (`biosim-eval`, FFI)
- `adapters/` — C++/Python/Rust integration demos for runtime checks
- `python/` — Python adapter package (EditDAG checks + suite generation)
- `examples/` — runnable examples and CI demos

## License
VeriBiota is licensed under Apache 2.0; see `LICENSE` and `NOTICE`.

Important: VeriBiota is research software and is not a medical device. It is not intended for diagnosis, treatment, or clinical decision‑making.
