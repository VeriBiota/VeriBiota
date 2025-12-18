# CI Adoption Kit (No Lean Required)

This page is a drop-in recipe for running VeriBiota in CI without installing Lean.

## What “snapshot signatures” are (and are not)

`snapshot_signature_v1` is a **provenance record**, not a cryptographic signature: it binds a check result to the **input hash**, **schema hash/id**, **theorem IDs**, and build metadata.

For cryptographic authenticity/non-repudiation, use the **Ed25519/JWS signing** on checks/certificates (`veribiota verify … --jwks …`), which is separate from snapshot signatures.

## Option A: Use the release bundle (recommended)

Release bundles contain:
- `veribiota` (native binary)
- `schemas/` and `profiles/manifest.json` (deterministic contract inputs)
- `.github/scripts/validate_snapshots.py` (snapshot validator)

### GitHub Actions workflow (copy/paste)

Pin `VERIBIOTA_TAG` to a specific release tag (do not use floating “latest” in regulated pipelines):

```yaml
name: veribiota

on:
  pull_request:
  push:

jobs:
  tier0:
    runs-on: ubuntu-latest
    env:
      VERIBIOTA_TAG: v0.2.1 # TODO: pin to the release you adopt
      VERIBIOTA_PLATFORM: linux-amd64
    steps:
      - uses: actions/checkout@v4

      - name: Download VeriBiota release bundle
        run: |
          set -euo pipefail
          BUNDLE="veribiota-${VERIBIOTA_TAG}-${VERIBIOTA_PLATFORM}"
          curl -L "https://github.com/OmnisGenomics/VeriBiota/releases/download/${VERIBIOTA_TAG}/${BUNDLE}.tar.gz" -o "${BUNDLE}.tar.gz"
          tar -xzf "${BUNDLE}.tar.gz"
          chmod +x "${BUNDLE}/veribiota"
          echo "VERIBIOTA_EXE=$PWD/${BUNDLE}/veribiota" >> "$GITHUB_ENV"
          echo "VERIBIOTA_DATA_DIR=$PWD/${BUNDLE}" >> "$GITHUB_ENV"

      - name: Run checks + emit snapshot provenance
        run: |
          set -euo pipefail
          mkdir -p ci_signatures
          "$VERIBIOTA_EXE" check alignment global_affine_v1 examples/veribiota-example-pipeline/ci_inputs/global_affine_v1.json \
            --snapshot-out ci_signatures/global_affine_v1.sig.json --compact
          "$VERIBIOTA_EXE" check edit edit_script_normal_form_v1 examples/veribiota-example-pipeline/ci_inputs/edit_script_normal_form_v1.json \
            --snapshot-out ci_signatures/edit_script_normal_form_v1.sig.json --compact

      - name: Validate snapshot_signature_v1 documents
        run: |
          set -euo pipefail
          python3 -m pip install --quiet jsonschema
          python3 "$VERIBIOTA_DATA_DIR/.github/scripts/validate_snapshots.py" ci_signatures
```

## Option B: Use the container image

On releases, a container image is published to GHCR:

- `ghcr.io/omnisgenomics/veribiota:<tag>`

Example:

```bash
docker run --rm -v "$PWD":/work -w /work ghcr.io/omnisgenomics/veribiota:v0.2.1 \
  check alignment global_affine_v1 ci_inputs/global_affine_v1.json --snapshot-out ci_signatures/global_affine_v1.sig.json --compact
```
