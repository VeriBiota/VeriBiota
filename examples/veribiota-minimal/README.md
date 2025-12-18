# VeriBiota minimal example (container)

This folder is a tiny “copy/paste into a new repo” starter:

- One input JSON: `ci_inputs/global_affine_v1.json`
- One command: run `veribiota check …` via the published container
- One output: `ci_signatures/global_affine_v1.sig.json` (`snapshot_signature_v1`)

## Run locally (Docker required)

```bash
cd examples/veribiota-minimal

docker pull ghcr.io/omnisgenomics/veribiota:v0.2.1
mkdir -p ci_signatures
docker run --rm -v "$PWD":/work -w /work ghcr.io/omnisgenomics/veribiota:v0.2.1 \
  check alignment global_affine_v1 ci_inputs/global_affine_v1.json \
  --snapshot-out ci_signatures/global_affine_v1.sig.json --compact
```

Notes:
- `snapshot_signature_v1` is a **provenance binding record**, not a cryptographic signature (no keys / nonrepudiation).
- Exit codes: `0` passed, `2` failed obligations, `1` malformed/internal (see `docs/TIER0_COMPLIANCE.md`).

## Turn this into a standalone repo

Copy the contents of `examples/veribiota-minimal/` into the root of a new repo.
The workflow template at `.github/workflows/veribiota.yml` will then run on GitHub Actions and upload snapshots as artifacts.
