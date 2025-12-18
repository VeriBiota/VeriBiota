# VeriBiota Examples

Drop-in examples that require zero Lean authoring.

## Minimal (container) template repo

Files: `examples/veribiota-minimal/`

- `ci_inputs/global_affine_v1.json` — smallest possible passing `global_affine_v1` instance.
- `.github/workflows/veribiota.yml` — workflow template that runs the published container and uploads `snapshot_signature_v1` artifacts.

Run (from this repo):

```bash
cd examples/veribiota-minimal
docker run --rm -v "$PWD":/work -w /work ghcr.io/omnisgenomics/veribiota:v0.2.1 \
  check alignment global_affine_v1 ci_inputs/global_affine_v1.json --snapshot-out ci_signatures/global_affine_v1.sig.json --compact
```

## Alignment profile (`global_affine_v1`)

Files: `examples/profiles/global_affine_v1/`

- `match.json` — identical single-base sequences (passes).
- `gap.json` — gap + match trace (passes).
- `mismatch_fail.json` — mismatched witness score (fails with exit code 2).

Run:

```bash
./veribiota check alignment global_affine_v1 examples/profiles/global_affine_v1/match.json
```

## Edit script profile (`edit_script_v1`)

Files: `examples/profiles/edit_script_v1/`

- `simple_sub.json` — one substitution (passes).
- `ins_del.json` — insertion case (passes).
- `payload_fail.json` — wrong payload vs target (fails).

Run:

```bash
./veribiota check edit edit_script_v1 examples/profiles/edit_script_v1/simple_sub.json
```

Tip: `VERIBIOTA_BUILD_ID` can be set to tag outputs (e.g., CI build SHA).
