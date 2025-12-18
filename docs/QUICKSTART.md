# VeriBiota Quickstart

Get from zero to a runnable profile check in minutes. Some profiles are backed by non‑placeholder Lean theorem anchors today (alignment + edit application + edit normalization + snapshot binding); others are contract-checked and fixture-tested while their theorem IDs remain reserved anchors. For the full list, see [`docs/PROFILE_SPEC.md`](PROFILE_SPEC.md). For emitting provenance records via `--snapshot-out`, see [`docs/SNAPSHOTS.md`](SNAPSHOTS.md).

## 15-minute onboarding funnel (CI wedge)

Goal: go from zero → “CI gates on proven invariants” in under 15 minutes.

1) **Install**
   - Use a **release bundle** (recommended) or **pinned container image** for CI stability (see [`docs/CI_ADOPTION_KIT.md`](CI_ADOPTION_KIT.md)).
   - Use a local build only if you’re actively hacking on the Lean code.

2) **Run one known-good example**
   - Run `global_affine_v1` once and confirm you get JSON to stdout and exit code `0`.

3) **Make failure real (on purpose)**
   - Run `examples/profiles/global_affine_v1/mismatch_fail.json` (or flip `witness.score` in `match.json`).
   - You should see `"status":"failed"` and exit code `2`.

4) **Add the CI gate**
   - Minimal GitHub Actions job (release bundle, emits snapshot provenance):

   ```yaml
   name: veribiota-tier0
   on: [pull_request, push]
   jobs:
     tier0:
       runs-on: ubuntu-latest
       env:
         VERIBIOTA_TAG: v0.2.1 # pin to the release you adopt
         VERIBIOTA_PLATFORM: linux-amd64
       steps:
         - uses: actions/checkout@v4
         - name: Download VeriBiota
           run: |
             set -euo pipefail
             BUNDLE="veribiota-${VERIBIOTA_TAG}-${VERIBIOTA_PLATFORM}"
             curl -L "https://github.com/OmnisGenomics/VeriBiota/releases/download/${VERIBIOTA_TAG}/${BUNDLE}.tar.gz" -o "${BUNDLE}.tar.gz"
             tar -xzf "${BUNDLE}.tar.gz"
             chmod +x "${BUNDLE}/veribiota"
             echo "VERIBIOTA_EXE=$PWD/${BUNDLE}/veribiota" >> "$GITHUB_ENV"
             echo "VERIBIOTA_DATA_DIR=$PWD/${BUNDLE}" >> "$GITHUB_ENV"
         - name: Run Tier 0 check + emit snapshot
           run: |
             set -euo pipefail
             mkdir -p ci_signatures
             "$VERIBIOTA_EXE" check alignment global_affine_v1 examples/profiles/global_affine_v1/match.json \
               --snapshot-out ci_signatures/global_affine_v1.sig.json --compact
         - uses: actions/upload-artifact@v4
           with:
             name: veribiota-snapshots
             path: ci_signatures/
   ```

5) **Optional authenticity**
   - If you need authenticity/non-repudiation, use Ed25519/JWS signing on checks/certs and verify with `veribiota verify …` (see [`docs/canonicalization.md`](canonicalization.md) and [`docs/FAILURE_MODES.md`](FAILURE_MODES.md)).

6) **Expansion path**
   - Start with `edit_script_v1`, then `edit_script_normal_form_v1`, then contract-checked profiles (`prime_edit_plan_v1`, `pair_hmm_bridge_v1`, `vcf_normalization_v1`).

## 0. Choose an install path

### Option A (recommended): use a release bundle

Download the release archive for your platform and extract it. Run `./veribiota …` from the extracted directory (the bundle includes `schemas/` and `profiles/manifest.json`, which are required for `--snapshot-out`).

### Option B: use the container image

Use a pinned tag for CI stability:

```bash
docker run --rm -v "$PWD":/work -w /work ghcr.io/omnisgenomics/veribiota:v0.2.1 --help
```

### Option C: build from source

## 1. Install the toolchain (source build only)

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
  | sh -s -- -y --default-toolchain=$(cat lean-toolchain)
echo "$HOME/.elan/bin" >> "$HOME/.profile"
source "$HOME/.profile"  # ensure elan is on PATH
```

Then fetch dependencies and build once:

```bash
lake update
lake build
```

## 2. Run a canonical profile check (no Lean editing)

Use the bundled global affine alignment example:

```bash
# From repo root
./veribiota check alignment global_affine_v1 examples/profiles/global_affine_v1/match.json
```

Expected shape (status must be `passed`):

```json
{
  "profile": "global_affine_v1",
  "profile_version": "1.0.0",
  "status": "passed",
  "theorems": ["VB_ALIGN_CORE_001", "VB_ALIGN_CORE_002"],
  "instance": {
    "seqA_length": 1,
    "seqB_length": 1,
    "trace_length": 1,
    "dp_score": 2,
    "alignment_matches_spec": true
  },
  "engine": {
    "veribiota_version": "0.1.0",
    "lean_version": "4.9.0",
    "build_id": "dev"
  },
  "signature": null
}
```

Shortcut: `scripts/check_alignment.sh examples/profiles/global_affine_v1/match.json` will build (if needed), run the profile, and summarize the result.

Tip: pass `-` as the input path to read JSON from stdin (useful for piping from other tools).

## 3. Edit script sanity profile (no-Lean extension)

Try the edit-script checker:

```bash
./veribiota check edit edit_script_v1 examples/profiles/edit_script_v1/simple_sub.json
```

You should see `status: "passed"` with `VB_EDIT_001` in the theorem list.

For normalized edit scripts, use:

```bash
./veribiota check edit edit_script_normal_form_v1 examples/veribiota-example-pipeline/ci_inputs/edit_script_normal_form_v1.json
```

You should see `VB_EDIT_001` and `VB_EDIT_002`, plus `normal_form: true` in the instance summary.

## 4. What “success” looks like

- `lake build` completes without errors.
- Profile commands exit `0` and emit JSON with `status: "passed"`.
- Theorems listed match the profile manifest (guarded in CI).

If you want a one-liner sanity check before commits:

```bash
lake exe biosim_tests
```

This runs the golden profile suites and manifest hash guard used in CI.
