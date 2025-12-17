# VeriBiota Quickstart

Get from zero to a runnable profile check in minutes. Some profiles are backed by non‑placeholder Lean theorem anchors today (alignment + edit application); others are contract-checked and fixture-tested while their theorem IDs remain reserved anchors. For the full list, see [`docs/PROFILE_SPEC.md`](PROFILE_SPEC.md). For emitting provenance signatures, see [`docs/SNAPSHOTS.md`](SNAPSHOTS.md).

## 0. Choose an install path

### Option A (recommended): use a release bundle

Download the release archive for your platform and extract it. Run `./veribiota …` from the extracted directory (the bundle includes `schemas/` and `profiles/manifest.json`, which are required for `--snapshot-out`).

### Option B: build from source

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
    "dpScore": 2,
    "alignment_matches_spec": true
  },
  "engine": {
    "veribiota_version": "0.1.0",
    "lean_version": "4.9.0"
  }
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

## 4. What “success” looks like

- `lake build` completes without errors.
- Profile commands exit `0` and emit JSON with `status: "passed"`.
- Theorems listed match the profile manifest (guarded in CI).

If you want a one-liner sanity check before commits:

```bash
lake exe biosim_tests
```

This runs the golden profile suites and manifest hash guard used in CI.
