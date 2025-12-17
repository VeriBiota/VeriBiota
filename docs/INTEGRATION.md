# VeriBiota Integration Guide

This shows how to call VeriBiota from CI or Python with stdin piping and stable exit codes.

## CLI expectations

- `0` → profile holds (`status: "passed"`).
- `2` → profile checked but failed (`status: "failed"`).
- `1` → malformed input or internal error.

Profiles:

- `global_affine_v1`
- `edit_script_v1`

Each verdict JSON includes `profile_version`, `theorems`, and an `engine` block (`veribiota_version`, `lean_version`, `build_id`).

## GitHub Actions snippet (download binary)

```yaml
- name: Download VeriBiota
  run: |
    VER=0.1.0
    PLATFORM=linux-amd64
    BUNDLE="veribiota-v${VER}-${PLATFORM}"
    curl -L "https://github.com/<org>/VeriBiota/releases/download/v${VER}/${BUNDLE}.tar.gz" -o "${BUNDLE}.tar.gz"
    tar -xzf "${BUNDLE}.tar.gz"
    chmod +x "${BUNDLE}/veribiota"
    echo "VERIBIOTA_EXE=$PWD/${BUNDLE}/veribiota" >> $GITHUB_ENV
    # Optional (only needed if you move the binary away from the bundle directory):
    echo "VERIBIOTA_DATA_DIR=$PWD/${BUNDLE}" >> $GITHUB_ENV

- name: Run profile check
  run: |
    cat examples/profiles/global_affine_v1/match.json | "$VERIBIOTA_EXE" check alignment global_affine_v1 -
```

## Python helper (stdin piping)

Install/ship `veribiota_py` (in this repo):

```python
from veribiota_py import check_alignment_global_affine_v1, check_edit_script_v1

instance = {
  "seqA": "A",
  "seqB": "A",
  "scoring": {"match": 2, "mismatch": -1, "gap_open": -2, "gap_extend": -1},
  "witness": {"score": 2, "trace": [{"op": "M"}]},
}

verdict = check_alignment_global_affine_v1(instance)
assert verdict["exit_code"] == 0
assert verdict["status"] == "passed"
```

Control which executable is used via `VERIBIOTA_EXE` (default: `veribiota` on PATH). Inputs can always be piped via `-` to avoid temp files.
