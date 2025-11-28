# VeriBiota Examples

Drop-in examples that require zero Lean authoring.

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
