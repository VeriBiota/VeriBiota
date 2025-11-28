# Tier 0 Compliance

Tier 0 compliance defines the minimum guarantees VeriBiota provides for a verification profile. Tier 0 profiles are safe to adopt in production CI and pipelines.

- Stable, documented JSON schema.
- Registered theorem set in the VeriBiota theorem registry.
- CLI entrypoint that validates instances against the schema and proof obligations.
- Golden fixtures and tests that exercise success/failure cases, including malformed input.
- Defined exit code semantics and structured JSON output (success and error).

---

## 1. Tier Definitions

VeriBiota uses a tiered model for profiles (alignment runs, edit scripts, prime plans, Pair-HMM bridges, etc.).

### Tier 0

Profiles that:

- Have a versioned JSON schema in `schemas/`.
- Are listed in `docs/PROFILE_SPEC.md` with a stable identifier.
- Are present in `profiles/manifest.json` with schema hashes and theorem anchors.
- Have Lean theorems registered in `Biosim/VeriBiota/Theorems.lean`.
- Have a CLI checker and tests covering valid, failing, and malformed instances with exit-code assertions.

Tier 0 provides correctness and robustness guarantees for individual profile instances. It is suitable for CI gating and automated validation.

### Tier 1 (planned)

Profiles that extend Tier 0 with additional guarantees such as cross-instance invariants or stronger semantic properties (e.g., normalization invariants for VCF).

### Tier 2 (planned)

Profiles that link multiple components (pipelines, GPU kernels, distributed services) under an end-to-end specification.

---

## 2. Current Tier 0 Profiles

The current Tier 0 set is maintained in `docs/PROFILE_SPEC.md` and `profiles/manifest.json`. At the time of writing, the Tier 0 profiles include:

- `global_affine_v1` — global affine alignment scoring and traceback.
- `edit_script_v1` — basic edit script structure and application.
- `edit_script_normal_form_v1` — normal form constraints for edit scripts (merged operations, canonical ordering).
- `prime_edit_plan_v1` — prime editing plan structure, including pegRNA and nicking design planning.
- `pair_hmm_bridge_v1` — bridge between alignment-style scoring and Pair-HMM likelihoods.

---

## 3. Guarantees

For Tier 0 profiles, VeriBiota guarantees:

- **Schema correctness** — each profile has a JSON schema that defines valid instances; the CLI validates inputs before semantic checks.
- **Theorem-anchored checking** — every Tier 0 profile is anchored to theorem IDs in `Biosim/VeriBiota/Theorems.lean`, tied via `profiles/manifest.json`.
- **Deterministic exit codes**
  - `0`: success (schema + proof obligations hold)
  - `2`: checked but failed obligations
  - `1`: malformed input or internal error
- **Structured JSON output** — success and failure runs emit machine-readable JSON summaries, including error objects for malformed inputs.

---

## 4. CLI Usage

Each Tier 0 profile has a CLI route of the form:

```bash
veribiota check alignment global_affine_v1 <input.json> [--snapshot-out PATH] [--compact]
veribiota check edit edit_script_v1 <input.json> [--snapshot-out PATH] [--compact]
veribiota check edit edit_script_normal_form_v1 <input.json> [--snapshot-out PATH] [--compact]
veribiota check prime prime_edit_plan_v1 <input.json> [--snapshot-out PATH] [--compact]
veribiota check hmm pair_hmm_bridge_v1 <input.json> [--snapshot-out PATH] [--compact]
```

- `-` can be used instead of a path to read JSON from stdin.
- `--snapshot-out PATH` writes a `snapshot_signature_v1` JSON document on passed/failed runs for provenance.
- Output: JSON summary with `profile`, `profile_version`, `status`, theorem IDs, instance summary, engine metadata, and structured errors when applicable.

Example (stdin):

```bash
cat Tests/profiles/global_affine_v1/match_pass.json | jq .input \
  | ./veribiota check alignment global_affine_v1 -
```

---

## 5. Tier 0 in CI

Typical steps:

1. Install Lean + dependencies (`lake build`).
2. Run the proof/profile tests (`lake exe biosim_tests`).
3. Run profile checks over representative instances, e.g.:

```bash
./veribiota check alignment global_affine_v1 Tests/profiles/global_affine_v1/match_pass.json
./veribiota check edit edit_script_normal_form_v1 Tests/profiles/edit_script_normal_form_v1/pass_simple_normal.json
./veribiota check prime prime_edit_plan_v1 Tests/profiles/prime_edit_plan_v1/pass_simple.json
./veribiota check hmm pair_hmm_bridge_v1 Tests/profiles/pair_hmm_bridge_v1/pass_simple.json
```

Consumers can swap in their own instances while keeping the same commands and exit-code expectations.

---

## 6. Snapshot Signatures (optional for Tier 0)

For stronger provenance, VeriBiota provides `snapshot_signature_v1` to bind a verification result to hashes, schema, theorem IDs, and build metadata. The schema lives at `schemas/provenance/snapshot_signature_v1.schema.json` and is manifest-registered. Emitting snapshot signatures is optional but recommended for long-lived artifacts and audited pipelines; pass `--snapshot-out PATH` to any Tier 0 `veribiota check …` command to materialize one.

---

## 7. How to adopt Tier 0

1. **Select profiles**: choose the Tier 0 profiles matching your workload.
2. **Mirror schemas**: keep `schemas/*.schema.json` under version control for traceability.
3. **Add CI checks**: run `veribiota check …` against your canonical instances; enforce `lake exe biosim_tests`.
4. **Track signatures (optional)**: emit and archive `snapshot_signature_v1` JSON alongside results for provenance.
