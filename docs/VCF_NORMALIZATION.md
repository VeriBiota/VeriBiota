# VCF Normalization Profile (`vcf_normalization_v1`)

`vcf_normalization_v1` is a Tier 1 semantic profile that verifies VCF normalization steps: variants must remain semantically identical while being left-aligned and minimally represented.

## What it checks

- Variant preservation: canonicalized original equals canonicalized normalized (no gain/loss of truth).
- Left-alignment/minimality: no redundant shared prefix/suffix remains; locus updates reflect any prefix trimming.
- Ref/alt consistency: ref/alt remain valid after trimming.
- Idempotence: re-normalizing an already normalized variant is a fixed point.

## Schema shape (summary)

`schemas/variant/vcf_normalization_v1.schema.json`:

- `input_vcf_hash`, `normalized_vcf_hash`: content hashes (e.g., `sha256:<hex>`).
- `reference_fasta_hash` (optional).
- `variants[]` entries:
  - `locus`: `chrom`, `pos`
  - `original`: `ref`, `alt[]`
  - `normalized`: `pos`, `ref`, `alt[]`
  - `operations`: optional list like `left_trim`, `right_trim`, `left_align`, `split`, `merge`, `pad_left`, `pad_right`.
- `summary`: optional counts (trimmed/split/invalid).

## CLI usage

```bash
veribiota check vcf vcf_normalization_v1 path/to/input.json --snapshot-out sig.json --compact
```

Output: JSON verdict with `variant_count`, `normalized_ok_count`, `all_variants_normalized`, hashes, theorem IDs (`VB_VCF_001`, `VB_VCF_002`), and engine metadata.

Snapshot: `--snapshot-out` writes a `snapshot_signature_v1` document binding the input hash, schema hash, theorem IDs, and build metadata to the result.

## Example input

```json
{
  "input_vcf_hash": "sha256:aaaaaaaa...aaaaaaaa",
  "normalized_vcf_hash": "sha256:bbbbbbbb...bbbbbbbb",
  "variants": [
    {
      "locus": { "chrom": "chr1", "pos": 1 },
      "original": { "ref": "AC", "alt": ["A"] },
      "normalized": { "pos": 2, "ref": "C", "alt": [""] },
      "operations": ["left_trim"]
    }
  ]
}
```

Run:

```bash
veribiota check vcf vcf_normalization_v1 examples/vcf_norm.json --snapshot-out sig.json
```

- Verdict: `all_variants_normalized: true`, `status: "passed"`.
- Signature: `sig.json` in `snapshot_signature_v1` format for provenance.
