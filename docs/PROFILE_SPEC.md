# VeriBiota Profile Catalog v0.1 – Spec

This catalog defines what VeriBiota profiles judge across the stack. Profiles are grouped by implementation tier.

| Profile                      | Status       | Domain        | Consumers          |
|------------------------------|--------------|---------------|--------------------|
| global_affine_v1             | Implemented  | alignment     | OGN, Helix         |
| edit_script_v1               | Implemented  | edit          | Helix, OGN         |
| edit_script_normal_form_v1   | Planned      | edit          | Helix              |
| prime_edit_plan_v1           | Planned      | CRISPR/Prime  | Helix              |
| pair_hmm_bridge_v1           | Planned      | HMM/variant   | OGN                |
| read_set_conservation_v1     | Planned      | pipeline      | OGN                |
| vcf_normalization_v1         | Tier 1 (in progress) | variant       | OGN, external      |
| offtarget_score_sanity_v1    | Future       | CRISPR        | Helix              |
| snapshot_signature_v1        | Future       | provenance    | Helix, VeriBiota   |

## Conventions

- Profile name: `snake_case_vN` (e.g., `global_affine_v1`).
- JSON schema: `schemas/<domain>/<profile>.schema.json`.
- Golden fixtures: `Tests/profiles/<profile>/*.json`.
- Manifest: `profiles/manifest.json` maps profile name → schema hash, theorem IDs.
- Verdict JSON shape:

```json
{
  "profile": "<name>",
  "profile_version": "X.Y.Z",
  "status": "passed | failed",
  "theorems": ["VB_..."],
  "instance": { "...summary..." },
  "engine": {
    "veribiota_version": "...",
    "lean_version": "...",
    "build_id": "..."
  }
}
```

- Exit codes: `0` profile holds (passed); `2` profile checked but failed; `1` malformed input or internal error.

## Tier 0 – Implemented Profiles

### 1. global_affine_v1 (Status: Implemented, contract locked)

- **Purpose**: Guarantee that an implementation’s global affine alignment result matches the formal DP specification and trace semantics.
- **Intended consumers**: OGN core aligner (CPU, GPU); any external tool claiming “VeriBiota-verified global alignment”.
- **Inputs (conceptual)**: `seqA`, `seqB` strings; `scoring` { `match`, `mismatch`, `gap_open`, `gap_extend` }; `witness` with `score` (int) and `trace` list of steps `{ op: "M" | "I" | "D" }`.
- **Verified properties**:
  - Trace validity: path from (0,0) to (|A|,|B|); no out-of-bounds or illegal transitions.
  - Score consistency: `traceScore(seqA, seqB, scoring, trace) = witness.score`.
  - DP optimality/equivalence: DP recurrence satisfied; `dpScore(seqA, seqB, scoring) = specGlobalAffine(seqA, seqB, scoring) = witness.score`.
  - Instance summary: verdict includes `seqA_length`, `seqB_length`, `trace_length`.
- **Theorem anchors**: `VB_ALIGN_CORE_001` (DP equals spec score); `VB_ALIGN_CORE_002` (trace from DP achieves `dpScore`).

### 2. edit_script_v1 (Status: Implemented, contract locked)

- **Purpose**: Guarantee that a claimed edit script coherently transforms `seqA` into `seqB`.
- **Intended consumers**: Helix edit planner; any tool generating explicit edit scripts (CRISPR, Prime, patching).
- **Inputs (conceptual)**: `seqA`, `seqB`; `edits` list of `{ type: "ins" | "del" | "sub", pos: int, len: int (for del/sub), payload: str (for ins/sub) }`.
- **Verified properties**:
  - Well-defined application: edits apply sequentially without index under/overflow; positions and lengths respect current string state.
  - Final result equality: applying edits left-to-right yields exactly `seqB`.
  - Basic coherence: no degenerate no-op edits (unless later normalized); no overlapping ambiguous edits.
- **Instance summary**: `seqA_length`, `seqB_length`, `edit_count`, and `applied_ok` boolean.
- **Theorem anchors**: `VB_EDIT_001` – edit script application is total and well-defined; future `VB_EDIT_002` – normalization theorem.

## Tier 1 – Next Profiles To Implement

### 3. edit_script_normal_form_v1 (Status: Planned, high priority)

- **Purpose**: Provide a canonical normalized form so different tools agree on “the same edit”.
- **Intended consumers**: Helix planner; any diff/patch layer in OGN; future audit/tracking.
- **Inputs**: `seqA`, `seqB`; `edits` arbitrary script; optionally `normalized_edits` claimed normal form.
- **Verified properties**:
  - Normalization correctness: `applyEdits(seqA, edits) = applyEdits(seqA, normalized_edits) = seqB`.
  - Normal form invariants: no adjacent merges possible; minimal representation under chosen ordering (e.g., leftmost, shortest); no redundant `sub` that is a match.
  - Idempotence: re-normalizing `normalized_edits` yields the same script.
- **Theorem anchors (planned)**: `VB_EDIT_002` – normalization preserves semantics and is idempotent.

### 4. prime_edit_plan_v1 (Status: Planned, high priority for Helix)

- **Purpose**: Verify that a Prime Editing plan (guide, RT template, nicking strategy) corresponds to a desired net edit script.
- **Intended consumers**: Helix prime editor module (simulated); future recommendations, constraints, AI models.
- **Inputs (conceptual)**:
  - `ref_seq`: reference context window.
  - `target_seq`: intended edited sequence (local window).
  - `plan`: pegRNA fields (spacer, PAM, RT template, PBS), optional nicking guide, cut positions, `net_edit_script` (reuse edit script schema) from `ref_seq` to `target_seq`.
- **Verified properties**:
  - Plan-to-edit linkage: `net_edit_script` encodes exactly the delta between `ref_seq` and `target_seq`; sites of change align with RT template design.
  - Internal consistency: PBS and RT lengths within allowed bounds; PAM positions consistent with spacer location.
  - Relationship to `edit_script_v1`: calls `edit_script_v1` on (`ref_seq`, `target_seq`, `net_edit_script`).
- **Theorem anchors (planned)**: `VB_PE_001` – prime plan’s net edit script equals delta between reference and target; `VB_EDIT_001` reused for base script correctness.

### 5. pair_hmm_bridge_v1 (Status: Planned, high priority for OGN)

- **Purpose**: Tie DP-based alignment scoring to Pair-HMM likelihood scoring under a specified parameter mapping (small instances).
- **Intended consumers**: OGN variant calling stack; any HMM-based likelihood computation referencing DP.
- **Inputs**: `seqA`, `seqB`; `dp_scoring` match/mismatch/gap penalties; `hmm_params` transition and emission probabilities (log space); `dp_witness` DP score (optional trace); `hmm_witness` log-likelihood or Viterbi score.
- **Verified properties**:
  - Parameter mapping correctness: DP gap open/extend and mismatch penalties correspond to log transition/emission probabilities via the mapping.
  - Score equivalence within tolerance: for finite sequences, `dp_score` equals (or within rounding epsilon of) `hmm_score` under the mapping.
  - Structural equivalence (optional): Viterbi path encoded by HMM corresponds to a valid DP alignment path.
- **Theorem anchors (planned)**: `VB_HMM_001` – mapping lemma (DP parameters ↔ HMM parameters); `VB_HMM_002` – small-instance equivalence theorem.

### 6. read_set_conservation_v1 (Status: Planned, high priority pipeline invariant)

- **Purpose**: Verify that a pipeline stage conserves the multiset of reads and sample labels modulo defined operations (e.g., marking duplicates, sorting).
- **Intended consumers**: OGN end-to-end pipeline; any ETL/transform stage in the stack.
- **Inputs**: `input_summary` (read count, sample IDs, checksums per-sample/lane, optional k-mer sketch); `output_summary` same structure; `allowed_ops` flags (e.g., sort, tag, mark-dup).
- **Verified properties**:
  - Count and identity preservation: for non-dropping stages, total counts match; sample IDs preserved without cross-sample mixing.
  - Checksum or sketch consistency: aggregate hashes or sketches consistent with allowed operations; if dropping low-quality reads, the allowed pattern is codified.
- **Theorem anchors (planned)**: `VB_PIPE_001` – multiset preservation under pure reordering; `VB_PIPE_002` – constrained drop rules.

### 7. vcf_normalization_v1 (Status: Tier 1 – semantic)

- **Purpose**: Guarantee that VCF entries are normalized (left-aligned, minimal representation) without changing variant meaning.
- **Inputs**: hashes/IDs of pre- and post-normalization VCFs; optional reference FASTA hash; per-variant records describing original vs normalized locus/ref/alt and operations applied.
- **Verified properties**:
  - Variant preservation: canonicalized original equals canonicalized normalized (no gain/loss of variants).
  - Left-alignment/minimality: normalized record matches canonical form (no shared prefix/suffix remains).
  - Ref/alt consistency: ref/alt remain valid after trimming and stay aligned to the reference context.
  - Idempotence: re-normalizing an already normalized variant yields the same variant.
- **Theorem anchors (Tier 1)**: `VB_VCF_001` – normalization preserves semantics; `VB_VCF_002` – normalization is idempotent/unique in window.

## Tier 2 – Future Profiles (Defined for alignment now)

### 8. offtarget_score_sanity_v1

- **Purpose**: Sanity-check off-target scoring fields (CRISPR/Prime design) for monotonicity and boundedness.
- **Inputs**: `sites` list with mismatch counts, distances to genomic landmarks, reported scores/probabilities.
- **Verified properties**:
  - Monotonicity: more mismatches must not yield higher risk scores than strictly fewer mismatches in the same context.
  - Bounded probabilities: probabilities sum to at most 1 across mutually exclusive outcomes.
  - Basic consistency: no NaNs, infinities, or out-of-range values.
- **Theorem anchors (planned)**: `VB_OFF_001` – monotonicity lemma over discrete mismatch counts.

### 9. snapshot_signature_v1 (Helix/VeriBiota artifact integrity)

- **Purpose**: Verify that a Helix/VeriBiota snapshot artifact (EVS, edit plan, etc.) is structurally sound and correctly signed/hash-linked.
- **Inputs**: `snapshot_json` artifact; `signature_block` (hash, optional signature, theorem IDs, version).
- **Verified properties**:
  - Schema correctness: snapshot conforms to its EVS or plan schema.
  - Hash integrity: embedded hash corresponds to the JSON content in a canonical representation.
  - Proof linkage: snapshot declares the VeriBiota theorems or profiles it depends on, matching manifest versions.
- **Theorem anchors (planned)**: `VB_SIG_001` – hash correctness and reproducibility on canonical form.

## How to Use This Spec

- Treat this file as the jurisdiction for what VeriBiota is allowed to verify.
- Wire Tier 0 profiles wherever needed; implement Tier 1 next; keep Tier 2 visible to guide design choices.
- Manifest (`profiles/manifest.json`), schemas (`schemas/...`), and golden fixtures (`Tests/profiles/...`) should stay in sync with these definitions.
