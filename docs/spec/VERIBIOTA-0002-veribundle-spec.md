# VERIBIOTA-0002 — VeriBundle & Claim Graph v0.1 (Draft)

**Status:** Draft  \
**Bundle target:** `bundle_version: 0.1`  \
**Purpose:** Define the verification substrate (VeriBundle, claims, evidence, signing, runner surface) so any engine can emit and check proof-backed biology artifacts (where proofs exist) with deterministic schemas and attestable outputs.

## 1) Scope
### 1.1 What VeriBiota is
A verification substrate that accepts a **Subject** (biological artifact) + **Provenance** + **Claims** (invariants) and produces a **Verdict** with **Evidence** (proofs/certs/stats) and **Witnesses** (counterexamples).

### 1.2 What this spec defines
- Core objects: `VeriBundle`, `Claim`, `Evidence`, `Witness`, `Profile`, `Certificate`.
- Canonical hashing and signing rules (content-addressed, composable).
- Minimal IR (Intermediate Representation) modules for catch-all coverage.
- Runner API surface (CLI + HTTP) and checker plugin interface.
- Privacy tiers (public vs. private evidence).

### 1.3 Non-goals (v0.1)
- Proving correctness of all numerics/statistics engines (we label them).
- Defining “one true biology ontology.”
- Replacing existing file formats (VCF/CRAM/etc.); we wrap and reference them.

## 2) Conventions
- **MUST / SHOULD / MAY** are normative.
- **Artifact** refers to any data object: file, graph, model, pipeline run, etc.
- **Canonical** means deterministic encoding for hashing and signing.

## 3) Core data model
### 3.1 IDs and naming
- Claim IDs: `vb.<domain>.<topic>.<name>` (example: `vb.genome.cds.frame_preserved`).
- Assumption IDs: `vb.assumption.<name>` (example: `vb.assumption.reference_build=GRCh38`).
- Profiles: `vb.profile.<name>@<semver>` (example: `vb.profile.clinical_strict@0.1.0`).

### 3.2 Hashes (content addressing)
Digest shape:

```
{ "alg": "sha256", "hex": "..." }
```

Rules:
- v0.1 MUST support `sha256`.
- Any referenced blob/file MUST have a digest.

### 3.3 Attachments (blobs)

```
{
  "name": "optional human name",
  "media_type": "application/cbor|application/json|text/plain|application/octet-stream",
  "digest": { "alg": "sha256", "hex": "..." },
  "size_bytes": 12345,
  "inline_base64": "OPTIONAL (small only)",
  "uri": "OPTIONAL (content-addressed store, s3, ipfs, etc)",
  "privacy": "public|restricted|secret"
}
```

Rules:
- `inline_base64` SHOULD be used only for small payloads (<256 KB).
- `privacy` MUST be present.

## 4) VeriBundle (the one thing everything emits)
### 4.1 Structure
VeriBundle is the signed/unsigned container describing Subject, Provenance, Claims, Attachments, optional signatures, and optional IR pointers.

Minimal conceptual schema:

```
{
  "bundle_version": "0.1",
  "subject": { ...SubjectRef... },
  "provenance": { ... },
  "ir": { ...optional IR pointers... },

  "assumption_defs": [
    { "id": "vb.assumption.reference_build=GRCh38", "text": "..." }
  ],

  "claims": [ ...ClaimResult... ],

  "summary": {
    "overall_result": "pass|fail|inconclusive",
    "highest_severity_failed": "blocker|warning|info|none",
    "profile": { "id": "vb.profile....", "digest": {..} }
  },

  "attachments": [ ...Attachment... ],

  "tcb": [ ...TrustedComponent... ],

  "signatures": [ ...optional... ]
}
```

### 4.2 SubjectRef
Represents the verified object:

```
{
  "kind": "Sequence|VariantSet|EditPlan|Network|PipelineRun|File",
  "format": "vcf|cram|fasta|gtf|sbml|veribiota.ir.sequence.v0.1|...",
  "digest": { "alg": "sha256", "hex": "..." },
  "uri": "OPTIONAL",
  "label": "OPTIONAL human label"
}
```

### 4.3 Provenance
Provenance must pin reproducibility-critical info:

```
{
  "inputs": [ { "name": "reads.cram", "digest": {...}, "uri": "...", "role": "reads" } ],
  "references": [ { "name": "GRCh38", "digest": {...}, "role": "reference" } ],
  "annotations": [ { "name": "gencode.v44", "digest": {...}, "role": "transcripts" } ],
  "software": [
    { "name": "ogn", "version": "x.y.z", "container_digest": {..}, "git_commit": "..." }
  ],
  "parameters": { "aligner": "bwa", "min_mapq": 30 },
  "timestamp_utc": "2025-12-05T00:00:00Z"
}
```

Rules:
- If a reference/annotation affects coordinates or semantics, it MUST be included with a digest.
- If results depend on a container, `container_digest` MUST be present.

### 4.4 Trusted Computing Base (TCB)

```
{
  "name": "veribiota-runner",
  "version": "0.1.3",
  "digest": { "alg": "sha256", "hex": "..." },
  "mode": "proof_checked|replayable|trusted_computation|statistical"
}
```

Rules:
- Every `ClaimResult` must imply a TCB mode (via its Evidence).

## 5) Claims, Evidence, Witnesses
### 5.1 ClaimResult

```
{
  "id": "vb.genome.cds.frame_preserved",
  "title": "CDS frame is preserved",
  "scope": { "transcript": "ENST0000...", "region": "chr7:...-..." },
  "severity": "blocker|warning|info",

  "assumptions": ["vb.assumption.reference_build=GRCh38"],

  "result": "pass|fail|inconclusive",
  "reason": "short human-readable explanation",

  "evidence": [ ...EvidenceRef... ],
  "witness":  { ...WitnessRef... },

  "metrics": { "optional": "numbers for dashboards" }
}
```

### 5.2 EvidenceRef (typed)

```
{
  "type": "lean_proof|replay_trace|stat_test|report|attestation",
  "tcb_mode": "proof_checked|replayable|trusted_computation|statistical|human",
  "attachment_digest": { "alg": "sha256", "hex": "..." },
  "summary": { "optional structured fields depending on type" }
}
```

Evidence type conventions:
- `lean_proof`: attachment contains a proof term or proof artifact; verifier must check it.
- `replay_trace`: attachment contains deterministic steps and hashes to replay.
- `stat_test`: attachment contains test name, parameters, p-value/bounds, and model assumptions.
- `report`: human-readable detail (still content-addressed).
- `attestation`: signed statement by a human/system (rare; explicit).

### 5.3 WitnessRef (counterexample)

```
{
  "type": "counterexample|minimal_case|data_pointer",
  "attachment_digest": { "alg": "sha256", "hex": "..." },
  "hint": "e.g., variant at chr7:117199644 breaks splice donor motif"
}
```

Rules:
- On `fail`, a witness SHOULD be present.
- Witness SHOULD be the “smallest useful” payload: positions, read subset hashes, transcript, violation score.

### 5.4 Result semantics
- `pass`: claim holds under listed assumptions within the evidence model.
- `fail`: claim violated; witness showed it.
- `inconclusive`: cannot evaluate; MUST include reasons (missing input, wrong ref, insufficient coverage, unsupported format).

## 6) IR modules (minimal, not bloated)
IR exists so checkers do not have to parse many formats. In v0.1 IR is optional but strongly recommended.

### 6.1 SequenceIR v0.1

Concepts:
- Contigs with names, lengths, and digest of bases (or reference pointer).
- Optional embedded sequence slices (small only).
- Features: genes/transcripts/exons/CDS segments with reading frame info.

Key objects:

```
{
  "ir_kind": "veribiota.ir.sequence@0.1",
  "reference": { ...SubjectRef... },
  "contigs": [ {"name":"chr1","length":248956422} ],
  "features": [
    {"type":"transcript","id":"ENST...","contig":"chr7","strand":"+",
     "exons":[{"start":...,"end":...}], "cds":[{"start":...,"end":...,"phase":0}]}
  ]
}
```

### 6.2 VariantIR v0.1

Principles:
- Must be normalized (left-aligned, parsimonious) relative to a pinned reference.
- Must carry genotypes and evidence summaries (not necessarily full reads).

Key objects:

```
{
  "ir_kind": "veribiota.ir.variant@0.1",
  "reference": { ...SubjectRef... },
  "variants": [
    {"contig":"chr7","pos":117199644,"ref":"G","alt":"A",
     "genotypes":[{"sample":"S1","gt":"0/1","gq":99,"dp":42,"ad":[21,21]}]}
  ]
}
```

### 6.3 EditIR v0.1
Edits are patches on a reference coordinate system:

```
{
  "ir_kind": "veribiota.ir.edit@0.1",
  "reference": { ...SubjectRef... },
  "operations": [
    {"op":"sub","contig":"chr7","pos":117199644,"ref":"G","alt":"A"}
  ],
  "intent": { "type":"knockout|repair|tag|unknown", "target":"GENE1" }
}
```

### 6.4 NetworkIR v0.1 (for Helix dynamics)

```
{
  "ir_kind": "veribiota.ir.network@0.1",
  "species": [{"id":"A","initial":10.0}],
  "reactions": [{"id":"R1","reactants":{"A":1},"products":{"B":1},"rate_law":"k*A","params":{"k":0.1}}]
}
```

### 6.5 PipelineIR v0.1 (OGN + others)
A pinned DAG:

```
{
  "ir_kind": "veribiota.ir.pipeline@0.1",
  "nodes": [
    {"id":"align","tool":"bwa","container_digest":{...},"params":{...},"inputs":["reads"],"outputs":["bam"]}
  ],
  "edges": [{"from":"align","to":"call"}]
}
```

## 7) Profiles & Policies (how intent becomes enforceable)
### 7.1 Profile

```
{
  "profile_id": "vb.profile.clinical_strict@0.1.0",
  "description": "Strict verification for clinical-like reporting",
  "required_claims": [
    {"id":"vb.pipeline.reference_consistency", "severity":"blocker"},
    {"id":"vb.variant.normalized", "severity":"blocker"},
    {"id":"vb.variant.read_support_consistent", "severity":"blocker",
     "params":{"min_dp":20,"max_alt_bias_p":1e-6}}
  ],
  "optional_claims": [
    {"id":"vb.population.hwe_sanity", "severity":"warning", "params":{"min_n":200}}
  ],
  "policy": {
    "blocker_fail": "overall_fail",
    "warning_fail": "overall_pass_with_warnings",
    "inconclusive": "overall_inconclusive"
  }
}
```

### 7.2 Policy rules
- Profiles MUST define how severities aggregate into `summary.overall_result`.
- Profiles SHOULD be content-addressed and pinned in `VeriBundle.summary.profile`.

## 8) Certificates and signing
### 8.1 What gets signed
v0.1 strongly recommends signing the entire canonical VeriBundle (including claim results and attachment digests).

### 8.2 Canonicalization rule
To avoid JSON canonicalization pain, v0.1 SHOULD use CBOR encoding of the bundle for hashing and signing (deterministic field ordering and stable encoding). JSON MAY be used as a transport/debug view, but hashes must be computed over the canonical CBOR.

### 8.3 VeriCert (envelope)

```
{
  "cert_version": "0.1",
  "bundle_digest": {"alg":"sha256","hex":"..."},
  "signer": {"key_id":"org.veribiota.prod.2025-01", "alg":"ed25519"},
  "signature": "base64...",
  "bundle_payload_cbor_base64": "OPTIONAL but recommended"
}
```

Rules:
- Certificates MUST include `bundle_digest`.
- If a certificate omits payload, verifier must fetch bundle by digest.

## 9) Minimal Runner API surface
### 9.1 CLI (required)
- `veribiota verify --profile <profile.json|id> --bundle <bundle.json|cbor> --out <bundle.vb.cbor>` → produces augmented bundle (adds claim results, evidence refs, summary, TCB).
- `veribiota sign --key <key> --bundle <bundle.vb.cbor> --out <cert.vbc>`.
- `veribiota check --cert <cert.vbc> [--policy strict]` → verifies signature, bundle digest, claim graph integrity, profile compliance.
- `veribiota explain --bundle <...> --claim <id>` → prints reasoning tree and witness pointers.

### 9.2 HTTP API (recommended)
- `POST /v0.1/verify` → input: bundle + profile; output: augmented bundle.
- `POST /v0.1/sign` → input: augmented bundle; output: cert.
- `POST /v0.1/check` → input: cert; output: verdict + failures + missing attachments.
- `GET /v0.1/claims` → lists supported claim IDs + parameters.
- `GET /v0.1/profiles/<id>` → returns profile definition (pinned).

## 10) Checker plugin interface (library contract)
A checker implements claim definitions, input requirements, and evaluation that emits deterministic `ClaimResult` objects.

Pseudo-interface:

```
trait Checker {
  fn supported_claims() -> [ClaimDef];
  fn required_inputs(claim_id) -> [InputRequirement];
  fn evaluate(ctx: EvalContext, claim: ClaimRequest) -> ClaimResult;
}
```

`EvalContext` provides IR resolvers (parse/convert VCF/CRAM/FASTA → IR), reference resolver by digest, attachment store (write blobs, returns digest), and deterministic runtime config (threads, seeds, container digests).

Rules:
- Checkers MUST be deterministic given the same inputs and params (or declare nondeterminism and mark evidence as non-replayable).
- Every checker output MUST set `tcb_mode` per evidence item.

## 11) Adapters (how it becomes catch-all)
Adapters are thin transforms:
- `vcf + reference -> VariantIR`
- `fasta + gtf -> SequenceIR`
- `edit_plan -> EditIR`
- `sbml/helix -> NetworkIR`
- `nextflow/snakemake/wdl + logs -> PipelineIR`

Adapter outputs MUST be content-addressed and appear in `bundle.ir` as `SubjectRef` entries to IR blobs. Example:

```
"ir": {
  "sequence_ir": {"kind":"File","format":"veribiota.ir.sequence@0.1","digest":{...}},
  "variant_ir":  {"kind":"File","format":"veribiota.ir.variant@0.1","digest":{...}}
}
```

## 12) Privacy & redaction tiers
Three tiers:
- `public`: safe to share broadly (no read-level data, no PHI).
- `restricted`: internal-only (may include sensitive metrics).
- `secret`: raw evidence (read subsets, private annotations, etc.).

Rules:
- Bundles SHOULD default to public evidence unless you explicitly opt in.
- Claims SHOULD degrade to `inconclusive` rather than forcing secret data into a public cert.
- Runner SHOULD support `--redaction public|restricted|secret` to control emitted attachments.

## 13) Compatibility & versioning
- `bundle_version` uses a semver-ish string; v0.1 readers MUST reject unknown major versions.
- Claim IDs are stable; claim semantics may evolve only with explicit versioned IDs or parameter changes recorded in evidence.

## Appendix A: Example minimal bundle (single claim)

```
{
  "bundle_version": "0.1",
  "subject": {
    "kind": "VariantSet",
    "format": "vcf",
    "digest": {"alg":"sha256","hex":"aaa..."}
  },
  "provenance": {
    "inputs": [{"name":"sample.cram","digest":{"alg":"sha256","hex":"bbb..."},"role":"reads"}],
    "references":[{"name":"GRCh38","digest":{"alg":"sha256","hex":"ccc..."},"role":"reference"}],
    "software":[{"name":"ogn","version":"1.2.3","container_digest":{"alg":"sha256","hex":"ddd..."}}],
    "parameters":{"min_mapq":30},
    "timestamp_utc":"2025-12-05T00:00:00Z"
  },
  "assumption_defs":[
    {"id":"vb.assumption.reference_build=GRCh38","text":"All coordinates are interpreted in GRCh38."}
  ],
  "claims":[
    {
      "id":"vb.variant.normalized",
      "title":"Variants are normalized vs reference",
      "scope":{"cohort":"sample"},
      "severity":"blocker",
      "assumptions":["vb.assumption.reference_build=GRCh38"],
      "result":"pass",
      "reason":"All variants left-aligned and parsimonious",
      "evidence":[
        {"type":"replay_trace","tcb_mode":"replayable","attachment_digest":{"alg":"sha256","hex":"eee..."},
         "summary":{"normalizer":"veribiota-norm@0.1","count":12345}}
      ]
    }
  ],
  "summary":{
    "overall_result":"pass",
    "highest_severity_failed":"none",
    "profile":{"id":"vb.profile.research_default@0.1.0","digest":{"alg":"sha256","hex":"fff..."}}
  },
  "attachments":[
    {"name":"norm-trace","media_type":"application/cbor","digest":{"alg":"sha256","hex":"eee..."},"size_bytes":9000,"privacy":"public"}
  ],
  "tcb":[
    {"name":"veribiota-runner","version":"0.1.0","digest":{"alg":"sha256","hex":"111..."},"mode":"replayable"}
  ]
}
```

## Appendix B: “Flagship claim packs” to define first (recommended)
- **Genomics structure (hard-ish):** `vb.variant.normalized`, `vb.pipeline.reference_consistency`, `vb.genome.cds.frame_preserved`, `vb.genome.no_premature_stop`, `vb.genome.splice_site_integrity` (score-based but with explicit model).
- **Variant sanity (soft/stat):** `vb.variant.read_support_consistent`, `vb.sample.contamination_below_threshold`, `vb.qc.coverage_sufficient`.
- **Simulation sanity (hard):** `vb.dynamics.non_negative_state`, `vb.dynamics.mass_conserved` (when applicable).
