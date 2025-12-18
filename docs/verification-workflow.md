# Verification Workflow

A model’s journey from JSON to verified, signed artifacts, runtime checks,
and (optionally) EditDAG verification.

## 1) Author or import the model
Start from your model JSON or import an example:
```bash
./veribiota import --in Biosim/Examples/Model/sir.model.json \
  --emit-all --out build/artifacts
```
This produces canonicalized model JSON plus a proof‑backed certificate and invariant checks.

## 2) Canonicalize for determinism
Enforce LF endings, stable ordering, and trailing newline for byte‑for‑byte equality:
```bash
./veribiota --canon build/artifacts/checks/sir-demo.json \
  --out build/artifacts/checks/sir-demo.json
```

## 3) Sign with Ed25519 (JWKS)
Attach authenticity and provenance using Ed25519 and JWKS:
```bash
export VERIBIOTA_SIG_MODE=signed-soft
export VERIBIOTA_SIG_KEY=/path/to/ed25519.pem
export VERIBIOTA_SIG_KID=your-key-id
make sign-soft
```
The signature block records `kid`, `issuedAt`, `payloadHash` (SHA‑256), and canonicalization settings.

Preflight checks (CI/local):
- `scripts/sign_preflight.sh` verifies JWKS matches the private key and that artifacts advertise `canonicalization: { scheme: "veribiota-canon-v1", newlineTerminated: true }`.
- Signing is refused if canonicalization mismatches or header/payload metadata diverge.

## 4) Verify certificates and checks
Consumers verify both canonicalization and signature:
```bash
./veribiota verify checks build/artifacts/checks/sir-demo.json \
  --jwks security/jwks.json --print-details
./veribiota verify cert   build/artifacts/certificates/sir-demo.json \
  --jwks security/jwks.json --print-details
```
Exit codes differentiate canonical mismatch, signature failure, and enforcement gaps. See Canonicalization & Signing (docs/canonicalization.md).

## 5) Verify simulation results
Runtime engines evaluate invariant drift and positivity against the signed checks JSON:
```bash
./veribiota verify results build/artifacts/checks/sir-demo.json results.jsonl
```

## 6) EditDAG verification tiers

For tools that emit edit DAGs (e.g., CRISPR/prime editing workflows), VeriBiota
provides a small, shared JSON schema plus a Python adapter and Lean entrypoint.

- **Tier 0 – raw JSON**:
  - Emit DAG JSON but skip structural checks entirely. Useful only during early
    prototyping; not recommended for CI or “Verified by VeriBiota” claims.
- **Tier 1 – JSON-only checks**:
  - Schema: `schema/veribiota.edit_dag.v1.json`.
  - Install the adapter: `python -m pip install .`
  - Run: `veribiota check-json --input 'veribiota_work/*.dag.json'`
  - Validates DAGs against the schema plus structural invariants:
    acyclicity, unique root at depth 0, depth monotonicity, and probability
    conservation on fanout and leaves. No Lean or Lake required.
- **Tier 2 – JSON + Lean checks**:
  - Generate a Lean suite from DAG JSON:
    ```bash
    veribiota generate-suite \
      --input 'veribiota_work/*.dag.json' \
      --project MySim \
      --suite DAGs
    lake build
    lake exe veribiota-check
    ```
  - This ensures the generated `EditDAG` values type-check inside the
    `Biosim.VeriBiota` library and are visible to Lean-level proofs.
- **Reusable GitHub Action**:
  - Any project can add:
    ```yaml
    - name: Run VeriBiota DAG checks
      uses: OmnisGenomics/VeriBiota/.github/actions/veribiota-check@v1
      with:
        project-name: MySim
        dag-glob: veribiota_work/*.dag.json
        veribiota-ref: v0.1.0
    ```
  - The action clones VeriBiota, installs Lean + the adapter, runs JSON-only
    checks, generates the Lean suite, and executes `lake exe veribiota-check`.

These tiers let consumers start at Tier 0 (chaos), add fast JSON sanity at Tier
1, and graduate to full “Verified by VeriBiota” Lean-backed checks at Tier 2,
without touching any Lean theory in their own repositories.

## Provenance chain
```
model.json → certificate.json → checks.json → signature → JWKS
```

Treat schemas under `schema/` as immutable for a given major version. All artifacts carry their `scheme` and canonicalization policy explicitly.

## Minisign sidecars (optional)
For Unix‑friendly detached signatures, you can create `*.minisig` files that sign the same canonical bytes used for JWS.

```bash
# Sign (assumes VERIBIOTA_MINISIGN_SEC points to your .key)
make minisign

# Verify (assumes VERIBIOTA_MINISIGN_PUB points to your .pub)
make verify-minisign
```

Notes: canonicalize before signing (the helper does this automatically), never commit keys, and keep this optional on Windows. See the “Minisign sidecars (optional)” section in the repository README for details.
