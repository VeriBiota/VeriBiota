# Canonicalization & Signing

VeriBiota artifacts (checks and certificates) use the **`veribiota-canon-v1`** canonicalization
scheme. This keeps hashes, signatures, and diffing stable across platforms.

## Canonicalization rules

1. **UTF-8 + LF** – JSON is encoded as UTF-8 with `\n` line endings. Output always ends with a trailing newline.
2. **Deterministic ordering** – objects are rendered with a fixed field order; arrays retain the source order but are deterministically sorted by the emitters.
3. **No extra whitespace** – pretty printing uses two-space indentation; compact mode omits insignificant whitespace but still enforces LF endings.
4. **Hash tags** – payload hashes are recorded as `sha256:<64 hex chars>` and computed after canonicalization.

Use the CLI to normalize any artifact before signing or diffing:

```bash
veribiota --canon build/artifacts/checks/sir-demo.json --out build/artifacts/checks/sir-demo.canon.json
```

## JWS construction

Signatures use Ed25519 and RFC 7515 compact serialization:

1. Header JSON:
   ```json
   {
     "alg": "EdDSA",
     "kid": "<key id>",
     "typ": "JWT",
     "veribiotaCanon": "veribiota-canon-v1"
   }
   ```
2. Canonical payload bytes (rule set above).
3. Signing input: `base64url(header) + "." + base64url(payload)`.
4. The Ed25519 signature over the signing input is base64url-encoded and appended as the third segment.

The resulting JWS is stored under `signature.jws`, alongside:

- `alg` (`Ed25519`)
- `kid`
- `issuedAt` (UTC ISO-8601)
- `payloadHash` (`sha256:<hex>`)
- `canonicalization` `{ "scheme": "veribiota-canon-v1", "newlineTerminated": true }`

## Verification contract

Consumers (CLI, engine, orchestration) must:

1. Parse JSON and extract the signature block.
2. Re-render the payload with the canonical rules.
3. Recompute the SHA256 tag and compare with `payloadHash`.
4. Verify the JWS using the `kid`-selected Ed25519 public key from the JWKS document.

Any deviation in canonicalization/JWS structure (missing newline, header mismatch, payload bytes
not matching the canonical rendering) produces exit code `4` (`canonical mismatch`). Signature
failures use exit code `2`, payload hash mismatches use exit code `3`, and missing signatures in
enforced mode use exit code `5`. For the full table (including parse/decode errors), see
[`docs/FAILURE_MODES.md`](FAILURE_MODES.md).

## Signing enforcement

The emitter refuses to sign if canonicalization metadata is missing or mismatched:

- Payload `canonicalization.scheme` must be `veribiota-canon-v1`.
- Payload must be newline-terminated (`newlineTerminated: true`) and end with a single `\n`.
- The signature header embeds `veribiotaCanon` which must match the payload scheme.
- CI preflight (`scripts/sign_preflight.sh`) validates that existing artifacts advertise the canonicalization policy before signing and that JWKS matches the configured private key.

## Determinism quick-check

```bash
make emit
cp build/artifacts/checks/sir-demo.json build/artifacts/checks.first.json
make emit
diff -u build/artifacts/checks.first.json build/artifacts/checks/sir-demo.json
```

CRLF inputs can be normalized via `veribiota --canon`, ensuring byte-for-byte
equivalence across Windows, macOS, and Linux.

## Schema links (contract v1)

- Checks schema: <https://veribiota.ai/schema/v1/checks.json> (raw: `schema/veribiota.checks.v1.json`)
- Certificate schema: <https://veribiota.ai/schema/v1/certificate.json> (raw: `schema/veribiota.certificate.v1.json`)

Artifacts conforming to these schemas are valid for all pilot contracts through **2025-Q1**.
Treat the v1 files as immutable; any future changes will ship under `/schema/v2/…` with a new tag.
