# What Happens When Things Fail

VeriBiota is designed for automation: commands return **stable exit codes** and (for profile checks) **machine-readable JSON** on stdout.

## Exit codes: `veribiota check …` (profile runner)

For Tier 0 profile checks (e.g. `global_affine_v1`), the contract is:

| Meaning | Exit code | `status` field |
|---|---:|---|
| Passed | `0` | `"passed"` |
| Failed a check (invariant/contract violation) | `2` | `"failed"` |
| Error (input decode, runtime exception, internal error, snapshot emission failed) | `1` | `"error"` |

Notes:

- On **parse/decode errors**, the runner prints a JSON payload with `"status":"error"` and exits `1`.
- On **normal success/failure**, the runner prints a JSON payload with `"status":"passed"` or `"status":"failed"` and exits `0` or `2`.
- If `--snapshot-out` is set and snapshot emission fails, the runner prints the verdict JSON and then prints `Snapshot signature failed: …` to stderr and exits `1`.

Practical examples:

- Wrong input shape (missing/invalid fields) → `"status":"error"`, exit `1`.
- Valid input, but witness does not match the spec → `"status":"failed"`, exit `2`.
- Snapshot emission fails (missing manifest, write failure, etc.) → stderr contains `Snapshot signature failed: …`, exit `1`.

## Exit codes: `veribiota verify (checks|cert) …` (signature integrity)

This command has explicit error codes for signature/canonicalization integrity failures:

| Meaning | Exit code |
|---|---:|
| OK | `0` |
| Parse or decode error | `1` |
| Invalid signature | `2` |
| Payload hash mismatch | `3` |
| Canonicalization mismatch | `4` |
| Missing signature when signature mode requires it | `5` |

Practical examples:

- Using the wrong JWKS (missing `kid` or wrong public key) → invalid signature, exit `2`.
- Tampering with the JSON payload without updating `signature.payloadHash` → hash mismatch, exit `3`.
- Producing a JWS over non-canonical payload bytes (wrong canonicalization scheme / header mismatch) → canonical mismatch, exit `4`.
- Verifying in a signed mode when the artifact has no `signature` block → missing signature, exit `5`.

## CI branching (recommended)

- `0` → success
- `2` → deterministic “checked and failed” (profile violation) or “signature invalid” depending on command
- `1` → malformed input or tool/runtime error
- `3` / `4` → deterministic tamper evidence (hash/canonicalization)
- `5` → missing required signature

