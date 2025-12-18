# Getting Started

This guide walks through building the toolchain, emitting artifacts, signing locally, and verifying outputs.

## Prerequisites
- Lean toolchain via `elan`
- Lake build system
- Python 3 (for CI utilities) and `jq`
- OpenSSL 3 if you’re on macOS (Homebrew’s `openssl@3`)

## Build the project
```bash
elan toolchain install $(cat lean-toolchain)
lake update && lake build
./veribiota --help
```

## Emit a complete demo bundle
```bash
./veribiota --emit-all --out build/artifacts
# Writes:
#   build/artifacts/models/sir-demo.json
#   build/artifacts/certificates/sir-demo.json (+ .sha256)
#   build/artifacts/checks/sir-demo.json (+ .sha256)
```

## Local signing quickstart
Generate a disposable key, derive a matching JWKS, and run a full signed round‑trip.

```bash
# Generate an Ed25519 private key
openssl genpkey -algorithm ed25519 -out security/local-signing.key

# Configure signing environment
export VERIBIOTA_SIG_MODE=signed-soft
export VERIBIOTA_SIG_KEY="$PWD/security/local-signing.key"
export VERIBIOTA_SIG_KID="local-test"

# Derive JWKS from the private key
X="$(
  openssl pkey -in "$VERIBIOTA_SIG_KEY" -pubout -outform DER \
  | tail -c 32 \
  | python3 -c 'import sys,base64;print(base64.urlsafe_b64encode(sys.stdin.buffer.read()).decode().rstrip("="))'
)"
jq -n --arg x "$X" --arg kid "$VERIBIOTA_SIG_KID" \
  '{keys:[{kty:"OKP",crv:"Ed25519",kid:$kid,x:$x}]}' > security/jwks.json

# Emit + sign artifacts
make sign-soft
```

macOS: Apple’s built‑in LibreSSL lacks Ed25519. Install Homebrew’s OpenSSL 3 and set `VERIBIOTA_OPENSSL`:
```bash
export VERIBIOTA_OPENSSL="$(brew --prefix openssl@3)/bin/openssl"
```

## Verify artifacts
```bash
./veribiota verify checks build/artifacts/checks/sir-demo.json \
  --jwks security/jwks.json --print-details
./veribiota verify cert   build/artifacts/certificates/sir-demo.json \
  --jwks security/jwks.json --print-details
```

## Import an external model
```bash
./veribiota import --in Biosim/Examples/Model/sir.model.json \
  --emit-all --out build/artifacts
```

## Next steps

- Learn the full Verification Workflow (docs/verification-workflow.md).
- Check the CLI & adapter reference (docs/cli.md).
- If your project emits edit DAGs, target the normalized schema
  `veribiota.edit_dag.v1` (docs/schema/edit_dag.md) and wire CI to the
  reusable GitHub Action:
  ```yaml
  - name: Run VeriBiota DAG checks
    uses: OmnisGenomics/VeriBiota/.github/actions/veribiota-check@v1
    with:
      project-name: MySim
      dag-glob: veribiota_work/*.dag.json
      veribiota-ref: v0.1.0
  ```
  For a concrete starting point, see the template layout under
  `examples/veribiota-example-project` in this repository.
