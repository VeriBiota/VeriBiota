# 🧬 VeriBiota™  
**Mathematically Proven Biology™** · [Docs Site](https://veribiota.github.io/VeriBiota/)

[![Docs](https://img.shields.io/badge/docs-MkDocs%20Material-7A6BB2)](https://veribiota.github.io/VeriBiota/)
[![Fast Gates](https://github.com/VeriBiota/VeriBiota/actions/workflows/ci.yml/badge.svg?label=fast-gates)](https://github.com/VeriBiota/VeriBiota/actions/workflows/ci.yml)

> **Fast Gates:** every PR runs `make verify-results` (runtime-backed checks) and `make check` (schema validation) before merge.
[![Fast Gates](https://github.com/VeriBiota/VeriBiota/actions/workflows/ci.yml/badge.svg?label=fast-gates)](https://github.com/VeriBiota/VeriBiota/actions/workflows/ci.yml)

Schemas: `veribiota.model.v1` · `veribiota.checks.v1` · `veribiota.certificate.v1`  
Canon: `veribiota-canon-v1`

VeriBiota transforms biological and biochemical models into cryptographically signed, formally verified artifacts. Every reaction, rate law, and invariant is backed by theorem-proven logic and a reproducible audit trail—turning biological simulation into a compliance-grade science.

---

## 🚀 Mission
**To make verified computation the default for life sciences.**  
VeriBiota delivers the first open standard for Proof-Backed Biological Simulation by unifying:

- **Lean 4 + mathlib** (formal proofs of species, reactions, invariants)  
- **Deterministic JSON schemas** (`veribiota.model.v1`, `veribiota.certificate.v1`, `veribiota.checks.v1`)  
- **Cryptographic signing & verification** (Ed25519 + JWKS)  
- **Executable semantics** (Rust/CUDA runtime, in development)

Result: every model is provable, auditable, and portable—from a graduate thesis to FDA submissions.

---

## 🧠 Why It Matters
**“We can’t reproduce what we can’t verify.”**  
Modern biology depends on simulation, but trust in those models is thin. VeriBiota replaces ad-hoc tooling with a formal, signed standard.

| Old Workflow                        | VeriBiota Upgrade                                  |
| ----------------------------------- | -------------------------------------------------- |
| Ad-hoc scripts & spreadsheets       | Deterministic, versioned schemas                   |
| Trust-me simulations                | Cryptographically signed certificates              |
| Peer review via screenshots         | Machine-checked Lean proofs                        |
| Regulatory uncertainty              | Immutable, auditable verification bundles          |

---

## 🧩 Architecture at a Glance
```
Lean Proof Plane ──► Signed Certificate (JSON)
        │
        ▼
Rust/CUDA Engine ──► Verified Simulation Results
```

| Layer            | Technology                  | Purpose                                                      |
| ---------------- | --------------------------- | ------------------------------------------------------------ |
| Proof Plane      | Lean 4 + mathlib            | Defines species, reactions, invariants; emits signed proofs. |
| Model IO         | JSON (`veribiota.model.v1`) | Canonicalizes + hashes every model.                          |
| Signer           | Ed25519 / JWKS              | Attaches cryptographic authenticity.                         |
| Runtime Engine   | Rust + CUDA (roadmap)       | Executes ODE/SSA simulations against Lean-proven invariants. |
| Portal / CLI     | Lake + `veribiota`          | Emits, signs, and verifies bundles end-to-end.               |

---

## 🧰 Quickstart
```bash
# Build the toolchain
elan toolchain install $(cat lean-toolchain)
lake update && lake build

# Import a canonical SIR model and emit the full bundle
./veribiota import --in Biosim/Examples/Model/sir.model.json \
  --emit-all --out build/artifacts

# Verify signed outputs
./veribiota verify checks build/artifacts/checks/sir-demo.json \
  --jwks security/jwks.json --print-details
./veribiota verify cert build/artifacts/certificates/sir-demo.json \
  --jwks security/jwks.json --print-details
```

### Local signing quickstart

Leverage the new signing preflight guard to try the full signature round-trip with a disposable key:

```bash
openssl genpkey -algorithm ed25519 -out security/local-signing.key
export VERIBIOTA_SIG_MODE=signed-soft
export VERIBIOTA_SIG_KEY="$PWD/security/local-signing.key"
export VERIBIOTA_SIG_KID="local-test"

# derive the JWKS from the private key
X="$(
  openssl pkey -in "$VERIBIOTA_SIG_KEY" -pubout -outform DER \
  | tail -c 32 \
  | python3 -c 'import sys,base64;print(base64.urlsafe_b64encode(sys.stdin.buffer.read()).decode().rstrip("="))'
)"
jq -n --arg x "$X" --arg kid "$VERIBIOTA_SIG_KID" \
  '{keys:[{kty:"OKP",crv:"Ed25519",kid:$kid,x:$x}]}' > security/jwks.json

make sign-soft
```

`make sign-soft` now starts by running `scripts/sign_preflight.sh`, which verifies that the JWKS entry matches the private key and that any existing artifacts still advertise the canonicalization policy. If the preflight passes, the target re-emits the artifacts, signs them, prints SHA-256 digests, and immediately re-verifies the signatures.

> **Tip:** `VERIBIOTA_SIG_KEY` may point to a key file or contain the raw PEM text. When the latter is detected, `scripts/sign_key_path.sh` will materialize a temporary file under `security/` and wire everything up automatically.

> **macOS note:** Apple’s built-in LibreSSL lacks Ed25519 support. Install Homebrew’s OpenSSL 3 (`brew install openssl@3`) and point `VERIBIOTA_OPENSSL` at it:
> ```bash
> export VERIBIOTA_OPENSSL="$(brew --prefix openssl@3)/bin/openssl"
> ```
> The signing helper uses `VERIBIOTA_OPENSSL` whenever it is present.

Docs: https://veribiota.github.io/VeriBiota/ · [`docs/cli.md`](docs/cli.md) · [`docs/model-ir.md`](docs/model-ir.md) · [`docs/simulator-integration.md`](docs/simulator-integration.md)
Adapter pack: [`adapters/README.md`](adapters/README.md)

---

## 🔐 Verification Workflow
1. **Model authoring** → canonical JSON (`veribiota.model.v1`)  
2. **Proof & certification** → Lean theorems baked into `certificate.json`  
3. **Cryptographic signing** → Ed25519 signature + SHA256 digest + JWKS metadata  
4. **Verification** → anyone runs `./veribiota verify …` to confirm authenticity

Every artifact carries a hashable provenance chain:
```
model.json → certificate.json → checks.json → signature → JWKS
```

---

## 🧾 Provenance & Compliance
- Deterministic builds (`lake build` → byte-identical JSON)  
- Canonicalization: `veribiota-canon-v1` (UTF-8, sorted fields, trailing newline)  
- Digital signatures: Ed25519 (`signature.jws`) + JWKS registry (`security/jwks.json`)  
- Tamper harness + schema validation baked into CI (`.github/workflows/ci.yml`)  
- CI simulates results and (on Ubuntu) optionally evaluates drift/positivity via `biosim-eval`  
- Ready for 21 CFR Part 11 / SOC 2 audit trails

---

## 💼 For Enterprise & Research Partners
- **Proof-as-a-Service** — Verified model certification + signed bundles  
- **Enterprise License** — Private signer, audit ledger, SLA coverage  
- **Training** — Formal methods bootcamps for computational biology teams  
- **Runtime Integration** — GPU-accelerated verified simulations (Rust/CUDA roadmap)

📧 partnerships@veribiota.ai

---

## 🧭 Roadmap
- ✅ **Open-core release (`v0.10.2-pilot`)** — full proof-to-certificate chain  
- 🛠️ **Runtime engine (Rust/CUDA)** — verified ODE/SSA execution  
- 🧾 **Audit ledger + portal** — hosted verification + immutable log  
- 🧬 **Partner integrations** — pharma, synthetic biology, academic pilots

---

## ⚖️ License
- Open-core components (Lean proofs, CLI, schemas) — **Apache 2.0**  
- Enterprise runtime, signer, and audit modules — **Commercial license**  
- See `LICENSE` and `NOTICE` for terms and attribution

> **Important:** VeriBiota is **research software** and is **not** a medical device.  
> It is not intended for diagnosis, treatment, or clinical decision-making.

---

## 🏁 Tagline
**VeriBiota — Mathematically Proven Biology™**  
*Where every model is reproducible, provable, and trusted.*

---

## 📦 Releases

We publish two tarballs on every `v*` tag:

- `artifacts.tgz` — canonical model/certificate/checks from `build/artifacts/`
- `pilot-demo-v1-artifacts.tgz` — frozen pilot bundle under `releases/pilot-demo-v1/build/artifacts/`

Tag to release:
```bash
git tag v0.10.2-pilot
git push origin v0.10.2-pilot
```

The release workflow builds, (optionally) signs with `VERIBIOTA_SIG_KEY`/`VERIBIOTA_JWKS_JSON`, and uploads both tarballs along with `LICENSE` and `NOTICE`.

---

### Minisign sidecars (optional)
For Unix-friendly detached signatures, you can create `*.minisig` next to each JSON. These sign the same canonical bytes used for JWS.

```bash
# Sign (assumes VERIBIOTA_MINISIGN_SEC points to your .key)
make minisign

# Verify (assumes VERIBIOTA_MINISIGN_PUB points to your .pub)
make verify-minisign
```

Notes:
- Canonical bytes: the signer script canonizes first (LF + trailing newline, sorted) and signs the `.canon.json` content.
- Key storage: do not commit keys. Use `~/veribiota-secrets/` locally; CI uses GitHub Secrets.
- Cross‑platform: minisign isn’t installed on Windows by default; keep it optional. Primary JWS/JWKS remains the source of truth.
