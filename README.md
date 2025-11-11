# 🧬 VeriBiota  
**Mathematically Proven Biology™**

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

Docs: [`docs/cli.md`](docs/cli.md) · [`docs/model-ir.md`](docs/model-ir.md)

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

---

## 🏁 Tagline
**VeriBiota — Mathematically Proven Biology™**  
*Where every model is reproducible, provable, and trusted.*
