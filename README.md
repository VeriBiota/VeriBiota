# Lean Biosim Blueprint

[▶️ **Run the Proof**](https://veribiota.ai/run-the-proof) — book a pilot demo slot (HubSpot form).

Pilot offer: **$10k** for two verified models + signed reports. Stripe invoicing available; bundle this repo’s `releases/pilot-demo-v1` folder with your quote.

## Pilot funnel assets

- Screencast (3 min): <https://veribiota.ai/video/make-pilot-demo.mp4> – shows `make pilot-demo` with SHA + signature lines.
- CTA button: the “Run the Proof” link above points to the HubSpot/Notion signup form.

_Current pilot tag: `v0.10.1-pilot` (introduces the `models/`, `certificates/`, `checks/` layout)._

## 1. Scope & Philosophy
- **Single source of truth:** one Lean core formalizes “biological dynamics”; every simulator (ODE, SSA, agent-based) is an implementation artefact extracted from the same semantics and proofs.
- **Typed sanity:** species inhabit finite types with decidable equality, states are `Finsupp` maps with codomains `ℕ`, `ℝ≥0`, or dimensionful newtypes. Units/positivity are enforced at the type level whenever viable.
- **Proof-centric engineering:** safety lemmas (positivity, support bounds, conservation) accompany any executable kernel. Modelers extend the core with custom invariants without rewriting compilers/simulators.
- **Layered semantics:** start from discrete steps (jump processes), lift to continuous time (ODE/SDE), then extend with spatial grids and typed agents—each layer reuses the same invariants.

## Signature modes (CLI)

| Mode             | Behavior |
| ---------------- | -------- |
| `unsigned`       | Default for local dev. Artifacts are canonicalized and `.sha256` sidecars are written, but no signature block is attached. |
| `signed-soft`    | Signs artifacts and verifies them immediately after emit; verification warnings do not fail the process. Ideal for CI/staging. |
| `signed-enforced`| Signs artifacts and requires verification everywhere (CLI, engine, orchestrator). Missing or invalid signatures cause hard failures. |

Set the mode via `--sig-mode` or `VERIBIOTA_SIG_MODE`. Signed modes also require `--sign-key`/`VERIBIOTA_SIG_KEY` and `--sign-kid`/`VERIBIOTA_SIG_KID`.

## Schema v1 API contract

The frozen schemas live at:

- Checks: <https://veribiota.ai/schema/v1/checks.json>
- Certificate: <https://veribiota.ai/schema/v1/certificate.json>
- Model IR layout: `docs/model-ir.md`

Artifacts conforming to schema v1 are valid for every pilot contract through **2025-Q1**. Version bumps will get new URLs (`/schema/v2/...`) and release tags.

## Pilot demo pack

- Folder: `releases/pilot-demo-v1`
- Contents: canonical SIR model/certificate/checks JSON files, SHA sidecars, JWKS sample, and frozen helper scripts.
- Usage: `make pilot-demo` prints SHA lines + verification output; send the resulting bundle alongside the Stripe invoice.

## Quickstart

### CLI in 60 seconds
```bash
make emit
BIOLEAN_SIG_MODE=signed-soft BIOLEAN_SIG_KID=veribiota-prod-2025-q1 \
BIOLEAN_SIG_KEY="$(cat ~/veribiota-secrets/veribiota_ed25519.pem)" \
  make sign-soft
make verify

# Import a canonical model + emit bundle
./veribiota import --in Biosim/Examples/Model/sir.model.json --emit-all \
  --out build/artifacts
```

See `docs/cli.md` for the full flag reference (`--emit-all`, `--canon`, `--checks-schema`, `verify results`, etc.).

## Engine integration handoff

See `docs/runtime_checks.md` for the `RuntimeChecks` trait, C ABI, and expectations on drift/positivity reporting. The FFI stays stable for the entirety of schema v1; treat it as frozen until v0.2.

## QA checklist

Before tagging or shipping a bundle, run through `docs/qa_checklist.md`. It captures the determinism matrix, AJV validation, tamper exit codes, CRLF normalization, pilot demo, and release upload requirements for v0.1.0.

## 2. Minimal Core (CRN-like)

### Key Structures
| Concept | Lean shape | Notes |
| --- | --- | --- |
| Species | `Type` with `[DecidableEq]` and often `Fintype` | Finite enumerations or indexed records. |
| State | `S →₀ α` (`α = ℕ` counts, `ℝ≥0` concentrations) | `Finsupp` provides finite support plus algebra. |
| Stoichiometry | `S →₀ ℤ` | Signed deltas derived from in/out stoichiometries. |
| Reaction | record of `(inStoich, outStoich, rate)` | Rate is `State S → ℝ≥0∞`; domain-specific laws wrap this. |
| System | `Finset (Reaction S)` (or `List` with `Nodup`) | Finite CRN; supporting notations for readability. |

### Deterministic Semantics (ODE)
\[
\frac{dx}{dt}(s) = \sum_{r \in R} \text{net}(r)(s) \cdot \text{rate}_r(x)
\]
- Provide a generic vector field `vf : (S → ℝ) → S → ℝ`.
- Rate combinators: pure mass-action, Hill/Michaelis–Menten, custom smooth laws.

### Stochastic Semantics (CTMC)
- State-dependent intensities `λ_r(x) : ℝ≥0`.
- Generator `Q(x, x + net r) = λ_r(x)`; diagonal entries ensure rows sum to zero.
- Gillespie SSA kernel is shown equivalent to this generator.

## 3. Proof Kits

| Lemma family | Goal | Ingredients |
| --- | --- | --- |
| Positivity | `fire` never produces negative counts. | `Finsupp` subtraction and enabling predicate. |
| Support bounds | Only mentioned species change. | `Finsupp.support` lemmas. |
| Linear invariants | `w · x` preserved when `w · net(r) = 0`. | Finite sums + dot-product macros. |
| Well-posed ODE | Local Lipschitz → existence/uniqueness. | Mathlib ODE library, polynomial bounds. |
| CTMC soundness | SSA distribution matches CTMC law. | Probability monad, measure-theoretic reasoning. |
| Absorbing/extinction | Characterize states with zero enabled reactions; prove extinction for pure death. | Markov chain hitting probabilities, supermartingale arguments. |

Reusable automation goal: `invariant_by_linear_form` tactic consumes stoichiometry matrix proofs and discharges conservation obligations.

See `docs/invariants.md` for `Invariant.lin.auto` examples and invariant-preservation lemmas.

## 4. Project Layout

```
lean-biosim/
  Biosim/Core/Species.lean          -- species classes, finite states, units scaffolding
  Biosim/Core/State.lean            -- aliases for ℕ/ℝ≥0 states, helper lemmas
  Biosim/Core/Stoich.lean           -- net effects, enabling predicates
  Biosim/Core/Reaction.lean         -- reaction records, rate combinators
  Biosim/Core/System.lean           -- CRN containers, DSL entries
  Biosim/Semantics/Discrete.lean    -- jump semantics, SSA step relation
  Biosim/Semantics/ODE.lean         -- vector field, well-posedness
  Biosim/SSA/Gillespie.lean         -- SSA kernel, proof of CTMC equivalence
  Biosim/Proofs/Invariants.lean     -- generic invariant theorems/tactics
  Biosim/Proofs/Positivity.lean     -- safe firing, support bounds
  Biosim/Examples/SIR.lean          -- deterministic SIR, conserved totals
  Biosim/Examples/BirthDeath.lean   -- CTMC model, extinction lemma
  Biosim/Examples/GRN.lean          -- toggle switch semantics
  Biosim/Docs/Roadmap.lean.md       -- living design notes
```

## 5. Lean Sketches

```lean
import Mathlib.Data.Finsupp
open scoped BigOperators

/-- Species live in some finite type. -/
class Species (α : Type) extends DecidableEq α

abbrev State (S : Type) := S →₀ ℕ
abbrev Stoich (S : Type) := S →₀ ℤ

structure Reaction (S : Type) where
  inStoich  : S →₀ ℕ
  outStoich : S →₀ ℕ
  rate      : State S → ℝ

namespace Reaction
def net {S} (r : Reaction S) : Stoich S :=
  r.outStoich.map Int.ofNat - r.inStoich.map Int.ofNat
end Reaction
```

Deterministic vector field:
```lean
def vf (sys : System S) (rate : Reaction S → (S → ℝ) → ℝ)
    (x : S → ℝ) (s : S) : ℝ :=
  ∑ r in sys.toFinset, rate r x * (r.outStoich s - r.inStoich s)
```

Linear invariant lemma skeleton:
```lean
structure LinInv (S : Type) where
  w : S → ℝ

def conservedBy (w : LinInv S) (r : Reaction S) : Prop :=
  ∑ s in r.supportUnion, w.w s * (r.outStoich s - r.inStoich s) = 0

theorem conserved_step
    (w : LinInv S) (sys : System S)
    (H : ∀ r ∈ sys.rs, conservedBy w r)
    {x} {r} (hr : r ∈ sys.rs) (h : System.enabled x r) :
    (∑ s, w.w s * (System.fire x r h s)) = ∑ s, w.w s * x s := by
  -- Uses algebraic lemmas on finsupp; `H hr` discharges the goal.
  admit
```

SSA step relation:
```lean
structure SSAStep (S : Type) (sys : System S) where
  x x' : State S
  r    : Reaction S
  τ    : ℝ
  enabled : System.enabled x r
  wait_nonneg : 0 ≤ τ
  x'_def  : x' = System.fire x r enabled
```

## 6. Example Pack
- **Birth–Death (`Examples/BirthDeath.lean`):** single species; positivity lemma, extinction probability proof (`δ > β`), expected count solves linear ODE.
- **SIR (`Examples/SIR.lean`):** deterministic ODE with conserved total `S + I + R`; R₀ bounds for the infection peak.
- **Genetic toggle (`Examples/GRN.lean`):** two repressors, Hill-rate reactions; prove existence of two attracting fixed points in symmetric parameter regime.

## 7. Notation & DSL
- Provide human-friendly macros:
  ```lean
  notation:50 L:50 " ⟶[" k:50 "] " R:50 =>
    Reaction.mk L R (fun x => massAction k ⟨L, R, ?_⟩ (fun s => (x s : ℝ)))
  ```
- `system` block:
  ```lean
  def BirthDeath : System Species :=
    system
    | ∅      ⟶[β]   X
    | X      ⟶[δ]   ∅
  ```
- Thin wrappers exporting CRNs to JSON for visualization tooling.

## 8. Phase-2 Extensions
- **Agent-based:** global state as multiset of agent records; rules as typed rewrites with guards. Provide mean-field compilation back to the CRN layer when applicable.
- **Spatial:** add lattice indices to species labels; discrete diffusion operators; max-principle proofs ensure positivity on grids; future bridge to PDE semantics.

## 9. Roadmap

| Phase | Duration | Milestones |
| --- | --- | --- |
| 0 — Boot & CI | 1–2 days | Lean toolchain, skeleton modules, CI running style-checks. |
| 1 — Discrete core + invariants | 3–5 days | `fire` semantics, positivity and linear invariants, DSL sugar, Birth–Death example. |
| 2 — ODE semantics | 1–2 weeks | Vector field + Lipschitz proofs, SIR conservation, differential invariant helpers. |
| 3 — SSA | 2–3 weeks | SSA step relation, measurable kernel, CTMC equivalence theorem, tail bounds on events. |
| 4 — Libraries & ergonomics | ongoing | Hill laws, unit system, invariant tactics, JSON exporters. |
| 5 — Agent/spatial | stretch | Typed agents, diffusion grids, PDE coupling explorations. |

Each phase ends with both formal statements and executable artifacts (Lean programs compiling to simulators) checked within the same repository.

## 10. Agent Workflow & Runtime Guardrails
- **Task cards:** structured specs live in `tasks/*.task.md`, validated by `schemas/task.schema.json`. Status must stay in (`todo`, `in_progress`, `blocked`, `done`) and acceptance clauses are executable checks.
- **Scratchpad:** use `.agent/state.json` plus per-task notes/traces for hand-offs. Decisions that change scope or ordering append to `.agent/decisions.log`.
- **Tooling contract:** agents restrict themselves to whitelisted commands declared in the cards and `Agentfile.md`.
- **Perf heuristics:** prefer shared-memory tiling with affine-gap DPX fast paths when available, keep host buffers pinned, overlap H2D/D2H with CUDA streams, and emit perf counters through the existing OGN logging macros.

## 11. Lean Toolchain & CI
- **Local setup:** install [`elan`](https://github.com/leanprover/elan) and run `elan default $(cat lean-toolchain)` (or `elan toolchain install ...`) to sync with the repo’s pinned Lean 4 release.
- **Dependency bootstrap:** execute `lake update` followed by `lake exe cache get` (optional but strongly recommended to download mathlib binaries) and finally `lake build` to check the library plus `Main.lean`.
- **Task schema validation:** run `npm install` once, then `npm run check:tasks` any time a `.task.md` changes.
- **CI:** `.github/workflows/ci.yml` mirrors these steps on every push/PR—Node toolchain for task validation plus an `elan` install that runs `lake update`, `lake exe cache get`, and `lake build`.

## 12. 0–90 Day Company Plan (build + sell in parallel)

### Weeks 1–2 — Boot & show the core works
- **Engineering deliverables:** publish the repo with `Biosim/Core/Basic.lean` (states/reactions/system + `fire`), `Biosim/Proofs/Invariants.lean` (linear invariant skeleton w/ `sorry` placeholders), `Biosim/Proofs/Certificate.lean` (JSON proof-certificate exporter), and `Biosim/Examples/SIR.lean` (infection + recovery reactions). Add a CLI or `#eval` that calls `ProofCert.save` to emit a SIR certificate JSON containing model name, semantics, and theorem IDs.
- **Acceptance criteria:** `lake build` succeeds on the pinned mathlib commit, at least one generic lemma is proved end-to-end (e.g. `firePreservesNonneg`), and a demo SIR certificate file is generated.
- **Launch collateral:** tiny landing page with the single-line value prop — “Proof-backed biological simulations: models that regulators, investors, and engineers can trust.”

### Weeks 3–6 — Make it undeniably useful
- **Engineering:** ship `Invariant.lin` tactic v0 (auto-proves linear conservation by checking that `w · net(r) = 0` for each reaction), deterministic semantics v0 (ODE vector field API + local Lipschitz scaffold for mass-action), SBML-lite JSON importer → `System`, and certificate v1 that records model hash, theorem statements/proof IDs, and parameters.
- **Go-to-market:** identify six pilot targets (three academic labs + three startups) and pitch a $15k fixed-price engagement: “we port your CRN/SBML to Lean, prove positivity plus ≥1 invariant, and return a signed JSON certificate + reproducible notebook.” Build a 10-slide deck covering problem → risk → core → demo proof → pilot scope → outcomes → price.
- **Acceptance criteria:** import at least one nontrivial CRN (≥5 species, ≥8 reactions), prove two invariants automatically, and close 1–2 paid pilots or signed LOIs with dates.

### Weeks 7–12 — Platform & revenue
- **Engineering:** SSA semantics v0 (path relation + generator equivalence on finite state), Rust `biosim-engine` stub that consumes exported JSON for fast ODE/SSA simulation with property tests against Lean invariants, and certificate/audit trail metadata (model hash, timestamps, mathlib commit, operator).
- **Sales packaging:** convert pilots to an open-core offer (Lean kernel + invariant tactic + examples under Apache-2) with commercial add-ons (SBML importer, certificate tooling, audit logging, GPU/Rust engine, SLAs). Services team handles model porting/bespoke proofs.
- **Acceptance criteria:** first invoice collected, “click-through” demo (upload JSON → receive certificate + sample sim plot), and written product packaging/pricing.

### Product packaging & pricing
- **Pricing bands:** Pilots at $10k–$25k (2–4 weeks for model port + two invariants + certificate); Enterprise Base at $30k/yr scaling to $120k/yr (Plus) based on model count/SLA depth; per-certificate add-on $2k–$8k (re-runs free for the same pinned model); compute at pass-through or 2× markup when hosted.
- **Open-core stance:** keep the Lean semantics, invariant tactic, and examples Apache-2; commercialize importers, certificates/audit logs, and GPU/Rust engines.

### This week’s exact task list
- **Build:** pin mathlib in `lakefile.lean`, run `lake build`, wire `#eval` (or CLI) that invokes `ProofCert.save` for SIR, and add the `Invariant.lin` tactic stub plus walker that checks `w · net(r) = 0` across all reactions.
- **Sell:** draft a one-pager and send to six pilot prospects describing the 2–4 week proof-backed certificate offer; book three 30-minute discovery calls using the SIR certificate demo as the anchor.

## 13. Architecture Blueprint (v1)

### Layered components
| Layer | Tech | Responsibility |
| --- | --- | --- |
| **Spec & proofs** | Lean 4 + mathlib (Lake project) | Defines `Species`, `State`, `Reaction`, semantics (discrete/ODE/SSA), invariant tactics, and certificate builder. Single source of truth for all semantics + theorems. |
| **Model IR** | JSON (`model.json`) | Canonical serialization of species, stoichiometry, rate-law tags/params, provenance metadata. Generated from Lean (for golden sources) or via SBML-lite importer for external models. |
| **Certificate IR** | JSON (`certificate.json`) | `{ modelHash, semantics, theorems: [{name, statement, proofId}], timestamp, toolchain, operator }`. Produced exclusively by Lean’s `ProofCert.save` after proofs check. |
| **Engines** | Rust crate `biosim-engine` (+ future CUDA) | Deterministic ODE + SSA executors consuming `model.json`. Uses property tests to ensure simulated trajectories respect Lean-proved invariants. |
| **Apps** | CLI / web “click-through” | Uploads JSON, invokes Lean certifier, dispatches sims via Rust engine, and emits charts + signed audit bundles. |

### Data flow
1. **Authoring:** models enter via Lean DSL or SBML-lite JSON importer (`Importer.toSystem`). All roads produce a `System` inside Lean.
2. **Proof phase:** invariants/positivity/ODE well-posedness are proved with reusable tactics (`Invariant.lin`, positivity kit, ODE Lipschitz lemmas). Successful proofs attach proof IDs.
3. **Certification:** `ProofCert.save` hashes `model.json`, records toolchain + mathlib commit, and writes `certificate.json`.
4. **Execution:** exported `model.json` feeds `biosim-engine` (Rust). Test harness cross-checks sampled trajectories against Lean invariants (QuickCheck-style) before any customer run.
5. **Distribution:** certificates + sim artifacts land in an audit log (Part-11 friendly) alongside operator identity and timestamp; customers receive both JSON files plus notebooks.

### Proof kits & priorities
- **Always-on:** positivity/support bounds, linear invariants (`Invariant.lin` with `w · net(r)` walker), and total-mass conservation macros.
- **High-signal:** Lipschitz/ODE existence-uniqueness (mass-action polynomial bounds), SSA ↔ CTMC equivalence (finite state), and generator soundness lemmas.
- **Automation hooks:** importer annotates reactions with rate-law families to auto-select appropriate tactics (mass-action vs Hill), while certificate generator includes the tactic provenance for traceability.

### Runtime + audit considerations
- Every certificate embeds `(mathlib commit, Lean version, importer version, engine version)` so regulators can replay proofs.
- Rust/engine layer treats Lean as authoritative; any divergence triggers a “proof mismatch” alert instead of silently running.
- Audit logs append `{modelHash, certHash, operator, customer, timestamp}` to a tamper-detectable ledger (file + optional managed DB).

### Risk mitigations baked into the architecture
- **Lean ergonomics:** users interact via JSON/DSL importer; Lean files stay internal to the toolchain.
- **SBML complexity:** start with SBML-lite schema (species, reactions, rates, units), validate strictly, and extend coverage incrementally.
- **Performance skepticism:** Rust/CUDA engines shoulder simulation load while Lean provides proofs; property tests verify no invariant regressions before delivery.

## 14. North Star
- **Single source of truth:** Lean definitions and theorems are canonical; every engine, dashboard, and notebook derives from or is checked against them.
- **Reproducibility by construction:** every artifact embeds toolchain pins (Lean version, mathlib commit), model hash, theorem set, and parameterization.
- **Dual execution planes:** the proof plane (Lean) owns semantics + proofs; the compute plane (Rust/CUDA) performs fast simulation while verifying against the proof plane.

## 15. Big Picture (Components & Flows)
```mermaid
flowchart LR
  subgraph Client
    UI[Web UI] --- CLI[CLI]
    SDK[Python SDK]
  end

  UI --> API
  CLI --> API
  SDK --> API

  subgraph ControlPlane
    API[Gateway/API]
    Auth[OIDC AuthN/AuthZ]
    Orchestrator[Job Orchestrator]
    Billing[Billing/Metering]
    Audit[Audit Trail]
  end

  subgraph ProofPlane
    Prover[Lean Prover Service]
    ModelCanon[Model Canonicalizer]
    CertSvc[Certificate Service]
    TacticLib[Tactic Library]
  end

  subgraph Data
    Reg[(Model Registry - Postgres)]
    Art[(Artifacts - S3/Blob)]
    MQ[[Queue]]
    Met[(Metrics - Prometheus)]
    Logs[(Logs)]
  end

  subgraph ComputePlane
    Engine[Simulation Engine (Rust/CUDA)]
    SWEEP[Param Sweep/Batch Runner]
    Cache[(Result Cache)]
  end

  API --> Auth
  API --> Reg
  API --> Orchestrator
  Orchestrator <---> MQ
  Orchestrator --> Prover
  Orchestrator --> Engine
  Prover --> ModelCanon
  Prover --> CertSvc
  CertSvc --> Art
  Engine --> Cache
  Engine --> Art
  API --> CertSvc
  API --> Cache
  API --> Billing
  API --> Audit
  Met --- API
  Met --- Prover
  Met --- Engine
```

- **Import → Prove → Certify:** SBML/JSON model → canonicalizer → Lean spec → run tactics → signed certificate JSON stored alongside artifacts.
- **Simulate:** canonical model + parameters → Rust engine (SSA/ODE) → results + provenance → persisted and cached.
- **Check:** randomized property checks ensure engine trajectories respect Lean-inferred invariants.

## 16. Lean Domain Model
- **Core concepts:** finite `Species`, discrete `State : Species →₀ ℕ` (counts) or `Species →₀ ℝ≥0` (concentrations), `Reaction` records with in/out stoichiometry and rate laws, `System` as a finite list of reactions.
- **Semantics:** CTMC generator `Q(x, x + net r) = λ_r(x)` and ODE flow `dx/dt = Σ_r net(r) · rate_r(x)`.
- **Proof toolkits:** positivity/support bounds, linear invariants (`w · net(r) = 0`), ODE well-posedness (local Lipschitz for mass-action/smooth), SSA ≡ CTMC equivalence via finite-state restriction.
- **Library layout:**
  - `Biosim/Core/` — states, reactions, enabling, `fire`.
  - `Biosim/Semantics/ODE/` — vector fields, Lipschitz scaffolding.
  - `Biosim/Semantics/CTMC/` — generator, measurability.
  - `Biosim/SSA/` — step relation, path measures, equivalence.
  - `Biosim/Proofs/` — positivity/invariants/well-posedness.
  - `Biosim/Tactics/` — invariant/positivity automation.
  - `Biosim/DSL/` — model-building sugar.
  - `Biosim/IO/` — JSON codecs for models/certificates.
  - `Biosim/Examples/` — SIR, birth–death, toggle switch, etc.

## 17. Interchange Formats
### Model IR (`model.json`)
- Canonical schema enabling round-trip between Lean, importers, and engines.
- Deterministic species ordering, integer stoichiometry, normalized parameter names.
- Rate laws tagged declaratively (`mass_action`, `hill`, `mm`, etc.) with parameter maps.
- SHA-256 hash computed post-canonicalization for proof/simulation caching.

```json
{
  "schema": "veribiota.model.v1",
  "meta": {
    "createdAt": "2025-11-06T12:00:00Z",
    "createdBy": "user@org",
    "toolchain": {
      "lean": "4.x.y",
      "mathlib": "commit-sha"
    }
  },
  "model": {
    "id": "sir-demo",
    "species": ["S", "I", "R"],
    "parameters": { "beta": 0.2, "gamma": 0.1 },
    "reactions": [
      {
        "name": "infect",
        "in": { "S": 1, "I": 1 },
        "out": { "I": 2 },
        "rate": { "kind": "mass_action", "k": "beta" }
      },
      {
        "name": "recover",
        "in": { "I": 1 },
        "out": { "R": 1 },
        "rate": { "kind": "mass_action", "k": "gamma" }
      }
    ],
    "units": { "S": "count", "I": "count", "R": "count" }
  },
  "hash": "sha256:...canonicalized..."
}
```

### Certificate JSON (`certificate.json`)
- Machine-checkable proof artifact including semantics, theorem statements, proof IDs, and cryptographic signature.

```json
{
  "schema": "veribiota.certificate.v1",
  "modelHash": "sha256:...",
  "semantics": ["CTMC", "ODE"],
  "toolchain": { "lean": "4.x.y", "mathlib": "commit-sha", "tacticLib": "v0.1.0" },
  "theorems": [
    { "name": "positivity", "statement": "∀ t, x(t) ≥ 0", "proofId": "b3f9..." },
    { "name": "conservation:N", "statement": "S+I+R invariant", "proofId": "9c2a..." }
  ],
  "limits": { "domain": "counts", "assumptions": ["rates≥0", "finite state"] },
  "signature": { "alg": "Ed25519", "keyId": "cert-signer-1", "jws": "..." },
  "timestamp": "2025-11-06T12:05:00Z"
}
```

### Checks JSON (`checks/sir-demo.json`)
- Canonical runtime-check bundle derived directly from Lean proofs.
- Header pins schema, toolchain (Lean/mathlib/tactic release), model hash, and generation timestamp.
- Each entry is typed (`positivity_counts`, `positivity_conc`, `lin_invariant`) with deterministic ordering, traceability (`proofId`), and explicit tolerance budget:
  - `positivity_counts` enforces integer-state non-negativity.
  - `positivity_conc` guards continuous integrators (`min(x) ≥ −ε`), recording the absolute tolerance used by the engine.
  - `lin_invariant` stores weights as a sorted map, tolerance policy (`absolute`/`relative`), `strict` mode, and the `proofId` that justified the invariant.
- Files are newline-terminated and accompanied by `sir-demo.json.sha256` sidecars for manual audits.
- Optional signature block (`signature`) is appended when `--sig-mode signed-soft|signed-enforced` is active. It records the algorithm (`Ed25519`), key ID, `issuedAt`, canonicalization metadata (always `scheme: veribiota-canon-v1` with LF + trailing newline), the payload hash (`sha256:<hex>` of the canonical payload *before* the signature is added), and a compact JWS. The protected header is `{"alg":"EdDSA","kid":"…","typ":"JWT","veribiotaCanon":"veribiota-canon-v1"}` and both header/payload/signature components use base64url encoding (per RFC 7515). Padding is stripped.
- Verification order: remove the signature block, re-render canonically (LF + newline), recompute `sha256:<hex>` and compare with `signature.payloadHash`, then verify the Ed25519 signature over `base64url(header) || "." || base64url(payload)` using the JWKS key matching `kid`. `signed-enforced` rejects any artifact missing or failing verification; `signed-soft` logs a warning but continues.

```json
{
  "schema": "veribiota.checks.v1",
  "toolchain": {"lean":"4.12.0","mathlib":"5f8c1ad","tactics":"Invariant.lin@0.1"},
  "modelHash": "sha256:cafebabe...",
  "generatedAt": "2025-11-10T17:00:00Z",
  "checks": [
    {"type":"positivity_counts","species":["S","I","R"]},
    {"type":"positivity_conc","species":["S","I","R"],"tolerance":1e-12},
    {"type":"lin_invariant","name":"N","proofId":"9c2a...",
      "weights":{"I":1,"R":1,"S":1},
      "tolerance":{"mode":"absolute","value":0.0},
      "strict":true}
  ]
}
```

### Simulation Result Bundle
- Header with model hash, parameter assignment, seeds, engine version.
- Body storing trajectories (time grid, state vectors), events, RNG provenance.
- Footer listing invariant checks (positivity, conserved quantities), bounds, and structured errors if violated.

## 18. Services Plane (SaaS)
- **API Gateway:** REST for clients + gRPC for internal services. Key endpoints:
  - `POST /v1/models/import` → `201 { modelId, modelHash }`.
  - `POST /v1/models/{modelId}/prove` → async `202 { jobId }`.
  - `GET /v1/certificates/{certificateId}` → certificate JSON.
  - `POST /v1/simulate` → `202 { runId }`.
  - `GET /v1/results/{runId}` → artifact links + status.
  - `GET /v1/checks/{runId}` → invariant summaries.
- **Prover Service:** renders canonical models into Lean modules, invokes tactics (`lin_conservation`, `positivity`, `lipschitz`), aggregates proofs into signed certificates, and caches by `(modelHash, theoremSet, toolchain)`.
- **Engine Service:** Rust/CUDA executors for ODE (DP5) and SSA (direct + next reaction) with reproducible RNG (PCG64). Batch runner handles parameter sweeps with hermetic containers; results land in object storage with summaries.
- **Orchestrator:** schedules proof/sim jobs via queue, prioritizes proofs, retries idempotently, and tracks job history.
- **Registry & Artifacts:** Postgres for models/runs/certs/billing; S3/Blob for model/certificate/result payloads.
- **Auth/Billing/Audit:** OIDC-powered RBAC per org, metering on proofs and compute, append-only audit log capturing request digests and actors.

## 19. Compute Plane Details
- **Performance:** zero-copy JSON parsing (serde), structure-of-arrays trajectories, memory-mapped outputs, GPU SSA for large propensity counts.
- **Determinism:** record RNG algorithm/seed/substream; fix floating-point mode and integrator tolerances; identical result headers on rerun with identical seeds.
- **Correctness hooks:** embed Lean-derived check functions (positivity, linear invariants) into runtime; violations abort runs with repro bundles.

## 20. Importers & DSL
- SBML-lite importer maps compartments/species/reactions/parameters into Model IR while preserving units when available.
- JSON DSL enumerates rate-law kinds (mass_action, hill, mm, custom_poly, user_defined with additional proof obligations).
- Canonicalization flattens algebra, sorts supports, validates non-negativity requirements.

## 21. Developer Experience
- **Repos:** `veribiota-core` (Lean OSS), `veribiota-engine` (Rust/CUDA enterprise), `veribiota-service` (API/orchestrator enterprise), `veribiota-sdks` (Python/TypeScript), `veribiota-examples` (verified gallery).
- **Build tooling:** Lake for Lean, Cargo for Rust, Nix/Docker for reproducible builds.
- **CI matrix:** pins `{lean, mathlib, rustc, CUDA}`; stores proof caches per commit; runs nightly property tests ensuring engine invariants.
- **Testing:** Lean unit lemmas, Rust integrator tests on analytic systems, property tests for invariant preservation, golden certificates/result summaries.

## 22. Observability
- **Metrics (Prometheus):** proof durations, lemma counts, engine throughput, invariant drift, queue depth, p99 job latency.
- **Logs:** structured JSON with correlation IDs.
- **Tracing:** end-to-end OpenTelemetry spans across API → Prover → Engine.

## 23. Security & Compliance
- Content-addressed storage (sha256) for models/results; references are by hash.
- Certificates signed with Ed25519 keys stored in HSM/KMS with rotation + key IDs.
- Supply-chain provenance (SLSA-style attestations) for binaries.
- Multi-tenant isolation at DB and artifact layer; default posture avoids PII.

## 24. Extensibility Points
- Rate-law plugins register Lean semantics, proof obligations, and engine evaluators.
- Constraint modules for dimensional analysis/unit checking (future type-level units).
- Spatial add-ons introduce lattice diffusion operators with discrete maximum principles and matching engine kernels.

## 25. Open-Core vs Enterprise Boundary
- **Open-core (OSS):** Lean core, base tactics, CLI, canonical examples (SIR/birth-death, etc.).
- **Enterprise:** SBML import pipeline, certificate signer, orchestrator, GPU/CUDA engine, audit/billing services, hosted UI, parameter sweeps.
- **Services:** bespoke model porting, custom theorem packages, HPC integrations.

## 26. API Contracts (Sketch)
```
POST /v1/models/import
Content-Type: application/json
-> 201 { "modelId": "...", "modelHash": "sha256:..." }

POST /v1/models/{modelId}/prove
-> 202 { "jobId": "..." }

GET /v1/certificates/{certificateId}
-> 200 application/json

POST /v1/simulate
Body: { "modelHash": "...", "params": {...}, "sim": {"mode":"ssa","T":1000,"seed":42} }
-> 202 { "runId": "..." }

GET /v1/results/{runId}
-> 200 { "status": "...", "urls": { "bundle": "s3://...", "preview": "..." } }

GET /v1/checks/{runId}
-> 200 { "positivity": true, "invariants": [{ "name": "N", "maxDrift": 1e-10 }] }
```

## 27. Implementation Milestones
- **Milestone A (2–3 weeks):** Model IR v1 with canonicalization/hash, Lean positivity + linear invariants with tactic, certificate v1 (unsigned acceptable), minimal ODE (DP5) + SSA engines, CLI/Python SDK for import → prove → simulate workflow.
- **Milestone B (next 4–6 weeks):** certificate signing + audit trail, parameter sweep runner, upload/download UI, property tests bridging engine ↔ Lean invariants, SBML-lite importer.
- **Milestone C (~Quarterly):** CTMC/SSA equivalence theorem (finite-state), GPU acceleration for SSA, spatial/lattice preview.

## 28. Non-Functional Targets
- Median proof time < 30 s for systems with ≤ 20 reactions.
- Simulation throughput ≥ 10⁶ events/s (CPU) and ≥ 10⁷ events/s (GPU target).
- Reproducible determinism: identical result headers for same seeds/config.
- Certificate issuance SLO: 99% < 2 minutes for typical models.
- Cost guardrails: autoscaled engine nodes with preemptible sweeps.

## 29. Immediate Build Tasks
- Implement `Invariant.lin` tactic v0 (`conservation.auto`, exposed in Lean as `conservation_auto`) checking `w · net(r) = 0` across reactions and constructing Lean proof terms.
- Emit runtime checkers from Lean (positivity, linear invariants) as lightweight evaluators consumed by the engine.
- Wire certificate generation via `ProofCert.save`, producing JSON with toolchain pins and at least two theorem slots (flag any placeholder proofs clearly).

### Demo Artifacts
- `Biosim/IO/Model.lean` defines the canonical model JSON IR; `Biosim/Examples/Model/SIR.lean` instantiates it for the SIR CRN.
- Generate the golden trio (model, certificate, checks) with the CLI:

```bash
make emit
sha256sum build/artifacts/models/sir-demo.json \
          build/artifacts/certificates/sir-demo.json \
          build/artifacts/checks/sir-demo.json

# Signed bundle (requires VERIBIOTA_SIG_KEY/KID in env)
VERIBIOTA_SIG_MODE=signed-soft make sign-soft

# Local verify auto-copies the sample JWKS if missing
make verify
```

  This emits:
  - `build/artifacts/models/sir-demo.json` + `sir-demo.json.sha256`
  - `build/artifacts/certificates/sir-demo.json` + `sir-demo.json.sha256`
  - `build/artifacts/checks/sir-demo.json` + `sir-demo.json.sha256`

> **JWKS note:** `make verify` runs `scripts/dev_jwks.sh`. If `security/jwks.json` is absent it copies `security/jwks.sample.json` so local verification “just works.” Never ship the sample key in CI or prod—wire a real JWKS there.

- **Advanced CLI automation:** embed the CLI inside other tooling by setting `VERIBIOTA_ARGS_JSON` (JSON array of strings). Regular command-line invocation remains the hero path; the env override is only for headless integrations.
- `Biosim.Examples.InvariantDemo` demonstrates the `conservation_auto` tactic (alias `Invariant.lin`) on a toy reaction that trivially preserves total mass.
- `Biosim/Examples/SIR.lean` instantiates infection/recovery reactions, proves total-population conservation, and shows positivity preservation for concrete populations.

### Testing
- Run `lake env lean Tests/Main.lean` to regenerate artifacts and assert:
  - model/certificate/check JSON files (each with a `sir-demo.json.sha256` sidecar) exist,
  - the certificate and checks `modelHash` fields match the model artifact,
  - semantics/theorem entries align with expectations and checks bind back to proof IDs,
  - the checks bundle round-trips byte-for-byte, matches a golden snapshot, rejects corruption (missing schema / bad hashes), and scales to ≥200 species without size blow-ups.
- The script exits nonzero on failure so it can gate CI.
- **Signature modes:** `--sig-mode unsigned` (default) emits plain JSON, `--sig-mode signed-soft` attaches a signature but does not enforce verification, and `--sig-mode signed-enforced` requires both signing and verification everywhere. The flag can be sourced from `VERIBIOTA_SIG_MODE`. When a signed mode is selected you must also pass `--sign-key <path>` (or `VERIBIOTA_SIG_KEY`) and `--sign-kid <id>` (or `VERIBIOTA_SIG_KID`).
