# Runtime Checks FFI (v0.1.0)

The `engine/biosim-checks` crate exposes the minimal contract the compute team needs to honour while we stay on schema v1.

```rust
pub struct Snapshot<'a> {
    pub t: f64,
    pub counts: Option<&'a [i64]>,
    pub conc:   Option<&'a [f64]>,
}

pub struct Outcome {
    pub t: f64,
    pub any_neg: bool,
    pub violated: bool,
    pub max_abs_drift: f64,
    pub max_rel_drift: f64,
}

pub enum SigMode { Unsigned, SignedSoft, SignedEnforced }

pub trait RuntimeChecks {
    fn preload_jwks(&mut self, jwks_json: &str) -> anyhow::Result<()> { ... }
    fn load_checks(&mut self, checks_json: &str, mode: SigMode) -> anyhow::Result<()>;
    fn evaluate(&self, snap: &Snapshot) -> Outcome;
}
```

The C ABI (see `engine/biosim-checks/ffi/lib.c`) mirrors these structs:

```c
int veribiota_checks_init(const char* jwks_json,
                        const char* checks_json,
                        int sig_mode);
int veribiota_checks_eval(const VeribiotaSnapshot* snap,
                        VeribiotaOutcome* out);
void veribiota_checks_free(void);
```

## Expectations for v0.1.0

> **Status:** the `engine/biosim-checks` crate currently ships a **stub** implementation of `RuntimeChecks`. Signature modes are accepted as input but not enforced, and linear invariants are evaluated against a baseline of `0.0` using a demo-specific `S/I/R` indexing convention. Treat these checks as advisory until a full implementation lands.

1. **Signature verification (future)** – the FFI reserves a `SigMode` and `jwks_json` parameter so engines can enforce `signed-soft` / `signed-enforced` once a production verifier is wired in. The v0.1.0 stub does **not** perform real JWS/JWKS verification yet.
2. **Evaluate per snapshot** – SSA runs should call once per event; ODE runs can downsample (for example, every 10 integration steps) as long as `strict=true` checks halt immediately when violated.
3. **Report drift** – runtimes should report absolute and relative drift for each invariant, populate `max_*` fields, and mark `violated` whenever tolerance is exceeded. The current stub reports drift relative to a zero baseline; future versions will support user-declared baselines.
4. **Result bundles** – include `modelHash` and `checksDigest` from the JSON header so `veribiota verify results <checks> <results>` passes.
5. **Stability** – the FFI ABI is frozen until schema v0.2. Ship any engine changes via a new crate version without breaking symbols.

Once the real implementation lands, drop it into the `RuntimeChecks` trait and keep the stub as an integration test.

## Local Results Evaluation (Rust helper)

For quick validation of positivity and invariant drift on a results JSONL, build and run the lightweight Rust evaluator:

```bash
cargo build --manifest-path engine/biosim-checks/Cargo.toml --bin biosim-eval
./target/debug/biosim-eval \
  --checks build/artifacts/checks/sir-demo.json \
  --results build/results/sir-sim.jsonl
```

It prints a tally like:

```
tally: any_neg=false violated=false max_abs_drift=0.000000 max_rel_drift=0.000000
```

Notes:
- The helper reads either `conc` or `counts` arrays per snapshot and respects strict linear invariant tolerances.
- It’s a convenience tool for demos and local runs; production engines should link the FFI or embed an equivalent implementation.
