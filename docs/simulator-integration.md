# Simulator Integration

Every run of `./veribiota simulate` now emits an end-to-end VeriBiota bundle
(model → checks → certificate → trajectory) and immediately verifies the
trajectory via `verify results`. The Lean driver produces the artifacts under
`build/artifacts/…`, writes the JSONL trajectory, and calls the Rust runtime
evaluator (`biosim-eval`). Build it once with:
```bash
cargo build --manifest-path engine/biosim-checks/Cargo.toml --bin biosim-eval --release
```
That gives you a working “batch via CLI” adapter with zero extra code.

For other engines (C++/Python/Rust/…​) you can pick the integration style that
fits your stack. The sections below outline three common adapters and point to
drop-in sample code. See `adapters/` for ready-to-run demos plus
`examples/checks.mass.json` and `examples/trajectory.sample.jsonl` for a tiny
three-species test bundle.

## 1. Batch via CLI

Use this when you already have a simulator that can emit JSONL snapshots. The
flow is:

```bash
# 0) emit or import your model; the CLI writes model/cert/checks bundles
./veribiota --emit-all --out build/artifacts

# 1) validate schemas
node scripts/schemaValidate.mjs build/artifacts/checks/sir-demo.json \
     build/artifacts/certificates/sir-demo.json

# 2) sign (soft or enforced)
make sign-soft

# 3) run the simulator → trajectory.jsonl and evaluate
./veribiota simulate --steps 200 --out build/results/run.jsonl
# Verification runs automatically; rerun manually if needed:
./veribiota verify results build/artifacts/checks/sir-demo.json \
  build/results/run.jsonl

# 4) verify checks/certs and ship the bundle
make verify
```

Any engine that can write `trajectory.jsonl` with `{ "t": …, "counts": […] }`
rows can reuse this flow.

## 2. Streaming via C FFI

Link against `libveribiota_checks` and feed each timestep to the evaluator. The
header lives at `engine/biosim-checks/ffi/veribiota_checks.h` and exposes three
functions:

```c
int veribiota_checks_init(const char *jwks_json,
                          const char *checks_json,
                          int sig_mode);
int veribiota_checks_eval(const VeribiotaSnapshot *snap,
                          VeribiotaOutcome *out);
void veribiota_checks_free(void);
```

See `adapters/cpp/streaming_adapter.cpp` for a complete stub. The adapter keeps
the evaluator alive for the whole simulation, fills either `counts` or `conc`
arrays per timestep, and stops the run the moment `violated` flips true. Exit
codes follow the CLI: `0` OK, `2` for invariant violations, `-1` for other
errors.

## 3. Python wrapper via ctypes

When your simulator is Python/NumPy-centric, load the shared library with
`ctypes`. The sample adapter at `adapters/python/veribiota_adapter.py` shows how
to initialize the evaluator and stream `numpy` arrays (or plain lists) through
it:

```python
from veribiota_adapter import init_checks, eval_stream
import numpy as np

init_checks("build/artifacts/checks/sir-demo.json")
stream = ((i * 0.1, np.array([999 - i, 1 + i, 0])) for i in range(50))
eval_stream(stream)
```

The helper raises on the first violation so you can fail fast in notebooks or
batch jobs.

## 4. In-process Rust (optional)

If your engine is Rust, depend on `engine/biosim-checks` directly. Deserialize
the checks bundle once, call the `RuntimeChecks` implementation per snapshot,
and map the `Outcome` struct to your logging/telemetry system. This gives the
best performance (no FFI) while sharing the exact same invariant logic.

---

Regardless of the adapter, persist four artifacts per run:

1. `model.json`
2. `checks.json`
3. `trajectory.jsonl`
4. `eval.json` (or the console log from the evaluator)

Sign the bundle with `make sign-soft` (or the enforced variant) so downstream
engines can verify provenance. CI already tamper-tests the adapters by flipping
counts negative and perturbing invariant weights; make sure the same exit codes
propagate through your integration hook.
