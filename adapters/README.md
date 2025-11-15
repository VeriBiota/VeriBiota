# VeriBiota Adapter Pack

This folder contains minimal integration shims for streaming VeriBiota
invariants through other engines. Each adapter reuses the same sample bundle
under `examples/`:

- `examples/checks.mass.json` – tiny checks spec (positivity + total-mass).
- `examples/trajectory.sample.jsonl` – three-step trajectory.
- `examples/species.example.json` – canonical ordering (`["S","I","R"]`).

## C++ (CMake)

```
cd adapters/cpp
cmake -B build -S . -DVERIBIOTA_CHECKS_LIB=../../target/release/libbiosim_checks.so
cmake --build build
./build/streaming_adapter ../../examples/checks.mass.json
```

Prereqs:

1. `cargo build --manifest-path engine/biosim-checks/Cargo.toml --release`
   (produces `target/release/libbiosim_checks.so|.dylib|.dll`).
2. `VERIBIOTA_CHECKS_LIB` must point at that shared library when configuring
   CMake.

## Python (ctypes)

```
export VERIBIOTA_CHECKS_LIB=$PWD/target/release/libbiosim_checks.so
python adapters/python/demo.py --checks examples/checks.mass.json \
  --trajectory examples/trajectory.sample.jsonl
```

`demo.py` streams each JSONL snapshot through `libveribiota_checks` and stops at
the first violation.

## Rust (in-process)

```
cargo run --manifest-path adapters/rust/Cargo.toml -- \
  --checks ../../examples/checks.mass.json \
  --trajectory ../../examples/trajectory.sample.jsonl
```

This sample pulls in the `biosim-checks` crate directly, avoiding FFI overhead.
All adapters emit violation details (max abs/rel drift) and exit with code 2 on
failure so they can plug into CI and schedulers.
