# VeriBiota Pilot Demo Pack (v1)

This folder is the exact bundle we send to pilot customers. It contains:

- `build/artifacts/` – canonical SIR model, certificate, and checks bundles plus SHA256 sidecars.
- `jwks.sample.json` – sample public key document for signature verification drills.
- `Makefile` + `scripts/pilot_demo.sh` – frozen helpers that run the emit → sign-soft → verify workflow.

## Quick start

```bash
$ make pilot-demo
```

That command:

1. Emits a fresh model / certificate / checks bundle.
2. Signs them in `signed-soft` mode (cached JWKS sample).
3. Runs `veribiota verify … --print-details` on the checks and certificate.
4. Prints the SHA256 lines you can paste into a pilot report.

Run the command from the repository root (this folder is frozen snapshot data). All outputs land in `build/artifacts/`. Share the `sir.*.json` files and corresponding `.sha256` sidecars with the pilot customer alongside the Stripe invoice.

Need to re-run later? Re-run `make pilot-demo` (or call `scripts/pilot_demo.sh` directly) and compare the SHA lines. Deterministic output means the schema contract is still locked.
