ART=build/artifacts
MODEL=$(ART)/models/sir-demo.json
CERT=$(ART)/certificates/sir-demo.json
CHECKS=$(ART)/checks/sir-demo.json
JWKS=security/jwks.json
DEFAULT_OPENSSL=$(shell /usr/bin/env bash -lc 'if [[ -x "/opt/homebrew/opt/openssl@3/bin/openssl" ]]; then echo /opt/homebrew/opt/openssl@3/bin/openssl; else command -v openssl; fi')
OPENSSL_BIN?=$(DEFAULT_OPENSSL)

.PHONY: emit sign-soft verify canon pilot-demo verify-results check

emit:
	./veribiota --emit-all --out $(ART)
	sha256sum $(MODEL) $(CERT) $(CHECKS)

sign-soft:
	@KEY_PATH=$$(./scripts/sign_key_path.sh) && \
	  VERIBIOTA_SIG_KEY="$$KEY_PATH" ./scripts/sign_preflight.sh && \
	  VERIBIOTA_SIG_MODE=signed-soft VERIBIOTA_SIG_KEY="$$KEY_PATH" VERIBIOTA_OPENSSL="$(OPENSSL_BIN)" ./veribiota --emit-all --out $(ART) \
	    --sign-key "$$KEY_PATH" --sign-kid "$$VERIBIOTA_SIG_KID" && \
	  sha256sum $(MODEL) $(CERT) $(CHECKS)

verify:
	./scripts/dev_jwks.sh
	./veribiota verify checks $(CHECKS) --jwks $(JWKS) --print-details
	./veribiota verify cert   $(CERT)   --jwks $(JWKS) --print-details

canon:
	./veribiota --canon $(CHECKS) --out $(CHECKS:.json=.canon.json)

pilot-demo: emit sign-soft verify
	@echo "Stripe link: $$VERIBIOTA_STRIPE_PILOT_URL"

.PHONY: simulate eval

# Run a quick ODE-like simulation and verify results metadata
simulate:
	./veribiota simulate --steps 50 --dt 0.25 --out build/results/sir-sim.jsonl
	./veribiota verify results $(CHECKS) build/results/sir-sim.jsonl

# Build and run the Rust helper to evaluate drift/positivity over results
eval:
	@if ! command -v cargo >/dev/null 2>&1; then \
	  echo "cargo is required for 'make eval'" >&2; exit 1; fi
	@if [ ! -f $(CHECKS) ]; then \
	  $(MAKE) emit; fi
	@if [ ! -f build/results/sir-sim.jsonl ]; then \
	  $(MAKE) simulate; fi
	cargo build --manifest-path engine/biosim-checks/Cargo.toml --bin biosim-eval
	./target/debug/biosim-eval --checks $(CHECKS) --results build/results/sir-sim.jsonl || true
	./target/debug/biosim-eval --json --checks $(CHECKS) --results build/results/sir-sim.jsonl || true

# Attempt to build biosim-eval, then run CLI verify results with soft fallback
verify-results:
	@if [ ! -f $(CHECKS) ]; then \
	  $(MAKE) emit; fi
	@if [ ! -f build/results/sir-sim.jsonl ]; then \
	  $(MAKE) simulate; fi
	@if command -v cargo >/dev/null 2>&1; then \
	  echo "[verify-results] building biosim-eval (release)"; \
	  cargo build --manifest-path engine/biosim-checks/Cargo.toml --bin biosim-eval --release || \
	    echo "[verify-results] cargo build failed; proceeding with CLI fallback"; \
	else \
	  echo "[verify-results] cargo not found; proceeding with CLI fallback"; \
	fi
	./veribiota verify results $(CHECKS) build/results/sir-sim.jsonl

# Validate checks and certificate JSON against schemas
check:
	@if [ ! -f $(CHECKS) ] || [ ! -f $(CERT) ]; then \
	  $(MAKE) emit; fi
	@node scripts/schemaValidate.mjs $(CHECKS) $(CERT)

MINISIGN_SEC?=$(VERIBIOTA_MINISIGN_SEC)
MINISIGN_PUB?=$(VERIBIOTA_MINISIGN_PUB)

.PHONY: minisign verify-minisign

minisign:
	@[[ -n "$(MINISIGN_SEC)" ]] || (echo "[minisign] set VERIBIOTA_MINISIGN_SEC to your .key path" && exit 2)
	@scripts/minisign_sidecar.sh $(MODEL) $(MINISIGN_SEC) "VeriBiota model"
	@scripts/minisign_sidecar.sh $(CERT)  $(MINISIGN_SEC) "VeriBiota certificate"
	@scripts/minisign_sidecar.sh $(CHECKS) $(MINISIGN_SEC) "VeriBiota checks"

verify-minisign:
	@[[ -n "$(MINISIGN_PUB)" ]] || (echo "[minisign] set VERIBIOTA_MINISIGN_PUB to your .pub path" && exit 2)
	minisign -Vm $(MODEL)    -p $(MINISIGN_PUB) -x $(MODEL).minisig
	minisign -Vm $(CERT)     -p $(MINISIGN_PUB) -x $(CERT).minisig
	minisign -Vm $(CHECKS)   -p $(MINISIGN_PUB) -x $(CHECKS).minisig
