# Keep artifacts inside this release directory so paths stay consistent
ART=build/artifacts
OUT_DIR=$(CURDIR)/$(ART)
MODEL=$(OUT_DIR)/models/sir-demo.json
CERT=$(OUT_DIR)/certificates/sir-demo.json
CHECKS=$(OUT_DIR)/checks/sir-demo.json
JWKS=security/jwks.json

.PHONY: emit sign-soft verify canon pilot-demo

emit:
	../../veribiota --emit-all --out "$(OUT_DIR)"
	sha256sum "$(MODEL)" "$(CERT)" "$(CHECKS)"

sign-soft:
	VERIBIOTA_SIG_MODE=signed-soft ../../veribiota --emit-all --out "$(OUT_DIR)" \
	  --sign-key "$$VERIBIOTA_SIG_KEY" --sign-kid "$$VERIBIOTA_SIG_KID"
	sha256sum "$(MODEL)" "$(CERT)" "$(CHECKS)"

verify:
	../../veribiota verify checks "$(CHECKS)" --jwks "$(JWKS)" --print-details
	../../veribiota verify cert   "$(CERT)"   --jwks "$(JWKS)" --print-details

canon:
	../../veribiota --canon "$(CHECKS)" --out "$(CHECKS:.json=.canon.json)"

pilot-demo: emit sign-soft verify
	@echo "Stripe link: $$VERIBIOTA_STRIPE_PILOT_URL"
