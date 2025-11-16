ART=build/artifacts
MODEL=$(ART)/models/sir-demo.json
CERT=$(ART)/certificates/sir-demo.json
CHECKS=$(ART)/checks/sir-demo.json
JWKS=security/jwks.json

.PHONY: emit sign-soft verify canon pilot-demo

emit:
	../../veribiota --emit-all --out "$(CURDIR)/$(ART)"
	sha256sum $(MODEL) $(CERT) $(CHECKS)

sign-soft:
	VERIBIOTA_SIG_MODE=signed-soft ../../veribiota --emit-all --out "$(CURDIR)/$(ART)" \
	  --sign-key "$$VERIBIOTA_SIG_KEY" --sign-kid "$$VERIBIOTA_SIG_KID"
	sha256sum $(MODEL) $(CERT) $(CHECKS)

verify:
	../../veribiota verify checks $(CHECKS) --jwks $(JWKS) --print-details
	../../veribiota verify cert   $(CERT)   --jwks $(JWKS) --print-details

canon:
	../../veribiota --canon $(CHECKS) --out $(CHECKS:.json=.canon.json)

pilot-demo: emit sign-soft verify
	@echo "Stripe link: $$VERIBIOTA_STRIPE_PILOT_URL"
