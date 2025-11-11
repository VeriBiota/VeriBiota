# QA Checklist (v0.1.0)

Run these before sending any pilot deliverable or cutting a release tag.

1. **Determinism matrix** – GitHub Actions (ubuntu + mac) passes; manually double-check `diff` on two `make emit` runs.
2. **AJV validation** – `npx ajv-cli validate -s schema/veribiota.checks.v1.json -d build/artifacts/checks/*.json` and `npx ajv-cli validate -s schema/veribiota.certificate.v1.json -d build/artifacts/certificates/*.json`.
3. **Tamper harness** – `tests/scripts/tamper.sh` returns exit code 3 for payload flip, 2 for signature flip; missing signature in enforced mode → 5; canonicalization mismatch → 4.
4. **CRLF normalization** – `veribiota --canon <file>` removes CRLF and reproduces byte-identical payload.
5. **pilot_demo.sh** – prints SHA lines and `veribiota verify … --print-details` output.
6. **Release assets** – `releases/pilot-demo-v1` contains the latest artifacts, sidecars, JWKS sample, and README.
7. **Tag** – `git tag v0.1.0 && git push origin v0.1.0` once everything above is green.
