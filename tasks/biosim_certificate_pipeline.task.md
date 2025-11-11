---
id: "biosim_certificate_pipeline"
title: "Certificate + model artifact pipeline"
kind: "code"
owner: "auto"
needs: ["biosim_core_invariants"]
inputs:
  - path: "Biosim/IO/Certificate.lean"
  - path: "Biosim/IO/Model.lean"
  - path: "Biosim/Examples/CertificateDemo.lean"
outputs:
  - path: "artifacts/certificates/sir-demo.json"
  - path: "artifacts/models/sir-demo.json"
acceptance:
  done_when:
    - "`./veribiota --emit-all` emits both model and certificate JSON"
    - "Certificate references the hashed model artifact"
    - "README includes instructions for regenerating artifacts"
    - "No build artifacts larger than 100MB are committed"
tools_allowed: ["build"]
time_budget_minutes: 120
status: "in_progress"
---
