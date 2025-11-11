---
id: "biosim_cli_docs"
title: "Document biosim CLI + artifact workflow"
kind: "doc"
needs: ["biosim_certificate_pipeline"]
outputs:
  - path: "README.md"
  - path: "docs/cli.md"
acceptance:
  done_when:
    - "README Demo Artifacts section describes model/certificate generation"
    - "docs/cli.md covers running `./veribiota …` and inspecting outputs"
    - "Instructions emphasize not committing `.lake/` artifacts"
tools_allowed: []
time_budget_minutes: 60
status: "in_progress"
---
