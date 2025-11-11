---
id: "biosim_model_ir"
title: "Model IR serialization & importer scaffold"
kind: "code"
needs: ["biosim_certificate_pipeline"]
outputs:
  - path: "Biosim/IO/Model.lean"
  - path: "Biosim/Examples/Model/SIR.lean"
  - path: "docs/model-ir.md"
acceptance:
  done_when:
    - "Model IR types encode meta/species/reactions/rate laws"
    - "`Biosim/Examples/Model/SIR.lean` round-trips to JSON via helper"
    - "Doc explains the schema and hashing rules"
    - "Importer stub/API is ready for JSON → Lean conversion"
tools_allowed: ["build"]
time_budget_minutes: 180
status: "todo"
---
