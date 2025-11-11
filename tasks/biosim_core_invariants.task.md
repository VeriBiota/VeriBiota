---
id: "biosim_core_invariants"
title: "Harden SIR invariants & positivity proofs"
kind: "code"
owner: "auto"
inputs:
  - path: "Biosim/Examples/SIR.lean"
  - path: "Biosim/Proofs/Invariants.lean"
  - path: "Biosim/Tactics/Invariant.lean"
outputs:
  - path: "Biosim/Examples/SIR.lean"
  - path: "Biosim/Proofs/Invariants.lean"
  - path: "Biosim/Tactics/Invariant.lean"
acceptance:
  done_when:
    - "SIR example proves total-population conservation via shared lemmas"
    - "Positivity lemmas exist for enabled infection/recovery steps"
    - "Invariant tactic closes all SIR invariant goals without manual arithmetic"
tools_allowed: ["build"]
time_budget_minutes: 120
status: "in_progress"
---
