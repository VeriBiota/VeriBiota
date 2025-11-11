# Linear Invariants

Lean treats invariants as weighted sums over finitely supported states. The helper tactic `Invariant.lin.auto` normalizes the stoichiometry of a reaction, builds the net `out - in` vector, and discharges the resulting arithmetic equality with `simp` + `ring`.

```lean
import Biosim.Examples.SIR
import Biosim.Tactics.Invariant

open Biosim.Examples

example (β : NNReal) :
    Biosim.Proofs.conservedBy Examples.totalPopulationInv (Examples.infection β) := by
  classical
  unfold Examples.totalPopulationInv Examples.infection
  Invariant.lin.auto
```

## Fire semantics + invariants

`Biosim.Proofs.weight_fire_eq` shows how a single fired reaction shifts the weighted sum by its delta:

```lean
open Biosim
open Biosim.Proofs

variable {S : Type} [Core.Species S]

theorem weight_after_fire
    (w : LinInv S) (x : Core.State S) (r : Core.Reaction S)
    (h : Core.System.enabled x r) :
    weight w (Core.System.fire x r h)
      = weight w x + delta w r := weight_fire_eq _ _ _ _
```

When `delta w r = 0` (proved via `Invariant.lin.auto`), firing preserves the invariant:

```lean
theorem preserves_mass
    (w : LinInv S) (x : Core.State S) (r : Core.Reaction S)
    (h : Core.System.enabled x r)
    (hc : conservedBy w r) :
    weight w (Core.System.fire x r h) = weight w x :=
  fire_preserves_weight _ _ _ h hc
```

See `Biosim/Examples/SIR.lean` for a complete worked example where the total population
`S + I + R` stays constant for both infection and recovery reactions.
