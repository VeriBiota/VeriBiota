import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Biosim.Proofs.Invariants

open Lean Parser Tactic Elab Tactic

-- NOTE: Lean treats dotted identifiers as hierarchical names, so the tactic
-- surface form uses an underscore even though user documentation refers to
-- `conservation.auto`.
syntax (name := conservationAuto) "conservation_auto" : tactic
syntax (name := invariantLinCmd) "Invariant.lin" : tactic
syntax (name := invariantLinLegacyCmd) "invariant_lin" : tactic

namespace Biosim
namespace Tactics
namespace Invariant

/-- Simple automation for linear invariants: expand definitions and simplify. -/
@[tactic conservationAuto] def evalConservationAuto : Tactic := fun _ => do
  Lean.Meta.withTransparency Lean.Meta.TransparencyMode.reducible do
    evalTactic <|
      ← `(tactic|
        (classical
          (simp (config := { decide := true })
            [Proofs.conservedBy, Proofs.delta, Proofs.weight,
             Finsupp.single, Finsupp.add_apply, Finsupp.sum, Finsupp.sum_single_index,
             Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul,
             Nat.cast_add, Nat.cast_ofNat, mul_add, add_mul,
             sub_eq_add_neg] <;> try norm_num)))

@[tactic invariantLinCmd] def evalInvariantLinAlias : Tactic :=
  evalConservationAuto

@[tactic invariantLinLegacyCmd] def evalInvariantLegacyAlias : Tactic :=
  evalConservationAuto

namespace Presets

open Biosim.Proofs

variable {S : Type u} [Core.Species S]

private def sumWeight (pairs : List (S × ℚ)) (target : S) : ℚ :=
  pairs.foldl
    (fun acc (species, w) =>
      if species = target then acc + w else acc)
    0

/-- Total-mass invariant assigning weight `1` to every species. -/
def total : LinInv S :=
  { w := fun _ => (1 : ℝ) }

/-- Custom mass invariant built from rational weights (duplicates coalesced, zeros dropped). -/
def mass (pairs : List (S × ℚ)) : LinInv S :=
  { w := fun s => ((sumWeight pairs s : ℚ) : ℝ) }

end Presets

end Invariant
end Tactics
end Biosim
