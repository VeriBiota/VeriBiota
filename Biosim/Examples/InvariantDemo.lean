import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Finsupp.Basic
import Biosim.Core.Reaction
import Biosim.Proofs.Invariants
import Biosim.Tactics.Invariant

namespace Biosim
namespace Examples
namespace InvariantDemo

open Core
open Finsupp

inductive TwoSpecies
  | A | B
  deriving DecidableEq, Fintype

instance : Core.Species TwoSpecies :=
  { toFintype := inferInstance
    decEq := inferInstance }

noncomputable def idleReaction : Reaction TwoSpecies :=
  { inStoich := Finsupp.single TwoSpecies.A (1 : ℕ)
    , outStoich := Finsupp.single TwoSpecies.A (1 : ℕ)
    , rate := fun _ => (0 : NNReal) }

noncomputable def unitWeight : Proofs.LinInv TwoSpecies :=
  { w := fun _ => 1 }

lemma idle_conserves_total :
    Proofs.conservedBy unitWeight idleReaction := by
  classical
  unfold unitWeight idleReaction Proofs.conservedBy Proofs.delta
  conservation_auto

end InvariantDemo
end Examples
end Biosim
