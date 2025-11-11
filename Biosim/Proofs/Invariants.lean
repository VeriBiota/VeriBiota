import Mathlib.Data.Finsupp.Basic
import Biosim.Core.System

namespace Biosim
namespace Proofs

open Core
open scoped BigOperators

universe u

structure LinInv (S : Type u) where
  w : S → ℝ

variable {S : Type u} [Core.Species S]

open Finset

/-- Weighted sum of a state with respect to a linear invariant. -/
noncomputable def weight (w : LinInv S) (x : State S) : ℝ :=
  x.sum fun s n => w.w s * (n : ℝ)

/-- Weight of a singleton state simplifies to `w s * n`. -/
@[simp] lemma weight_single (w : LinInv S) (s : S) (n : ℕ) :
    weight w (Finsupp.single s n) = w.w s * (n : ℝ) := by
  classical
  simp [weight]

/-- `weight` is additive on states. -/
@[simp] lemma weight_add (w : LinInv S) (x y : State S) :
    weight w (x + y) = weight w x + weight w y := by
  classical
  simpa [weight, add_comm, add_left_comm, add_assoc] using
    (Finsupp.sum_add_index'
      (fun _ => by simp)
      (fun _ => by
        intro a b
        simp [Nat.cast_add, mul_add, add_comm, add_left_comm, add_assoc])
      : _)

/-- Weighted difference between the outputs and inputs of a reaction. -/
noncomputable def delta (w : LinInv S) (r : Reaction S) : ℝ :=
  (r.outStoich.sum fun s n => w.w s * (n : ℝ))
    - (r.inStoich.sum fun s n => w.w s * (n : ℝ))

/-- Convenience rewrite for `delta`. -/
@[simp] lemma delta_eq_weight_diff (w : LinInv S) (r : Reaction S) :
    delta w r = weight w r.outStoich - weight w r.inStoich := rfl

/-- A reaction preserves the invariant when the weighted net change is zero. -/
def conservedBy (w : LinInv S) (r : Reaction S) : Prop :=
  delta w r = 0

@[simp] lemma weight_zero (w : LinInv S) : weight w (0 : State S) = 0 := by
  classical
  simp [weight]

@[simp] lemma conservedBy_iff (w : LinInv S) (r : Reaction S) :
    conservedBy w r ↔ weight w r.outStoich = weight w r.inStoich := by
  classical
  unfold conservedBy
  constructor <;> intro h
  · exact sub_eq_zero.mp h
  · exact sub_eq_zero.mpr h

/-- Stub lemma kept for compatibility. -/
lemma preserved_step (w : LinInv S) (r : Reaction S)
    (h : conservedBy w r) : conservedBy w r := h

end Proofs
end Biosim
