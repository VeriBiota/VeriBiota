import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic.Ring
import Biosim.Core.System

set_option linter.unnecessarySimpa false

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
lemma delta_eq_weight_diff (w : LinInv S) (r : Reaction S) :
    delta w r = weight w r.outStoich - weight w r.inStoich := rfl

/-- A reaction preserves the invariant when the weighted net change is zero. -/
def conservedBy (w : LinInv S) (r : Reaction S) : Prop :=
  delta w r = 0

/-- Weight of the consumed portion equals the original weight minus the inputs. -/
lemma weight_consume (w : LinInv S) (x inputs : State S)
    (h : ∀ s, inputs s ≤ x s) :
    weight w (System.consume x inputs)
      = weight w x - weight w inputs := by
  classical
  have hEq :=
    congrArg (weight w) (System.consume_add_inputs x inputs h)
  simp [weight_add, add_comm, add_left_comm, add_assoc] at hEq
  have hSum :
      weight w (System.consume x inputs) + weight w inputs = weight w x := by
    simpa [add_comm] using hEq
  exact (eq_sub_of_add_eq hSum)

/-- Firing a reaction shifts the weight by the reaction's delta. -/
lemma weight_fire_eq (w : LinInv S) (x : State S) (r : Reaction S)
    (h : System.enabled x r) :
    weight w (System.fire x r h)
      = weight w x + (delta w r) := by
  classical
  have hConsume :
      weight w (System.consume x r.inStoich)
        = weight w x - weight w r.inStoich :=
    weight_consume w x r.inStoich (fun s => h s)
  have hFire :
      weight w (System.fire x r h)
        = weight w (System.consume x r.inStoich) + weight w r.outStoich := by
    simp [System.fire, weight_add]
  have hCombined :
      weight w (System.fire x r h)
        = weight w x - weight w r.inStoich + weight w r.outStoich := by
    have hTmp := hFire
    simp [hConsume] at hTmp
    exact hTmp
  have rearr :
      weight w x - weight w r.inStoich + weight w r.outStoich
        = weight w x + (weight w r.outStoich - weight w r.inStoich) := by
    ring
  have hDeltaExpr :
      weight w (System.fire x r h)
        = weight w x + (weight w r.outStoich - weight w r.inStoich) := by
    have hTmp := hCombined
    simp [rearr] at hTmp
    exact hTmp
  have hFinal :
      weight w (System.fire x r h)
        = weight w x + delta w r := by
    calc
      weight w (System.fire x r h)
          = weight w x + (weight w r.outStoich - weight w r.inStoich) := hDeltaExpr
      _ = weight w x + delta w r := by
        simpa using
          congrArg (fun t => weight w x + t)
            ((delta_eq_weight_diff (w := w) (r := r)).symm)
  exact hFinal

/-- Enabled reactions preserve a linear invariant when `delta = 0`. -/
lemma fire_preserves_weight (w : LinInv S) (x : State S)
    (r : Reaction S) (h : System.enabled x r)
    (hc : conservedBy w r) :
    weight w (System.fire x r h) = weight w x := by
  classical
  have hfire := weight_fire_eq (w := w) (x := x) (r := r) h
  have hdelta : delta w r = 0 := hc
  simpa [hdelta] using hfire

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
