import Mathlib.Data.Finsupp.Basic
import Biosim.Core.Reaction

namespace Biosim
namespace Core

universe u

structure System (S : Type u) where
  reactions : List (Reaction S)
  deriving Inhabited

namespace System
variable {S : Type u}

@[simp] lemma reactions_eq (sys : System S) : sys.reactions = sys.reactions := rfl

/-- Reaction `r` is enabled when all required inputs are available in the state. -/
def enabled (x : State S) (r : Reaction S) : Prop :=
  ∀ s, r.inStoich s ≤ x s

/-- Internal helper that removes the consumed inputs from a state. -/
noncomputable def consume (x : State S) (inputs : State S) : State S :=
  Finsupp.zipWith Nat.sub (by simp) x inputs

/-- Consuming then re-adding the inputs recovers the original state. -/
lemma consume_add_inputs (x inputs : State S)
    (h : ∀ s, inputs s ≤ x s) :
    consume x inputs + inputs = x := by
  classical
  ext s
  simp [consume, Finsupp.zipWith_apply, Nat.sub_add_cancel (h s)]

/-- Apply a single reaction once. -/
noncomputable def fire (x : State S) (r : Reaction S) (_h : enabled x r) : State S :=
  consume x r.inStoich + r.outStoich

@[simp]
lemma fire_apply (x : State S) (r : Reaction S) (h : enabled x r) (s : S) :
    fire x r h s = x s - r.inStoich s + r.outStoich s := by
  classical
  simp [fire, consume, Finsupp.zipWith_apply]

/-- Enabled reactions preserve non-negativity coordinate-wise. -/
lemma fire_nonneg (x : State S) (r : Reaction S) (h : enabled x r) :
    ∀ s, 0 ≤ fire x r h s := by
  intro s
  exact Nat.zero_le _

end System

end Core
end Biosim
