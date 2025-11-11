import Mathlib.Data.NNReal.Basic

namespace Biosim
namespace Semantics

universe u

/-- Minimal placeholder for jump steps; future work will enrich this record. -/
structure JumpStep (S : Type u) where
  τ : NNReal

namespace JumpStep

variable {S : Type u}

@[simp]
lemma tau_nonneg (step : JumpStep S) : 0 ≤ step.τ :=
  step.τ.property

end JumpStep

end Semantics
end Biosim
