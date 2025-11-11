import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.NNReal.Basic
import Biosim.Core.Species

namespace Biosim
namespace Core

universe u

abbrev State (S : Type u) := S →₀ ℕ
abbrev ContinuousState (S : Type u) := S →₀ NNReal

variable {S : Type u}

/-- Total mass/count of a discrete state. -/
noncomputable def total (x : State S) : Nat :=
  x.sum fun _ n => n

@[simp]
lemma total_zero : total (0 : State S) = 0 := by
  classical
  simp [total]

/-- Cast a discrete state into a nonnegative real vector. -/
noncomputable def toNNRealState (x : State S) : ContinuousState S :=
  Finsupp.mapRange (fun n : ℕ => (n : NNReal)) (by simp) x

end Core
end Biosim
