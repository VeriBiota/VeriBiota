import Mathlib.Data.Finsupp.Basic
import Biosim.Core.Species
import Biosim.Core.State

namespace Biosim
namespace Core

universe u

abbrev Stoich (S : Type u) := S →₀ ℤ

variable {S : Type u}

/-- Convert a stoichiometric map to an integer vector function. -/
noncomputable def applyStoich (Δ : Stoich S) (x : State S) : Stoich S :=
  Δ + Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) x

end Core
end Biosim
