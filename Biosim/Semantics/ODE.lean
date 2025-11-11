import Mathlib.Data.Finsupp.Basic
import Mathlib.Topology.Instances.Real
import Biosim.Core.System

namespace Biosim
namespace Semantics

open Core

universe u

variable {S : Type u}

/-- Deterministic vector field assembled from a system's reactions. -/
def vectorField (sys : System S) (rate : Reaction S → (S → ℝ) → ℝ)
    (x : S → ℝ) (s : S) : ℝ :=
  (sys.reactions.map fun r =>
      rate r x * ((r.outStoich s : ℝ) - (r.inStoich s : ℝ))).sum

end Semantics
end Biosim
