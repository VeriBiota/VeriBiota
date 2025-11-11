import Biosim.Core.System

namespace Biosim
namespace Proofs

open Core

universe u

variable {S : Type u}

lemma fire_preserves_nonneg (x : State S) (r : Reaction S)
    (h : System.enabled x r) : ∀ s, 0 ≤ System.fire x r h s :=
  System.fire_nonneg x r h

end Proofs
end Biosim
