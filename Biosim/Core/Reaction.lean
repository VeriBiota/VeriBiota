import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.NNReal.Basic
import Biosim.Core.State
import Biosim.Core.Stoich

namespace Biosim
namespace Core

universe u

structure Reaction (S : Type u) where
  inStoich  : State S
  outStoich : State S
  rate      : State S → NNReal

noncomputable def Reaction.net {S : Type u} (r : Reaction S) : Stoich S :=
  Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) r.outStoich
    - Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) r.inStoich

end Core
end Biosim
