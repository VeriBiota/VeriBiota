import Mathlib.Tactic.DeriveFintype
import Biosim.Core.System

namespace Biosim
namespace Examples

open Core

inductive BirthDeathSpecies
  | X
  deriving DecidableEq, Fintype

instance : Core.Species BirthDeathSpecies :=
  { toFintype := inferInstance
    decEq := inferInstance }

/-- Placeholder birth-death system (no reactions yet). -/
def birthDeathSystem : System BirthDeathSpecies where
  reactions := []

end Examples
end Biosim
