import Mathlib.Tactic.DeriveFintype
import Biosim.Core.System

namespace Biosim
namespace Examples

open Core

inductive GRNSpecies
  | A | B
  deriving DecidableEq, Fintype

instance : Core.Species GRNSpecies :=
  { toFintype := inferInstance
    decEq := inferInstance }

/-- Placeholder toggle-switch system awaiting reactions. -/
def grnSystem : System GRNSpecies where
  reactions := []

end Examples
end Biosim
