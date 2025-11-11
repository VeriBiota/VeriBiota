import Mathlib.Data.Fintype.Card

namespace Biosim
namespace Core

universe u

/-- Finite species live in enumerated types with decidable equality.
The `fintype` field exposes the enumeration for downstream bounds. -/
class Species (α : Type u) extends Fintype α where
  decEq : DecidableEq α

attribute [instance] Species.decEq

/-- Cardinality helper for species types. -/
noncomputable def speciesCount (S : Type u) [Species S] : Nat :=
  Fintype.card S

end Core
end Biosim
