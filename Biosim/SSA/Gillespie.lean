import Mathlib.Data.NNReal.Basic
import Biosim.Core.System

namespace Biosim
namespace SSA

open Core

universe u

structure Kernel (S : Type u) where
  sys : System S
  step : State S → State S → NNReal

/-- Placeholder property describing normalization. -/
def isProbabilityKernel {S : Type u} (K : Kernel S) : Prop :=
  ∀ x, K.step x x = 1

end SSA
end Biosim
