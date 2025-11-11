import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Finsupp.Basic
import Biosim.Core.System
import Biosim.Core.Reaction
import Biosim.Proofs.Invariants
import Biosim.Proofs.Positivity
import Biosim.Tactics.Invariant

namespace Biosim
namespace Examples

open Core
open Finsupp

/-- Species for the classical SIR model. -/
inductive SIRSpecies
  | S | I | R
  deriving DecidableEq, Fintype

instance : Core.Species SIRSpecies :=
  { toFintype := inferInstance
    decEq := inferInstance }

/-- Infection reaction: `S + I → 2 I`. For now the rate is a constant placeholder. -/
noncomputable def infection (β : NNReal) : Reaction SIRSpecies :=
  { inStoich := Finsupp.single SIRSpecies.S (1 : ℕ) + Finsupp.single SIRSpecies.I (1 : ℕ)
    , outStoich := Finsupp.single SIRSpecies.I (2 : ℕ)
    , rate := fun _ => β }

/-- Recovery reaction: `I → R`. Rate placeholder set to γ. -/
noncomputable def recovery (γ : NNReal) : Reaction SIRSpecies :=
  { inStoich := Finsupp.single SIRSpecies.I (1 : ℕ)
    , outStoich := Finsupp.single SIRSpecies.R (1 : ℕ)
    , rate := fun _ => γ }

/-- The SIR system consisting of infection and recovery reactions. -/
noncomputable def sirSystem (β γ : NNReal) : System SIRSpecies :=
  { reactions := [infection β, recovery γ] }

/-- State constructor from explicit counts. -/
noncomputable def stateOfCounts (s i r : ℕ) : State SIRSpecies :=
  Finsupp.single SIRSpecies.S s
    + Finsupp.single SIRSpecies.I i
    + Finsupp.single SIRSpecies.R r

@[simp] lemma stateOfCounts_apply_S (s i r : ℕ) :
    stateOfCounts s i r SIRSpecies.S = s := by
  classical
  simp [stateOfCounts, Finsupp.add_apply, add_comm, add_left_comm, add_assoc]

@[simp] lemma stateOfCounts_apply_I (s i r : ℕ) :
    stateOfCounts s i r SIRSpecies.I = i := by
  classical
  simp [stateOfCounts, Finsupp.add_apply, add_comm, add_left_comm, add_assoc]

@[simp] lemma stateOfCounts_apply_R (s i r : ℕ) :
    stateOfCounts s i r SIRSpecies.R = r := by
  classical
  simp [stateOfCounts, Finsupp.add_apply, add_comm, add_left_comm, add_assoc]

/-- Infection requires one susceptible and one infected individual. -/
lemma infection_enabled_of_counts (β : NNReal) {s i r : ℕ} :
    System.enabled (stateOfCounts (s + 1) (i + 1) r) (infection β) := by
  classical
  intro species
  cases species with
  | S =>
      simp [infection, stateOfCounts_apply_S, Nat.succ_le_succ_iff]
  | I =>
      simp [infection, stateOfCounts_apply_I, Nat.succ_le_succ_iff, add_comm]
  | R =>
      simp [infection, stateOfCounts]

/-- Recovery requires one infected individual. -/
lemma recovery_enabled_of_counts (γ : NNReal) {s i r : ℕ} :
    System.enabled (stateOfCounts s (i + 1) r) (recovery γ) := by
  classical
  intro species
  cases species with
  | I =>
      simp [recovery, stateOfCounts_apply_I, Nat.succ_le_succ_iff]
  | S =>
      simp [recovery, stateOfCounts]
  | R =>
      simp [recovery, stateOfCounts]

/-- Uniform weight assigning 1 to every species (total population). -/
noncomputable def totalPopulationInv : Proofs.LinInv SIRSpecies :=
  { w := fun _ => 1 }

@[simp] lemma infection_preserves_total (β : NNReal) :
    Proofs.conservedBy totalPopulationInv (infection β) := by
  classical
  unfold totalPopulationInv infection Proofs.conservedBy Proofs.delta
  have hOut :
      (Finsupp.single SIRSpecies.I (2 : ℕ)).sum
          (fun _ n => (n : ℝ)) = 2 := by simp
  have hInS :
      (Finsupp.single SIRSpecies.S (1 : ℕ)).sum
          (fun _ n => (n : ℝ)) = 1 := by simp
  have hInI :
      (Finsupp.single SIRSpecies.I (1 : ℕ)).sum
          (fun _ n => (n : ℝ)) = 1 := by simp
  have hDisjoint :
      Disjoint (Finsupp.single SIRSpecies.S (1 : ℕ)).support
               (Finsupp.single SIRSpecies.I (1 : ℕ)).support := by
    classical
    simp [Finsupp.support_single_ne_zero]
  have hInTotal :
      (Finsupp.single SIRSpecies.S (1 : ℕ) + Finsupp.single SIRSpecies.I (1 : ℕ)).sum
          (fun _ n => (n : ℝ)) = 2 := by
    classical
    have h :=
      Finsupp.sum_add_index_of_disjoint hDisjoint (fun _ n => (n : ℝ))
    have h' :
        (Finsupp.single SIRSpecies.S (1 : ℕ) + Finsupp.single SIRSpecies.I (1 : ℕ)).sum
            (fun _ n => (n : ℝ))
          = (1 : ℝ) + 1 := by
      simpa [hInS, hInI] using h
    simpa [one_add_one_eq_two] using h'
  simp [hOut, hInTotal]

@[simp] lemma recovery_preserves_total (γ : NNReal) :
    Proofs.conservedBy totalPopulationInv (recovery γ) := by
  classical
  unfold totalPopulationInv recovery Proofs.conservedBy Proofs.delta
  have hOut :
      (Finsupp.single SIRSpecies.R (1 : ℕ)).sum
          (fun _ n => (n : ℝ)) = 1 := by simp
  have hIn :
      (Finsupp.single SIRSpecies.I (1 : ℕ)).sum
          (fun _ n => (n : ℝ)) = 1 := by simp
  simp [hOut, hIn]

/-- Infection preserves non-negativity on concrete count states. -/
lemma infection_fire_nonneg_counts (β : NNReal) (s i r : ℕ) :
    ∀ species,
      0 ≤ System.fire (stateOfCounts (s + 1) (i + 1) r)
        (infection β) (infection_enabled_of_counts (β := β)) species :=
  Proofs.fire_preserves_nonneg _ _ _

/-- Recovery preserves non-negativity on concrete count states. -/
lemma recovery_fire_nonneg_counts (γ : NNReal) (s i r : ℕ) :
    ∀ species,
      0 ≤ System.fire (stateOfCounts s (i + 1) r)
        (recovery γ) (recovery_enabled_of_counts (γ := γ)) species :=
  Proofs.fire_preserves_nonneg _ _ _

end Examples
end Biosim
