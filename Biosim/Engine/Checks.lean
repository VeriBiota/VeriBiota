import Biosim.IO.Checks

namespace Biosim
namespace Engine
namespace Checks
open Biosim.IO

/-- Snapshot of engine state for runtime check evaluation. -/
structure Snapshot where
  values : List (String × Float)
  deriving Inhabited

namespace Snapshot

def ofList (entries : List (String × Float)) : Snapshot :=
  { values := entries }

def lookup (snap : Snapshot) (species : String) : Float :=
  match snap.values.find? (fun entry => entry.1 = species) with
  | some (_, value) => value
  | none => 0.0

end Snapshot

structure EvalResult where
  maxDrift : Float := 0.0
  violated? : Bool := false
  firstViolationIdx? : Option Nat := none
  deriving Repr

structure RuntimeConfig where
  linearBaselines : List (String × Float) := []

namespace RuntimeConfig

def lookup (cfg : RuntimeConfig) (name : String) : Float :=
  match cfg.linearBaselines.find? (fun p => p.1 = name) with
  | some (_, value) => value
  | none => 0.0

end RuntimeConfig

private def positivityCountsEval (species : List String) (snapshots : List Snapshot) :
    EvalResult :=
  let rec loop
      | _, [] => { maxDrift := 0.0, violated? := false, firstViolationIdx? := none }
      | idx, snap :: rest =>
          if species.all (fun s => snap.lookup s ≥ 0.0) then
            loop (idx + 1) rest
          else
            { violated? := true, firstViolationIdx? := some idx }
  loop 0 snapshots

private def positivityConcEval (species : List String) (tol : Float)
    (snapshots : List Snapshot) : EvalResult :=
  let rec loop
      | _, [] => { maxDrift := 0.0, violated? := false, firstViolationIdx? := none }
      | idx, snap :: rest =>
          if species.all (fun s => snap.lookup s ≥ -tol) then
            loop (idx + 1) rest
          else
            { violated? := true, firstViolationIdx? := some idx }
  loop 0 snapshots

private def linearThreshold (tol : IO.Checks.Tolerance)
    (baseline : Float) (drift : Float) : Bool :=
  match tol.mode with
  | IO.Checks.ToleranceMode.absolute => drift ≤ tol.value
  | IO.Checks.ToleranceMode.relative =>
      let ref := Float.abs baseline
      drift ≤ ref * tol.value

private def weightDot (weights : List (String × Int)) (snap : Snapshot) : Float :=
  weights.foldl
    (fun acc (species, coeff) =>
      acc + Float.ofInt coeff * snap.lookup species) 0.0

private def linearEval (spec : IO.Checks.LinearInvariantSpec) (baseline : Float)
    (snapshots : List Snapshot) : EvalResult :=
  let rec loop
      | _, [], maxDrift, first? => { maxDrift, violated? := first?.isSome, firstViolationIdx? := first? }
      | idx, snap :: rest, maxDrift, first? =>
          let value := weightDot spec.weights snap
          let drift := Float.abs (value - baseline)
          let maxDrift := if drift > maxDrift then drift else maxDrift
          let within := linearThreshold spec.tolerance baseline drift
          let first? :=
            match first? with
            | some n => some n
            | none => if within then none else some idx
          loop (idx + 1) rest maxDrift first?
  loop 0 snapshots 0.0 none

def evaluate (cfg : RuntimeConfig) (check : IO.Checks.Check)
    (snapshots : List Snapshot) : EvalResult :=
  match check.normalize with
  | IO.Checks.Check.positivityCounts spec =>
      positivityCountsEval spec.species snapshots
  | IO.Checks.Check.positivityConcentration spec =>
      positivityConcEval spec.species spec.tolerance snapshots
  | IO.Checks.Check.linearInvariant spec =>
      let baseline := cfg.lookup spec.name
      linearEval spec baseline snapshots

end Checks
end Engine
end Biosim
