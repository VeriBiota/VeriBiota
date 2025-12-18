import Mathlib

namespace Biosim
namespace VeriBiota
namespace Alignment
namespace GlobalAffineV1

/-- Scoring scheme for global affine alignment. -/
structure Scoring where
  matchScore : Int
  mismatch   : Int
  gapOpen    : Int
  gapExtend  : Int
  deriving Repr, DecidableEq

/-- Trace operations recorded by an aligner. -/
inductive TraceOp where
  | M  -- match/mismatch
  | I  -- insertion (gap in `seqA`)
  | D  -- deletion  (gap in `seqB`)
  deriving Repr, DecidableEq

/-- Witness supplied by an implementation under test. -/
structure Witness where
  score  : Int
  trace  : List TraceOp
  deriving Repr, DecidableEq

/-- Concrete alignment instance for the `global_affine_v1` profile. -/
structure Instance where
  seqA    : String
  seqB    : String
  scoring : Scoring
  witness : Witness
  deriving Repr, DecidableEq

/-- Stable profile identifier used on the CLI/API surface. -/
def profileId : String := "global_affine_v1"

/-- Theorem anchors advertised to callers. -/
def coreTheorems : List String :=
  ["VB_ALIGN_CORE_001", "VB_ALIGN_CORE_002"]

private def negInf : Int := -1000000000000000 -- sentinel for impossible states

private def max3 (a b c : Int) : Int :=
  max a (max b c)

private def prefixGapScore (len : Nat) (s : Scoring) : Int :=
  match len with
  | 0 => negInf
  | Nat.succ k => s.gapOpen + s.gapExtend * Int.ofNat k

/-- Score a concrete witness trace against the provided sequences/scoring. -/
def scoreTrace (seqA seqB : String) (scoring : Scoring) (trace : List TraceOp) :
    Except String Int := do
  let a := seqA.data
  let b := seqB.data
  let rec loop (ia ib : Nat) (prev? : Option TraceOp) (acc : Int)
      : List TraceOp → Except String (Nat × Nat × Int)
    | [] => pure (ia, ib, acc)
    | TraceOp.M :: rest =>
        match a.get? ia, b.get? ib with
        | some ca, some cb =>
            let delta := if ca = cb then scoring.matchScore else scoring.mismatch
            loop (ia + 1) (ib + 1) none (acc + delta) rest
        | _, _ =>
            throw s!"trace matches beyond input length (a={ia}/{a.length}, b={ib}/{b.length})"
    | TraceOp.I :: rest =>
        match b.get? ib with
        | none =>
            throw s!"trace inserts beyond end of seqB (idx {ib}, len {b.length})"
        | some _ =>
            let gap :=
              match prev? with
              | some TraceOp.I => scoring.gapExtend
              | _ => scoring.gapOpen
            loop ia (ib + 1) (some TraceOp.I) (acc + gap) rest
    | TraceOp.D :: rest =>
        match a.get? ia with
        | none =>
            throw s!"trace deletes beyond end of seqA (idx {ia}, len {a.length})"
        | some _ =>
            let gap :=
              match prev? with
              | some TraceOp.D => scoring.gapExtend
              | _ => scoring.gapOpen
            loop (ia + 1) ib (some TraceOp.D) (acc + gap) rest
  let (ia, ib, total) ← loop 0 0 none 0 trace
  if ia = a.length ∧ ib = b.length then
    pure total
  else
    throw s!"trace did not consume all input (a={ia}/{a.length}, b={ib}/{b.length})"

/-- DP row for affine gap alignment (per-column scores for each state). -/
structure DPRow where
  m : Array Int
  i : Array Int
  d : Array Int

private def initRow (bLen : Nat) (scoring : Scoring) : DPRow := Id.run do
  let mut mRow := Array.mkArray (bLen + 1) negInf
  let mut iRow := Array.mkArray (bLen + 1) negInf
  let mut dRow := Array.mkArray (bLen + 1) negInf
  mRow := mRow.set! 0 0
  let mut current := scoring.gapOpen
  for j in List.range bLen do
    let idx := j + 1
    iRow := iRow.set! idx current
    current := current + scoring.gapExtend
  pure { m := mRow, i := iRow, d := dRow }

private def nextRow (iPrefix : Nat) (a : Char) (bArr : Array Char) (scoring : Scoring)
    (prev : DPRow) : DPRow := Id.run do
  let bLen := bArr.size
  let mut mRow := Array.mkArray (bLen + 1) negInf
  let mut iRow := Array.mkArray (bLen + 1) negInf
  let mut dRow := Array.mkArray (bLen + 1) negInf
  let leading := prefixGapScore iPrefix scoring
  dRow := dRow.set! 0 leading
  for j in List.range bLen do
    let col := j + 1
    let b := bArr.get! j
    let matchScore := if a = b then scoring.matchScore else scoring.mismatch
    let matchBase := max3 (prev.m.get! j) (prev.i.get! j) (prev.d.get! j)
    mRow := mRow.set! col (matchBase + matchScore)
    let iVal := max3
      (mRow.get! (col - 1) + scoring.gapOpen)
      (iRow.get! (col - 1) + scoring.gapExtend)
      (dRow.get! (col - 1) + scoring.gapOpen)
    iRow := iRow.set! col iVal
    let dVal := max3
      (prev.m.get! col + scoring.gapOpen)
      (prev.d.get! col + scoring.gapExtend)
      (prev.i.get! col + scoring.gapOpen)
    dRow := dRow.set! col dVal
  pure { m := mRow, i := iRow, d := dRow }

/-- Specification score for global affine alignment using a simple DP. -/
def specGlobalAffine (seqA seqB : String) (scoring : Scoring) : Int :=
  let aArr := seqA.data.toArray
  let bArr := seqB.data.toArray
  let init := initRow bArr.size scoring
  let finalRow :=
    Id.run <| do
      let mut row := init
      for idx in List.range aArr.size do
        let a := aArr.get! idx
        row := nextRow (idx + 1) a bArr scoring row
      pure row
  let n := bArr.size
  max3 (finalRow.m.get! n) (finalRow.i.get! n) (finalRow.d.get! n)

/-- Profile property: the witness trace matches the spec DP score. -/
def SpecHolds (inst : Instance) : Prop :=
  scoreTrace inst.seqA inst.seqB inst.scoring inst.witness.trace =
      Except.ok inst.witness.score ∧
    specGlobalAffine inst.seqA inst.seqB inst.scoring = inst.witness.score

/-- Decider used by the CLI/API surface. -/
def checkInstance (inst : Instance) : Decidable (SpecHolds inst) := by
  unfold SpecHolds
  cases hTrace : scoreTrace inst.seqA inst.seqB inst.scoring inst.witness.trace with
  | ok traceScore =>
      simpa [hTrace] using
        (inferInstance :
          Decidable (traceScore = inst.witness.score ∧
            specGlobalAffine inst.seqA inst.seqB inst.scoring = inst.witness.score))
  | error _ =>
      exact isFalse (by intro h; cases h.left)

end GlobalAffineV1
end Alignment
end VeriBiota
end Biosim
