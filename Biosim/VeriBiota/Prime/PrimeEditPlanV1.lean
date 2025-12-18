import Biosim.VeriBiota.Edit.EditScriptV1

namespace Biosim
namespace VeriBiota
namespace Prime
namespace PrimeEditPlanV1

open Edit
open EditScriptV1

structure PegRNA where
  spacer : String
  pam : String
  rtTemplate : String
  pbs : String
  deriving Repr, DecidableEq

structure Nick where
  spacer : String
  pam : String
  position : Nat
  deriving Repr, DecidableEq

structure Instance where
  refSeq : String
  targetSeq : String
  pegRNA : PegRNA
  nick? : Option Nick := none
  netEditScript : List EditScriptV1.Edit
  deriving Repr, DecidableEq

def profileId : String := "prime_edit_plan_v1"
def profileVersion : String := "1.0.0"
def coreTheorems : List String := ["VB_PE_001", "VB_EDIT_001"]

private def withinBounds (peg : PegRNA) : Bool :=
  let pbsLen := peg.pbs.length
  let rtLen := peg.rtTemplate.length
  pbsLen ≥ 8 ∧ pbsLen ≤ 20 ∧ rtLen ≥ 10 ∧ rtLen ≤ 80

private def pamAligned (seq spacer pam : String) : Bool :=
  seq.startsWith (spacer ++ pam)

def SpecHolds (inst : Instance) : Prop :=
  EditScriptV1.applyEdits inst.refSeq inst.netEditScript = some inst.targetSeq ∧
    withinBounds inst.pegRNA ∧
    pamAligned inst.refSeq inst.pegRNA.spacer inst.pegRNA.pam ∧
    match inst.nick? with
    | some nick =>
        pamAligned inst.refSeq nick.spacer nick.pam ∧
          nick.position ≤ inst.refSeq.length
    | none => True

def checkInstance (inst : Instance) : Decidable (SpecHolds inst) := by
  unfold SpecHolds
  cases h : inst.nick? <;> (simp [h, withinBounds, pamAligned]; infer_instance)

end PrimeEditPlanV1
end Prime
end VeriBiota
end Biosim
