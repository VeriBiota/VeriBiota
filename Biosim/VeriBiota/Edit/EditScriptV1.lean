import Mathlib

namespace Biosim
namespace VeriBiota
namespace Edit
namespace EditScriptV1

inductive EditType where
  | ins
  | del
  | sub
  deriving Repr, DecidableEq

structure Edit where
  type    : EditType
  pos     : Nat
  len     : Nat := 0
  payload : String := ""
  deriving Repr, DecidableEq

structure Instance where
  seqA  : String
  seqB  : String
  edits : List Edit
  deriving Repr, DecidableEq

def profileId : String := "edit_script_v1"
def profileVersion : String := "1.0.0"
def coreTheorems : List String := ["VB_EDIT_001"]

def splice (s : List Char) (pos : Nat) (takeLen : Nat) (insert : List Char) :
    Option (List Char) := do
  if pos > s.length then
    none
  else if pos + takeLen > s.length then
    none
  else
    pure (s.take pos ++ insert ++ s.drop (pos + takeLen))

def applyEdit (s : String) (e : Edit) : Option String :=
  let chars := s.data
  match e.type with
  | EditType.ins =>
      splice chars e.pos 0 e.payload.data |>.map String.mk
  | EditType.del =>
      if e.len = 0 then none
      else splice chars e.pos e.len [] |>.map String.mk
  | EditType.sub =>
      if e.len = 0 then none
      else splice chars e.pos e.len e.payload.data |>.map String.mk

def applyEdits (s : String) (es : List Edit) : Option String :=
  es.foldlM (fun acc e => applyEdit acc e) s

theorem applyEdits_append (s : String) (xs ys : List Edit) :
    applyEdits s (xs ++ ys) = (applyEdits s xs) >>= fun s' => applyEdits s' ys := by
  simp [applyEdits, List.foldlM_append]

def SpecHolds (inst : Instance) : Prop :=
  applyEdits inst.seqA inst.edits = some inst.seqB

def checkInstance (inst : Instance) : Decidable (SpecHolds inst) := by
  unfold SpecHolds
  infer_instance

end EditScriptV1
end Edit
end VeriBiota
end Biosim
