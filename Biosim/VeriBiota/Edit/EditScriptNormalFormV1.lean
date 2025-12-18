import Biosim.VeriBiota.Edit.EditScriptV1

namespace Biosim
namespace VeriBiota
namespace Edit
namespace EditScriptNormalFormV1

open EditScriptV1

structure Instance where
  seqA : String
  seqB : String
  edits : List Edit
  normalizedEdits? : Option (List Edit) := none
  deriving Repr, DecidableEq

def profileId : String := "edit_script_normal_form_v1"
def profileVersion : String := "1.0.0"
def coreTheorems : List String := ["VB_EDIT_001", "VB_EDIT_002"]

def mergeEdits (a b : Edit) : Option Edit :=
  if a.type ≠ b.type then
    none
  else
    match a.type with
    | EditType.sub =>
        -- Only merge length-preserving substitutions, so normalization is semantics-preserving
        -- under the sequential `applyEdits` semantics.
        if a.len > 0 ∧ b.len > 0 ∧ a.payload.length = a.len ∧ b.payload.length = b.len ∧ a.pos + a.len = b.pos then
          some { a with len := a.len + b.len, payload := a.payload ++ b.payload }
        else
          none
    | EditType.del =>
        -- Under sequential semantics, two deletions are mergeable iff they delete from the same
        -- position in the evolving string.
        if a.len > 0 ∧ b.len > 0 ∧ a.pos = b.pos then
          some { a with len := a.len + b.len }
        else
          none
    | EditType.ins =>
        let payloadLen := a.payload.length
        if b.pos = a.pos then
          -- Later insertions at the same position occur before earlier insertions.
          some { a with payload := b.payload ++ a.payload }
        else if b.pos = a.pos + payloadLen then
          some { a with payload := a.payload ++ b.payload }
        else
          none

def normalizeScriptAcc : List Edit → List Edit → List Edit
  | acc, [] => acc.reverse
  | [], e :: es => normalizeScriptAcc [e] es
  | h :: t, e :: es =>
      match mergeEdits h e with
      | some merged => normalizeScriptAcc (merged :: t) es
      | none => normalizeScriptAcc (e :: h :: t) es

def normalizeScript (edits : List Edit) : List Edit :=
  normalizeScriptAcc [] edits

def NoMergeRel (a b : Edit) : Prop :=
  mergeEdits a b = none

def NoMergeAdj (edits : List Edit) : Prop :=
  List.Chain' NoMergeRel edits

def AccNoMerge (acc : List Edit) : Prop :=
  List.Chain' (fun a b => NoMergeRel b a) acc

theorem accNoMerge_nil : AccNoMerge ([] : List Edit) := by
  simp [AccNoMerge, NoMergeRel]

private theorem getLast?_eq_head?_reverse {α : Type} :
    ∀ l : List α, l.getLast? = l.reverse.head?
  | [] => by simp
  | [a] => by simp
  | a :: b :: t => by
      have ih := getLast?_eq_head?_reverse (b :: t)
      calc
        (a :: b :: t).getLast? = (b :: t).getLast? := by simp [List.getLast?_cons_cons]
        _ = (b :: t).reverse.head? := ih
        _ = (a :: b :: t).reverse.head? := by
            have hne2 : (t.reverse ++ [b]) ≠ ([] : List α) := by
              simp
            have hHead :
                ((t.reverse ++ [b]) ++ [a]).head? = (t.reverse ++ [b]).head? := by
              simpa using
                (List.head?_append_of_ne_nil (l₁ := t.reverse ++ [b]) (l₂ := [a]) hne2)
            have : (t.reverse ++ [b]).head? = (t.reverse ++ [b, a]).head? := by
              simpa [List.append_assoc] using hHead.symm
            simpa [List.reverse_cons, List.append_assoc] using this

theorem mergeEdits_prev_none_of_merge (prev a b merged : Edit) :
    mergeEdits prev a = none →
      mergeEdits a b = some merged →
        mergeEdits prev merged = none := by
  intro hPrev hMerge
  cases aTy : a.type with
  | ins =>
      cases bTy : b.type with
      | ins =>
          by_cases hb0 : b.pos = a.pos
          ·
            have hEq : merged = { a with payload := b.payload ++ a.payload } := by
              apply Eq.symm
              apply Option.some.inj
              simpa [mergeEdits, aTy, bTy, hb0] using hMerge
            have hMergedTy : merged.type = EditType.ins := by
              simp [hEq, aTy]
            have hMergedPos : merged.pos = a.pos := by
              simp [hEq]
            cases prevTy : prev.type
            · -- prev ins
              have hPos0 : a.pos ≠ prev.pos := by
                intro hEqPos
                have : mergeEdits prev a ≠ none := by
                  simp [mergeEdits, prevTy, aTy, hEqPos]
                exact this hPrev
              have hPos1 : a.pos ≠ prev.pos + prev.payload.length := by
                intro hEqPos
                have hLen : prev.payload.length ≠ 0 := by
                  intro hLen0
                  apply hPos0
                  simpa [hLen0] using hEqPos
                have : mergeEdits prev a ≠ none := by
                  have hPos0' : a.pos ≠ prev.pos := hPos0
                  simp [mergeEdits, prevTy, aTy, hPos0', hEqPos, hLen]
                exact this hPrev
              have hPos0' : merged.pos ≠ prev.pos := by
                intro hEqPos
                apply hPos0
                simpa [hMergedPos] using hEqPos
              have hPos1' : merged.pos ≠ prev.pos + prev.payload.length := by
                intro hEqPos
                apply hPos1
                simpa [hMergedPos] using hEqPos
              simp [mergeEdits, prevTy, hMergedTy, hPos0', hPos1']
            · -- prev del
              simp [mergeEdits, prevTy, hMergedTy]
            · -- prev sub
              simp [mergeEdits, prevTy, hMergedTy]
          ·
            by_cases hb1 : b.pos = a.pos + a.payload.length
            ·
              have hLenA : a.payload.length ≠ 0 := by
                intro hLen0
                apply hb0
                simpa [hLen0] using hb1
              have hEq : merged = { a with payload := a.payload ++ b.payload } := by
                apply Eq.symm
                apply Option.some.inj
                simpa [mergeEdits, aTy, bTy, hb0, hb1, hLenA] using hMerge
              have hMergedTy : merged.type = EditType.ins := by
                simp [hEq, aTy]
              have hMergedPos : merged.pos = a.pos := by
                simp [hEq]
              cases prevTy : prev.type
              · -- prev ins
                have hPos0 : a.pos ≠ prev.pos := by
                  intro hEqPos
                  have : mergeEdits prev a ≠ none := by
                    simp [mergeEdits, prevTy, aTy, hEqPos]
                  exact this hPrev
                have hPos1 : a.pos ≠ prev.pos + prev.payload.length := by
                  intro hEqPos
                  have hLen : prev.payload.length ≠ 0 := by
                    intro hLen0
                    apply hPos0
                    simpa [hLen0] using hEqPos
                  have : mergeEdits prev a ≠ none := by
                    have hPos0' : a.pos ≠ prev.pos := hPos0
                    simp [mergeEdits, prevTy, aTy, hPos0', hEqPos, hLen]
                  exact this hPrev
                have hPos0' : merged.pos ≠ prev.pos := by
                  intro hEqPos
                  apply hPos0
                  simpa [hMergedPos] using hEqPos
                have hPos1' : merged.pos ≠ prev.pos + prev.payload.length := by
                  intro hEqPos
                  apply hPos1
                  simpa [hMergedPos] using hEqPos
                simp [mergeEdits, prevTy, hMergedTy, hPos0', hPos1']
              · -- prev del
                simp [mergeEdits, prevTy, hMergedTy]
              · -- prev sub
                simp [mergeEdits, prevTy, hMergedTy]
            ·
              exfalso
              simp [mergeEdits, aTy, bTy, hb0, hb1] at hMerge
      | del =>
          exfalso
          simp [mergeEdits, aTy, bTy] at hMerge
      | sub =>
          exfalso
          simp [mergeEdits, aTy, bTy] at hMerge
  | del =>
      cases bTy : b.type with
      | ins =>
          exfalso
          simp [mergeEdits, aTy, bTy] at hMerge
      | del =>
          have hb : 0 < a.len ∧ 0 < b.len ∧ a.pos = b.pos := by
            by_cases hb : 0 < a.len ∧ 0 < b.len ∧ a.pos = b.pos
            · exact hb
            ·
              exfalso
              simp [mergeEdits, aTy, bTy, hb] at hMerge
          have hEq : merged = { a with len := a.len + b.len } := by
            apply Eq.symm
            apply Option.some.inj
            simpa [mergeEdits, aTy, bTy, hb] using hMerge
          have hMergedTy : merged.type = EditType.del := by
            simp [hEq, aTy]
          have hMergedPos : merged.pos = a.pos := by
            simp [hEq]
          cases prevTy : prev.type
          · -- prev ins
            simp [mergeEdits, prevTy, hMergedTy]
          · -- prev del
            have hNot : ¬(0 < prev.len ∧ 0 < a.len ∧ prev.pos = a.pos) := by
              intro hConj
              have : mergeEdits prev a ≠ none := by
                simp [mergeEdits, prevTy, aTy, hConj]
              exact this hPrev
            by_cases hConj : 0 < prev.len ∧ 0 < merged.len ∧ prev.pos = merged.pos
            · have : 0 < prev.len ∧ 0 < a.len ∧ prev.pos = a.pos := by
                refine ⟨hConj.1, hb.1, ?_⟩
                simpa [hMergedPos] using hConj.2.2
              exact (hNot this).elim
            ·
              simp [mergeEdits, prevTy, hMergedTy, hConj]
          · -- prev sub
            simp [mergeEdits, prevTy, hMergedTy]
      | sub =>
          exfalso
          simp [mergeEdits, aTy, bTy] at hMerge
  | sub =>
      cases bTy : b.type with
      | ins =>
          exfalso
          simp [mergeEdits, aTy, bTy] at hMerge
      | del =>
          exfalso
          simp [mergeEdits, aTy, bTy] at hMerge
      | sub =>
          have hb :
              a.len > 0 ∧
                b.len > 0 ∧
                  a.payload.length = a.len ∧
                    b.payload.length = b.len ∧ a.pos + a.len = b.pos := by
            by_cases hb :
                a.len > 0 ∧
                  b.len > 0 ∧
                    a.payload.length = a.len ∧
                      b.payload.length = b.len ∧ a.pos + a.len = b.pos
            · exact hb
            ·
              exfalso
              simp [mergeEdits, aTy, bTy, hb] at hMerge
          have hEq :
              merged = { a with len := a.len + b.len, payload := a.payload ++ b.payload } := by
            apply Eq.symm
            apply Option.some.inj
            simpa [mergeEdits, aTy, bTy, hb] using hMerge
          have hMergedTy : merged.type = EditType.sub := by
            simp [hEq, aTy]
          have hMergedPos : merged.pos = a.pos := by
            simp [hEq]
          cases prevTy : prev.type
          · -- prev ins
            simp [mergeEdits, prevTy, hMergedTy]
          · -- prev del
            simp [mergeEdits, prevTy, hMergedTy]
          · -- prev sub
            have hNot :
                ¬(0 < prev.len ∧
                      0 < a.len ∧
                        prev.payload.length = prev.len ∧
                          a.payload.length = a.len ∧ prev.pos + prev.len = a.pos) := by
              intro hConj
              have : mergeEdits prev a ≠ none := by
                simp [mergeEdits, prevTy, aTy, hConj]
              exact this hPrev
            by_cases hConj :
                0 < prev.len ∧
                  0 < merged.len ∧
                    prev.payload.length = prev.len ∧
                      merged.payload.length = merged.len ∧ prev.pos + prev.len = merged.pos
            · have :
                  0 < prev.len ∧
                    0 < a.len ∧
                      prev.payload.length = prev.len ∧
                        a.payload.length = a.len ∧ prev.pos + prev.len = a.pos := by
                refine ⟨hConj.1, hb.1, hConj.2.2.1, hb.2.2.1, ?_⟩
                simpa [hMergedPos] using hConj.2.2.2.2
              exact (hNot this).elim
            ·
              simp [mergeEdits, prevTy, hMergedTy, hConj]

theorem normalizeScriptAcc_noMergeAdj (acc edits : List Edit) :
    AccNoMerge acc → NoMergeAdj (normalizeScriptAcc acc edits) := by
  intro hAcc
  induction edits generalizing acc with
  | nil =>
      -- Convert `AccNoMerge acc` (a chain on `acc`) to `NoMergeAdj acc.reverse` using `chain'_reverse`.
      have : NoMergeAdj acc.reverse := by
        simpa [NoMergeAdj, AccNoMerge, NoMergeRel] using
          (List.chain'_reverse (R := NoMergeRel) (l := acc)).2 hAcc
      simpa [normalizeScriptAcc] using this
  | cons e es ih =>
      cases acc with
      | nil =>
          have hAcc' : AccNoMerge ([e] : List Edit) := by
            simp [AccNoMerge, NoMergeRel]
          simpa [normalizeScriptAcc] using ih (acc := [e]) hAcc'
      | cons h t =>
          cases hm : mergeEdits h e with
          | none =>
              have hAcc' : AccNoMerge (e :: h :: t) := by
                -- Extend the accumulator chain by a new head `e`; the only new adjacency is `(h,e)`.
                unfold AccNoMerge at *
                -- `chain'_cons'` gives a convenient constructor view for `Chain'`.
                refine (List.chain'_cons'.2 ?_)
                refine ⟨?_, hAcc⟩
                intro y hy
                have : y = h := by
                  have : (h = y) := by simpa [List.head?, Option.mem_def] using hy
                  exact this.symm
                subst this
                simp [NoMergeRel, hm]
              simpa [normalizeScriptAcc, hm] using ih (acc := e :: h :: t) hAcc'
          | some merged =>
              have hAcc' : AccNoMerge (merged :: t) := by
                cases t with
                | nil =>
                    simp [AccNoMerge, NoMergeRel]
                | cons prev rest =>
                    -- From the existing accumulator chain, extract the boundary `mergeEdits prev h = none`.
                    have hStep : mergeEdits prev h = none := by
                      unfold AccNoMerge at hAcc
                      have := (List.chain'_cons'.1 hAcc).1
                      -- head? (prev :: rest) = some prev
                      have : mergeEdits prev h = none := by
                        have := this prev (by simp [List.head?])
                        simpa [NoMergeRel] using this
                      exact this
                    have hTail : AccNoMerge (prev :: rest) := by
                      unfold AccNoMerge at hAcc
                      exact (List.chain'_cons'.1 hAcc).2
                    have hPrevMerged : mergeEdits prev merged = none :=
                      mergeEdits_prev_none_of_merge (prev := prev) (a := h) (b := e) (merged := merged) hStep hm
                    -- Build the new accumulator chain `merged :: prev :: rest`.
                    unfold AccNoMerge
                    refine (List.chain'_cons'.2 ?_)
                    refine ⟨?_, hTail⟩
                    intro y hy
                    have : y = prev := by
                      have : (prev = y) := by simpa [List.head?, Option.mem_def] using hy
                      exact this.symm
                    subst this
                    simpa [NoMergeRel] using hPrevMerged
              simpa [normalizeScriptAcc, hm] using ih (acc := merged :: t) hAcc'

theorem normalizeScript_noMergeAdj (edits : List Edit) :
    NoMergeAdj (normalizeScript edits) := by
  simpa [normalizeScript] using normalizeScriptAcc_noMergeAdj (acc := []) (edits := edits) accNoMerge_nil

theorem normalizeScriptAcc_eq_of_noMergeAdj (pref edits : List Edit) :
    NoMergeAdj (pref ++ edits) → normalizeScriptAcc pref.reverse edits = pref ++ edits := by
  intro hChain
  induction edits generalizing pref with
  | nil =>
      simp [normalizeScriptAcc]
  | cons e es ih =>
      cases pref with
      | nil =>
          -- pref = []
          simpa [normalizeScriptAcc] using ih (pref := [e]) (by simpa using hChain)
      | cons pHead pTail =>
          let pref : List Edit := pHead :: pTail
          -- pref is nonempty; the boundary between pref and `e` must be non-mergeable.
          have hb :
              ∀ x ∈ pref.getLast?, ∀ y ∈ (e :: es).head?, NoMergeRel x y := by
            have := (List.chain'_append (R := NoMergeRel) (l₁ := pref) (l₂ := e :: es)).1 hChain
            exact this.2.2
          -- `pref.getLast?` is the head of `pref.reverse`.
          have hLast : pref.getLast? = pref.reverse.head? :=
            getLast?_eq_head?_reverse (l := pref)
          -- With no merge at the boundary, the normalizer pushes `e` and continues.
          have : (pref ++ [e]) ++ es = pref ++ (e :: es) := by simp [List.append_assoc]
          have hChain' : NoMergeAdj ((pref ++ [e]) ++ es) := by
            simpa [this] using hChain
          -- Unfold one step of the normalizer.
          -- `pref.reverse` is nonempty in this branch.
          cases prefRev : pref.reverse with
          | nil =>
              cases pref <;> simp at prefRev
          | cons last rest =>
              have hMergeBoundary : mergeEdits last e = none := by
                have hLastOpt : pref.getLast? = some last := by
                  simpa [prefRev] using hLast
                have hMemLast : last ∈ pref.getLast? := by
                  simp [Option.mem_def, hLastOpt]
                have hRel : NoMergeRel last e := by
                  have := hb last hMemLast e (by simp [List.head?])
                  simpa using this
                simpa [NoMergeRel] using hRel
              -- Apply the induction hypothesis to the extended prefix.
              simpa [normalizeScriptAcc, prefRev, hMergeBoundary, List.append_assoc] using
                ih (pref := pref ++ [e]) hChain'

theorem normalizeScript_eq_of_noMergeAdj (edits : List Edit) :
    NoMergeAdj edits → normalizeScript edits = edits := by
  intro h
  simpa [normalizeScript] using normalizeScriptAcc_eq_of_noMergeAdj (pref := []) (edits := edits) (by simpa using h)

theorem normalizeScript_idempotent (edits : List Edit) :
    normalizeScript (normalizeScript edits) = normalizeScript edits := by
  apply normalizeScript_eq_of_noMergeAdj
  exact normalizeScript_noMergeAdj edits

private theorem bind_map_mk_splice (x : Option (List Char)) (pos takeLen : Nat) (insert : List Char) :
    (x.map String.mk >>= fun s1 => (splice s1.data pos takeLen insert).map String.mk) =
      ((x >>= fun chars => splice chars pos takeLen insert).map String.mk) := by
  cases x <;> rfl

private theorem splice_ins_ins_same_pos (s : List Char) (pos : Nat) (a b : List Char) :
    ((splice s pos 0 a) >>= fun s' => splice s' pos 0 b) = splice s pos 0 (b ++ a) := by
  by_cases hpos : pos > s.length
  · simp [splice, hpos]
  ·
    have hposLe : pos ≤ s.length := Nat.le_of_not_gt hpos
    set s1 : List Char := s.take pos ++ a ++ s.drop pos with hs1
    have hFirst : splice s pos 0 a = some s1 := by
      simp [splice, hpos, hs1, Nat.add_zero]
    -- Reduce the left to a single splice on `s1`.
    simp [hFirst]
    have hTakeLen : (s.take pos).length = pos := by
      simp [List.length_take, Nat.min_eq_left hposLe]
    have hPosLeS1 : pos ≤ s1.length := by
      simp [hs1, List.append_assoc, List.length_append, hTakeLen, Nat.add_assoc]
    have hPosNotGtS1 : ¬pos > s1.length := Nat.not_lt_of_ge hPosLeS1
    -- Unfold both splices now that the bounds are in the right shape.
    simp [splice, hpos, hPosNotGtS1, Nat.add_zero]
    have hLe : pos ≤ (s.take pos).length := by
      simp [hTakeLen]
    have hTake : s1.take pos = s.take pos := by
      calc
        s1.take pos = (s.take pos ++ (a ++ s.drop pos)).take pos := by
          simp [hs1, List.append_assoc]
        _ = (s.take pos).take pos := by
          simpa using
            (List.take_append_of_le_length (l₁ := s.take pos) (l₂ := a ++ s.drop pos) (n := pos) hLe)
        _ = s.take pos := by
          apply List.take_all_of_le
          simp [hTakeLen]
    have hDrop : s1.drop pos = a ++ s.drop pos := by
      calc
        s1.drop pos = (s.take pos ++ (a ++ s.drop pos)).drop pos := by
          simp [hs1, List.append_assoc]
        _ = (s.take pos).drop pos ++ (a ++ s.drop pos) := by
          simpa using
            (List.drop_append_of_le_length (l₁ := s.take pos) (l₂ := a ++ s.drop pos) (n := pos) hLe)
        _ = [] ++ (a ++ s.drop pos) := by
          have hLen : (s.take pos).length ≤ pos := by
            simp [hTakeLen]
          simp [List.drop_eq_nil_of_le hLen]
        _ = a ++ s.drop pos := by simp
    simp [hTake, hDrop, List.append_assoc]

private theorem splice_ins_ins_adj_pos (s : List Char) (pos : Nat) (a b : List Char) :
    ((splice s pos 0 a) >>= fun s' => splice s' (pos + a.length) 0 b) = splice s pos 0 (a ++ b) := by
  by_cases hpos : pos > s.length
  · simp [splice, hpos]
  ·
    have hposLe : pos ≤ s.length := Nat.le_of_not_gt hpos
    set s1 : List Char := s.take pos ++ a ++ s.drop pos with hs1
    have hFirst : splice s pos 0 a = some s1 := by
      simp [splice, hpos, hs1, Nat.add_zero]
    -- Reduce the left to a single splice on `s1`.
    simp [hFirst]
    have hTakeLen : (s.take pos).length = pos := by
      simp [List.length_take, Nat.min_eq_left hposLe]
    have hLenL1 : (s.take pos ++ a).length = pos + a.length := by
      simp [List.length_append, hTakeLen]
    have hPosLeNew : pos + a.length ≤ s1.length := by
      have hLeFull : (s.take pos ++ a).length ≤ s1.length := by
        simp [hs1, List.append_assoc, List.length_append]
      calc
        pos + a.length = (s.take pos ++ a).length := hLenL1.symm
        _ ≤ s1.length := hLeFull
    have hPosNotGtNew : ¬(pos + a.length) > s1.length :=
      Nat.not_lt_of_ge hPosLeNew
    -- Unfold both splices now that the bounds are in the right shape.
    simp [splice, hpos, hPosNotGtNew, Nat.add_zero]
    have hTake : s1.take (pos + a.length) = s.take pos ++ a := by
      calc
        s1.take (pos + a.length) = ((s.take pos ++ a) ++ s.drop pos).take (pos + a.length) := by
          simp [hs1, List.append_assoc]
        _ = (s.take pos ++ a).take (pos + a.length) := by
          have hLe : pos + a.length ≤ (s.take pos ++ a).length := by
            simp [hLenL1]
          simpa using
            (List.take_append_of_le_length (l₁ := s.take pos ++ a) (l₂ := s.drop pos) (n := pos + a.length) hLe)
        _ = s.take pos ++ a := by
          apply List.take_all_of_le
          simp [hLenL1]
    have hDrop : s1.drop (pos + a.length) = s.drop pos := by
      calc
        s1.drop (pos + a.length) = ((s.take pos ++ a) ++ s.drop pos).drop (pos + a.length) := by
          simp [hs1, List.append_assoc]
        _ = (s.take pos ++ a).drop (pos + a.length) ++ s.drop pos := by
          have hLe : pos + a.length ≤ (s.take pos ++ a).length := by
            simp [hLenL1]
          simpa using
            (List.drop_append_of_le_length (l₁ := s.take pos ++ a) (l₂ := s.drop pos) (n := pos + a.length) hLe)
        _ = [] ++ s.drop pos := by
          have hLen : (s.take pos ++ a).length ≤ pos + a.length := by
            simp [hLenL1]
          simp [List.drop_eq_nil_of_le hLen]
        _ = s.drop pos := by simp
    simp [hTake, hDrop, List.append_assoc]

private theorem splice_del_del_same_pos (s : List Char) (pos len1 len2 : Nat) :
    ((splice s pos len1 []) >>= fun s' => splice s' pos len2 []) = splice s pos (len1 + len2) [] := by
  by_cases hpos : pos > s.length
  · simp [splice, hpos]
  ·
    have hposLe : pos ≤ s.length := Nat.le_of_not_gt hpos
    by_cases hlen1 : pos + len1 > s.length
    ·
      have hlen12 : pos + (len1 + len2) > s.length := by
        have hle : pos + len1 ≤ pos + (len1 + len2) := by
          simp [Nat.add_assoc]
        exact Nat.lt_of_lt_of_le hlen1 hle
      simp [splice, hpos, hlen1, hlen12, Nat.add_assoc]
    ·
      have hlen1Le : pos + len1 ≤ s.length := Nat.le_of_not_gt hlen1
      -- After the first deletion.
      set s1 : List Char := s.take pos ++ s.drop (pos + len1) with hs1
      have hFirst : splice s pos len1 [] = some s1 := by
        simp [splice, hpos, hlen1, hs1, Nat.add_assoc]
      -- Reduce to a single splice on `s1`.
      simp [hFirst]
      have hLenTake : (s.take pos).length = pos := by
        simp [List.length_take, Nat.min_eq_left hposLe]
      have hLen1Le' : len1 ≤ s.length := le_trans (Nat.le_add_left len1 pos) hlen1Le
      have hLenS1 : s1.length = s.length - len1 := by
        have hLen1LePos : len1 ≤ s.length - pos := by
          have : len1 + pos ≤ s.length := by
            simpa [Nat.add_comm] using hlen1Le
          exact (Nat.le_sub_iff_add_le (k := pos) (m := s.length) (n := len1) hposLe).2 this
        have hLenEq : pos + (s.length - (pos + len1)) = s.length - len1 := by
          calc
            pos + (s.length - (pos + len1)) = pos + ((s.length - pos) - len1) := by
              simp [Nat.sub_add_eq, Nat.add_assoc]
            _ = pos + (s.length - pos) - len1 := by
              simpa using (Nat.add_sub_assoc hLen1LePos pos).symm
            _ = (s.length - pos + pos) - len1 := by
              simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            _ = s.length - len1 := by
              simp [Nat.sub_add_cancel hposLe, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        calc
          s1.length = (s.take pos ++ s.drop (pos + len1)).length := by simp [hs1]
          _ = (s.take pos).length + (s.drop (pos + len1)).length := by simp [List.length_append]
          _ = pos + (s.length - (pos + len1)) := by
              simp [hLenTake, List.length_drop, Nat.add_assoc]
          _ = s.length - len1 := by
              simp [hLenEq]
      have hPosNotGt : ¬pos > s1.length := by
        have hPosLeDrop : pos ≤ s.length - len1 :=
          (Nat.le_sub_iff_add_le (k := len1) (m := s.length) (n := pos) hLen1Le').2 (by
            simpa [Nat.add_comm] using hlen1Le)
        have : pos ≤ s1.length := by simpa [hLenS1] using hPosLeDrop
        exact Nat.not_lt_of_ge this
      by_cases hlen12 : pos + len1 + len2 > s.length
      ·
        have hlen12' : pos + (len1 + len2) > s.length := by
          simpa [Nat.add_assoc] using hlen12
        have hSecondFail : pos + len2 > s1.length := by
          have hTooFar : s.length - len1 < pos + len2 := by
            apply (Nat.sub_lt_iff_lt_add hLen1Le').2
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlen12
          simpa [hLenS1] using hTooFar
        simp [splice, hpos, hlen12', hPosNotGt, hSecondFail, Nat.add_assoc]
      ·
        have hlen12Le : pos + len1 + len2 ≤ s.length := Nat.le_of_not_gt hlen12
        have hNotMerged : ¬pos + (len1 + len2) > s.length := by
          apply Nat.not_lt_of_ge
          simpa [Nat.add_assoc] using hlen12Le
        have hSecondNotGt : ¬pos + len2 > s1.length := by
          have hSecondLe : pos + len2 ≤ s.length - len1 :=
            (Nat.le_sub_iff_add_le (k := len1) (m := s.length) (n := pos + len2) hLen1Le').2 (by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlen12Le)
          have : pos + len2 ≤ s1.length := by simpa [hLenS1] using hSecondLe
          exact Nat.not_lt_of_ge this
        have hLe : pos ≤ (s.take pos).length := by
          simp [hLenTake]
        have hTake : s1.take pos = s.take pos := by
          calc
            s1.take pos = (s.take pos ++ s.drop (pos + len1)).take pos := by simp [hs1]
            _ = (s.take pos).take pos := by
                simpa using
                  (List.take_append_of_le_length (l₁ := s.take pos) (l₂ := s.drop (pos + len1)) (n := pos) hLe)
            _ = s.take pos := by
                apply List.take_all_of_le
                simp [hLenTake]
        have hDrop : s1.drop (pos + len2) = s.drop (pos + len1 + len2) := by
          have hLenPrefix : (s.take pos).length = pos := hLenTake
          calc
            s1.drop (pos + len2) = (s.take pos ++ s.drop (pos + len1)).drop (pos + len2) := by simp [hs1]
            _ = (s.take pos ++ s.drop (pos + len1)).drop ((s.take pos).length + len2) := by
                simp [hLenPrefix, Nat.add_assoc]
            _ = (s.drop (pos + len1)).drop len2 := by
                simpa using (List.drop_append (l₁ := s.take pos) (l₂ := s.drop (pos + len1)) len2)
            _ = s.drop (pos + len1 + len2) := by
                simp [List.drop_drop, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        simp [splice, hpos, hNotMerged, hPosNotGt, hSecondNotGt, hTake, hDrop, Nat.add_assoc, List.append_assoc]

private theorem splice_sub_sub_adj_pos (s : List Char) (pos len1 len2 : Nat) (a b : List Char) :
    a.length = len1 →
      ((splice s pos len1 a) >>= fun s' => splice s' (pos + len1) len2 b) =
        splice s pos (len1 + len2) (a ++ b) := by
  intro hLenA
  by_cases hpos : pos > s.length
  · simp [splice, hpos]
  ·
    have hposLe : pos ≤ s.length := Nat.le_of_not_gt hpos
    by_cases hlen1 : pos + len1 > s.length
    ·
      have hlen12 : pos + (len1 + len2) > s.length := by
        have hle : pos + len1 ≤ pos + (len1 + len2) := by
          simp [Nat.add_assoc]
        exact Nat.lt_of_lt_of_le hlen1 hle
      simp [splice, hpos, hlen1, hlen12, Nat.add_assoc]
    ·
      have hlen1Le : pos + len1 ≤ s.length := Nat.le_of_not_gt hlen1
      -- After the first substitution.
      set s1 : List Char := s.take pos ++ a ++ s.drop (pos + len1) with hs1
      have hFirst : splice s pos len1 a = some s1 := by
        simp [splice, hpos, hlen1, hs1, Nat.add_assoc]
      simp [hFirst]
      have hLenTake : (s.take pos).length = pos := by
        simp [List.length_take, Nat.min_eq_left hposLe]
      have hLenPrefix : (s.take pos ++ a).length = pos + len1 := by
        simp [List.length_append, hLenTake, hLenA]
      have hLenS1 : s1.length = s.length := by
        calc
          s1.length = (s.take pos ++ a ++ s.drop (pos + len1)).length := by
              simp [hs1]
          _ = (s.take pos).length + a.length + (s.drop (pos + len1)).length := by
              simp [List.append_assoc, List.length_append, Nat.add_assoc]
          _ = pos + len1 + (s.length - (pos + len1)) := by
              simp [hLenTake, hLenA, List.length_drop, Nat.add_assoc]
          _ = s.length := by
              have h : s.length - (pos + len1) + (pos + len1) = s.length :=
                Nat.sub_add_cancel hlen1Le
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
      by_cases hlen12 : pos + len1 + len2 > s.length
      ·
        have hNotFirst : ¬(pos + len1) > s1.length := by
          have : pos + len1 ≤ s1.length := by simpa [hLenS1] using hlen1Le
          exact Nat.not_lt_of_ge this
        have hTooFar : (pos + len1) + len2 > s1.length := by
          have : (pos + len1) + len2 > s.length := by
            simpa [Nat.add_assoc] using hlen12
          simpa [hLenS1] using this
        have hMergedFail : pos + (len1 + len2) > s.length := by
          simpa [Nat.add_assoc] using hlen12
        simp [splice, hpos, hMergedFail, hNotFirst, hTooFar]
      ·
        have hlen12Le : pos + len1 + len2 ≤ s.length := Nat.le_of_not_gt hlen12
        have hNotMerged : ¬pos + (len1 + len2) > s.length := by
          apply Nat.not_lt_of_ge
          simpa [Nat.add_assoc] using hlen12Le
        have hNotFirst : ¬(pos + len1) > s1.length := by
          have : pos + len1 ≤ s1.length := by simpa [hLenS1] using hlen1Le
          exact Nat.not_lt_of_ge this
        have hNotSecond : ¬(pos + len1) + len2 > s1.length := by
          have : (pos + len1) + len2 ≤ s1.length := by
            have : (pos + len1) + len2 ≤ s.length := by
              simpa [Nat.add_assoc] using hlen12Le
            simpa [hLenS1] using this
          exact Nat.not_lt_of_ge this
        have hTake : s1.take (pos + len1) = s.take pos ++ a := by
          have hLe : pos + len1 ≤ (s.take pos ++ a).length := by
            simp [hLenPrefix]
          calc
            s1.take (pos + len1) =
                ((s.take pos ++ a) ++ s.drop (pos + len1)).take (pos + len1) := by
                  simp [hs1, List.append_assoc]
            _ = (s.take pos ++ a).take (pos + len1) := by
                  simpa using
                    (List.take_append_of_le_length (l₁ := s.take pos ++ a) (l₂ := s.drop (pos + len1))
                      (n := pos + len1) hLe)
            _ = s.take pos ++ a := by
                  apply List.take_all_of_le
                  simp [hLenPrefix]
        have hDrop : s1.drop (pos + len1 + len2) = s.drop (pos + len1 + len2) := by
          calc
            s1.drop (pos + len1 + len2) =
                ((s.take pos ++ a) ++ s.drop (pos + len1)).drop ((s.take pos ++ a).length + len2) := by
                  simp [hs1, List.append_assoc, hLenPrefix, Nat.add_assoc]
            _ = (s.drop (pos + len1)).drop len2 := by
                  simpa using (List.drop_append (l₁ := s.take pos ++ a) (l₂ := s.drop (pos + len1)) len2)
            _ = s.drop (pos + len1 + len2) := by
                  simp [List.drop_drop, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        simp [splice, hpos, hNotMerged, hNotFirst, hNotSecond, hTake, hDrop, List.append_assoc]
        simp (config := { failIfUnchanged := false }) [Nat.add_assoc, List.append_assoc]

theorem applyEdits_mergeEdits_eq (s : String) (a b merged : Edit) :
    mergeEdits a b = some merged →
      applyEdits s [a, b] = applyEdits s [merged] := by
  intro hMerge
  have hTyEq : a.type = b.type := by
    by_contra hNe
    simp [mergeEdits, hNe] at hMerge
  cases aTy : a.type with
  | ins =>
      have bTy : b.type = EditType.ins := by
        simpa [aTy] using hTyEq.symm
      by_cases hb0 : b.pos = a.pos
      ·
        have hEq : merged = { a with payload := b.payload ++ a.payload } := by
          apply Eq.symm
          apply Option.some.inj
          simpa [mergeEdits, aTy, bTy, hTyEq, hb0] using hMerge
        cases hEq
        -- Reduce to list-level splice composition and map.
        have hSplice :=
          splice_ins_ins_same_pos (s := s.data) (pos := a.pos) (a := a.payload.data) (b := b.payload.data)
        -- Unfold `applyEdits` and rewrite the intermediate `String.mk` conversions away.
        simp [EditScriptV1.applyEdits, EditScriptV1.applyEdit, aTy, bTy, hb0, bind_map_mk_splice, hSplice]
      ·
        by_cases hb1 : b.pos = a.pos + a.payload.length
        ·
          have hEq : merged = { a with payload := a.payload ++ b.payload } := by
            apply Eq.symm
            apply Option.some.inj
            simpa [mergeEdits, aTy, bTy, hTyEq, hb0, hb1.symm] using hMerge
          cases hEq
          have hSplice :=
            splice_ins_ins_adj_pos (s := s.data) (pos := a.pos) (a := a.payload.data) (b := b.payload.data)
          simp [EditScriptV1.applyEdits, EditScriptV1.applyEdit, aTy, bTy, hb0, hb1, bind_map_mk_splice]
          simpa using congrArg (Option.map String.mk) hSplice
        ·
          exfalso
          simp [mergeEdits, aTy, bTy, hTyEq, hb0, hb1] at hMerge
  | del =>
      have bTy : b.type = EditType.del := by
        simpa [aTy] using hTyEq.symm
      have hb : a.len > 0 ∧ b.len > 0 ∧ a.pos = b.pos := by
        by_cases hb : a.len > 0 ∧ b.len > 0 ∧ a.pos = b.pos
        · exact hb
        ·
          exfalso
          simp [mergeEdits, aTy, bTy, hTyEq, hb] at hMerge
      have hEq : merged = { a with len := a.len + b.len } := by
        apply Eq.symm
        apply Option.some.inj
        simpa [mergeEdits, aTy, bTy, hTyEq, hb] using hMerge
      cases hEq
      have haLen : a.len ≠ 0 := Nat.ne_of_gt hb.1
      have hbLen : b.len ≠ 0 := Nat.ne_of_gt hb.2.1
      have hMergedLen : a.len + b.len ≠ 0 := by
        exact Nat.ne_of_gt (Nat.add_pos_left hb.1 b.len)
      have hSplice :=
        splice_del_del_same_pos (s := s.data) (pos := a.pos) (len1 := a.len) (len2 := b.len)
      have hbPos : b.pos = a.pos := hb.2.2.symm
      simp [EditScriptV1.applyEdits, EditScriptV1.applyEdit, aTy, bTy, hbPos, haLen, hbLen, hMergedLen,
        bind_map_mk_splice, Nat.add_assoc]
      simpa using congrArg (Option.map String.mk) hSplice
  | sub =>
      have bTy : b.type = EditType.sub := by
        simpa [aTy] using hTyEq.symm
      have hb :
          a.len > 0 ∧
            b.len > 0 ∧
              a.payload.length = a.len ∧
                b.payload.length = b.len ∧ a.pos + a.len = b.pos := by
        by_cases hb :
            a.len > 0 ∧
              b.len > 0 ∧
                a.payload.length = a.len ∧
                  b.payload.length = b.len ∧ a.pos + a.len = b.pos
        · exact hb
        ·
          exfalso
          simp [mergeEdits, aTy, bTy, hTyEq, hb] at hMerge
      have hEq : merged = { a with len := a.len + b.len, payload := a.payload ++ b.payload } := by
        apply Eq.symm
        apply Option.some.inj
        simpa [mergeEdits, aTy, bTy, hTyEq, hb] using hMerge
      cases hEq
      have haLen : a.len ≠ 0 := Nat.ne_of_gt hb.1
      have hbLen : b.len ≠ 0 := Nat.ne_of_gt hb.2.1
      have hMergedLen : a.len + b.len ≠ 0 := by
        exact Nat.ne_of_gt (Nat.add_pos_left hb.1 b.len)
      have hSplice :=
        splice_sub_sub_adj_pos (s := s.data) (pos := a.pos) (len1 := a.len) (len2 := b.len)
          (a := a.payload.data) (b := b.payload.data) (by simpa using hb.2.2.1)
      have hbPos : b.pos = a.pos + a.len := hb.2.2.2.2.symm
      simp [EditScriptV1.applyEdits, EditScriptV1.applyEdit, aTy, bTy, hbPos, haLen, hbLen, hMergedLen,
        bind_map_mk_splice, Nat.add_assoc]
      simpa using congrArg (Option.map String.mk) hSplice

theorem applyEdits_normalizeScriptAcc (s : String) (acc edits : List Edit) :
    applyEdits s (normalizeScriptAcc acc edits) = applyEdits s (acc.reverse ++ edits) := by
  induction edits generalizing acc with
  | nil =>
      simp [normalizeScriptAcc]
  | cons e es ih =>
      cases acc with
      | nil =>
          simpa [normalizeScriptAcc] using ih (acc := [e])
      | cons h t =>
          cases hm : mergeEdits h e with
          | none =>
              -- No merge: just push `e` onto the accumulator.
              simpa [normalizeScriptAcc, hm, List.reverse_cons, List.append_assoc] using
                ih (acc := e :: h :: t)
          | some merged =>
              have ih' := ih (acc := merged :: t)
              -- Replace `[h,e]` with `[merged]` under sequential semantics, after the shared prefix.
              have hPair :
                  applyEdits s (t.reverse ++ h :: e :: es) = applyEdits s (t.reverse ++ merged :: es) := by
                -- Factor out the common prefix.
                rw [EditScriptV1.applyEdits_append]
                rw [EditScriptV1.applyEdits_append]
                -- Case split on the prefix evaluation.
                cases hPref : applyEdits s t.reverse with
                | none =>
                    simp [hPref]
                | some s' =>
                    -- Reduce to the merged pair on the intermediate string, then re-append `es`.
                    have hPair' : applyEdits s' (h :: e :: es) = applyEdits s' (merged :: es) := by
                      -- Factor out the shared suffix `es`.
                      change applyEdits s' ([h, e] ++ es) = applyEdits s' ([merged] ++ es)
                      rw [EditScriptV1.applyEdits_append (s := s') (xs := [h, e]) (ys := es)]
                      rw [EditScriptV1.applyEdits_append (s := s') (xs := [merged]) (ys := es)]
                      -- Use the pair-merge correctness lemma.
                      have hMid : applyEdits s' [h, e] = applyEdits s' [merged] :=
                        applyEdits_mergeEdits_eq (s := s') (a := h) (b := e) (merged := merged) hm
                      simp [hMid]
                    simp [hPref, hPair']
              -- Finish: rewrite the IH target to match the original accumulator.
              simpa [normalizeScriptAcc, hm, List.reverse_cons, List.append_assoc, hPair] using ih'

theorem applyEdits_normalizeScript (s : String) (edits : List Edit) :
    applyEdits s (normalizeScript edits) = applyEdits s edits := by
  simpa [normalizeScript] using applyEdits_normalizeScriptAcc (s := s) (acc := []) (edits := edits)

private def hasMergeableAdj (edits : List Edit) : Bool :=
  match edits with
  | [] => false
  | [_] => false
  | a :: b :: rest =>
      match mergeEdits a b with
      | some _ => true
      | none => hasMergeableAdj (b :: rest)

private def slice (s : String) (pos len : Nat) : Option String :=
  let chars := s.data
  if pos + len ≤ chars.length then
    some <| String.mk ((chars.drop pos).take len)
  else
    none

private def hasRedundantSubs (seqA : String) (edits : List Edit) : Bool :=
  edits.any fun e =>
    match e.type with
    | EditType.sub =>
        if e.len = 0 then
          true
        else
          match slice seqA e.pos e.len with
          | some frag => frag = e.payload
          | none => true
    | _ => false

def isNormalForm (seqA : String) (edits : List Edit) : Bool :=
  normalizeScript edits = edits ∧ !hasMergeableAdj edits ∧ !hasRedundantSubs seqA edits

def SpecHolds (inst : Instance) : Prop :=
  applyEdits inst.seqA inst.edits = some inst.seqB ∧
    isNormalForm inst.seqA inst.edits ∧
    match inst.normalizedEdits? with
    | none =>
        normalizeScript inst.edits = inst.edits
    | some norm =>
        applyEdits inst.seqA norm = some inst.seqB ∧
        isNormalForm inst.seqA norm ∧
        normalizeScript inst.edits = norm ∧
        normalizeScript norm = norm

def checkInstance (inst : Instance) : Decidable (SpecHolds inst) := by
  unfold SpecHolds
  cases h : inst.normalizedEdits? <;> (simp [h]; infer_instance)

end EditScriptNormalFormV1
end Edit
end VeriBiota
end Biosim
