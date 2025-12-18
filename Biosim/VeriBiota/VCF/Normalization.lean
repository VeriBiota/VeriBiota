import Mathlib

namespace Biosim
namespace VeriBiota
namespace VCF
namespace Normalization

structure Variant where
  chrom : String
  pos : Nat
  ref : String
  alt : String
  deriving Repr, DecidableEq

structure VariantRecord where
  original : Variant
  normalized : Variant
  operations : List String := []
  deriving Repr, DecidableEq

structure Instance where
  inputVcfHash : String
  normalizedVcfHash : String
  referenceFastaHash? : Option String := none
  variants : List VariantRecord
  deriving Repr, DecidableEq

def profileId : String := "vcf_normalization_v1"
def profileVersion : String := "1.0.0"
def coreTheorems : List String := ["VB_VCF_001", "VB_VCF_002"]

private def commonPrefixLen : List Char → List Char → Nat
  | c1 :: r1, c2 :: r2 =>
      if c1 = c2 then
        1 + commonPrefixLen r1 r2
      else
        0
  | _, _ => 0

private def dropPrefix (n : Nat) (xs : List Char) : List Char :=
  xs.drop n

private def dropSuffix (n : Nat) (xs : List Char) : List Char :=
  (xs.reverse.drop n).reverse

private def canonicalize (v : Variant) : Variant := Id.run do
  let refList := v.ref.data
  let altList := v.alt.data
  let pre := commonPrefixLen refList altList
  let ref1 := dropPrefix pre refList
  let alt1 := dropPrefix pre altList
  let suf := commonPrefixLen ref1.reverse alt1.reverse
  let ref2 := dropSuffix suf ref1
  let alt2 := dropSuffix suf alt1
  let refStr := String.mk ref2
  let altStr := String.mk alt2
  let pos' := v.pos + pre
  { v with pos := pos', ref := refStr, alt := altStr }

def equivalent (a b : Variant) : Prop :=
  canonicalize a = canonicalize b

def normalizeVariant (v : Variant) : Variant :=
  canonicalize v

def recordHolds (r : VariantRecord) : Prop :=
  normalizeVariant r.original = r.normalized ∧
    equivalent r.original r.normalized

private instance (r : VariantRecord) : Decidable (recordHolds r) := by
  unfold recordHolds equivalent normalizeVariant
  infer_instance

def SpecHolds (inst : Instance) : Prop :=
  ∀ r ∈ inst.variants, recordHolds r

private def decidableForallMem {α : Type} (xs : List α) (p : α → Prop)
    [∀ a, Decidable (p a)] : Decidable (∀ a ∈ xs, p a) := by
  induction xs with
  | nil =>
      exact isTrue (by intro a ha; cases ha)
  | cons x xs ih =>
      by_cases hx : p x
      · cases ih with
        | isTrue hxs =>
            exact isTrue (by
              intro a ha
              have h' : a = x ∨ a ∈ xs := by simpa using ha
              cases h' with
              | inl hEq => simpa [hEq] using hx
              | inr hMem => exact hxs a hMem)
        | isFalse hxs =>
            exact isFalse (by
              intro hall
              apply hxs
              intro a ha
              exact hall a (by simp [ha]))
      ·
        exact isFalse (by
          intro hall
          apply hx
          exact hall x (by simp))

def checkInstance (inst : Instance) : Decidable (SpecHolds inst) := by
  unfold SpecHolds
  simpa using (decidableForallMem inst.variants recordHolds)

end Normalization
end VCF
end VeriBiota
end Biosim
