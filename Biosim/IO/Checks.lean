import Lean.Data.Json
import Biosim.IO.Shared

open Lean
open System

private def insertionSort {α : Type u} (cmp : α → α → Bool) :
    List α → List α
  | [] => []
  | x :: xs =>
      let rec insert (x : α) : List α → List α
        | [] => [x]
        | y :: ys =>
            if cmp x y then
              x :: y :: ys
            else
              y :: insert x ys
      insert x (insertionSort cmp xs)

namespace Biosim
namespace IO
namespace Checks

private def normalizeStrings (xs : List String) : List String :=
  let filtered := xs.filter fun s => !s.isEmpty
  (insertionSort (· ≤ ·) filtered).eraseDups

private def normalizeWeights (pairs : List (String × Int)) :
    List (String × Int) :=
  let insert (acc : List (String × Int)) (species : String) (coeff : Int) :=
    let rec go
      | [] =>
          if coeff = 0 then [] else [(species, coeff)]
      | (s, w) :: rest =>
          if s = species then
            let new := w + coeff
            if new = 0 then rest else (s, new) :: rest
          else
            (s, w) :: go rest
    go acc
  let combined :=
    pairs.foldl (fun acc (species, coeff) => insert acc species coeff) []
  insertionSort (fun a b => a.1 ≤ b.1)
    (combined.filter fun (_, coeff) => coeff ≠ 0)

private def jsonFromFloat! (x : Float) : Json :=
  match JsonNumber.fromFloat? x with
  | Sum.inr num => Json.num num
  | Sum.inl err => panic! s!"Invalid float for JSON serialization: {err}"

inductive ToleranceMode
  | absolute
  | relative
  deriving DecidableEq, Repr

namespace ToleranceMode

def toString : ToleranceMode → String
  | absolute => "absolute"
  | relative => "relative"

def ofString? : String → Option ToleranceMode
  | "absolute" => some absolute
  | "relative" => some relative
  | _ => none

end ToleranceMode

structure Tolerance where
  mode : ToleranceMode
  value : Float
  deriving Repr

namespace Tolerance

def toJson (tol : Tolerance) : Json :=
  Json.mkObj
    [("mode", Json.str tol.mode.toString)
    , ("value", jsonFromFloat! tol.value)]

end Tolerance

structure LinearInvariantSpec where
  name : String
  proofId : String
  weights : List (String × Int)
  tolerance : Tolerance
  strict : Bool := false
  deriving Repr

structure PositivityCounts where
  species : List String
  deriving Repr

structure PositivityConcentration where
  species : List String
  tolerance : Float := 1e-12
  deriving Repr

inductive Check
  | positivityCounts (spec : PositivityCounts)
  | positivityConcentration (spec : PositivityConcentration)
  | linearInvariant (spec : LinearInvariantSpec)
  deriving Repr

namespace Check

def normalize : Check → Check
  | positivityCounts spec =>
      positivityCounts { species := normalizeStrings spec.species }
  | positivityConcentration spec =>
      positivityConcentration
        { species := normalizeStrings spec.species
          , tolerance := spec.tolerance }
  | linearInvariant spec =>
      linearInvariant
        { spec with weights := normalizeWeights spec.weights }

private def weightsToJson (weights : List (String × Int)) : Json :=
  Json.mkObj (weights.map fun (species, coeff) =>
    (species, Json.num (JsonNumber.fromInt coeff)))

def toJson : Check → Json
  | positivityCounts spec =>
      Json.mkObj
        [("type", Json.str "positivity_counts")
        , ("species",
            Json.arr <| Array.mk (spec.species.map Json.str))]
  | positivityConcentration spec =>
      Json.mkObj
        [("type", Json.str "positivity_conc")
        , ("species",
            Json.arr <| Array.mk (spec.species.map Json.str))
        , ("tolerance", jsonFromFloat! spec.tolerance)]
  | linearInvariant spec =>
      let base : List (String × Json) :=
        [("type", Json.str "lin_invariant")
        , ("name", Json.str spec.name)
        , ("proofId", Json.str spec.proofId)
        , ("weights", weightsToJson spec.weights)
        , ("tolerance", spec.tolerance.toJson)]
      let base :=
        if spec.strict then
          base ++ [("strict", Json.bool true)]
        else
          base
      Json.mkObj base

end Check

structure Bundle where
  schema : String := "veribiota.checks.v1"
  toolchain : Biosim.IO.ToolchainInfo
  modelHash : String
  generatedAt : String
  checks : List Check := []
  signature? : Option Biosim.IO.SignatureInfo := none
  deriving Repr

namespace Bundle

def normalize (bundle : Bundle) : Bundle :=
  { bundle with checks := bundle.checks.map Check.normalize }

def toJson (bundle : Bundle) : Json :=
  let normalized := bundle.normalize
  Json.mkObj
    ([("schema", Json.str normalized.schema)
     , ("toolchain", normalized.toolchain.toChecksJson)
     , ("modelHash", Json.str normalized.modelHash)
     , ("generatedAt", Json.str normalized.generatedAt)
     , ("checks",
         Json.arr <|
           Array.mk (normalized.checks.map Check.toJson))] ++
     match normalized.signature? with
     | none => []
     | some sig => [("signature", sig.toJson)])

def render (bundle : Bundle) (pretty := true) : String :=
  let json := bundle.toJson
  let body :=
    if pretty then json.pretty 2 else json.compress
  if body.endsWith "\n" then body else body ++ "\n"

def save (path : System.FilePath) (bundle : Bundle) (pretty := true) :
    IO String := do
  let payload := (bundle.render pretty).toUTF8
  IO.writeFileWithSha path payload

private def expectStringField (obj : Json) (field : String) :
    Except String String := do
  match obj.getObjVal? field with
  | Except.ok (Json.str s) => pure s
  | Except.ok _ =>
      Except.error s!"Field '{field}' must be a string"
  | Except.error err => Except.error err

private def expectFloatField (obj : Json) (field : String) :
    Except String Float := do
  match obj.getObjVal? field with
  | Except.ok (Json.num num) => pure num.toFloat
  | Except.ok _ =>
      Except.error s!"Field '{field}' must be numeric"
  | Except.error err => Except.error err

private def parseSpecies (json : Json) : Except String (List String) :=
  match json with
  | Json.arr arr =>
      arr.data.mapM fun entry =>
        match entry with
        | Json.str s => pure s
        | _ => Except.error "Species entries must be strings"
  | _ => Except.error "'species' must be an array"

private def parseTolerance (json : Json) : Except String Tolerance := do
  let modeStr ← expectStringField json "mode"
  let mode ←
    match ToleranceMode.ofString? modeStr with
    | some m => pure m
    | none => Except.error s!"Unknown tolerance mode '{modeStr}'"
  let value ← expectFloatField json "value"
  pure { mode, value }

private def parseWeights (json : Json) :
    Except String (List (String × Int)) := do
  match json with
  | Json.obj entries =>
      let res :=
        entries.fold (init := Except.ok []) fun acc key value => do
          let acc ← acc
          match value with
          | Json.num num =>
              match num.toString.toInt? with
              | some v => Except.ok <| (key, v) :: acc
              | none =>
                  Except.error s!"Weight for '{key}' must be integer"
          | Json.str s =>
              match s.toInt? with
              | some v => Except.ok <| (key, v) :: acc
              | none =>
                  Except.error s!"Weight for '{key}' must be integer"
          | _ => Except.error s!"Weight for '{key}' must be numeric"
      res
  | _ => Except.error "'weights' must be an object"

private def parseCheck (json : Json) : Except String Check := do
  let ty ← expectStringField json "type"
  match ty with
  | "positivity_counts" =>
      let species ← parseSpecies (← json.getObjVal? "species")
      pure <| Check.positivityCounts { species := species }
  | "positivity_conc" =>
      let species ← parseSpecies (← json.getObjVal? "species")
      let tol ← expectFloatField json "tolerance"
      pure <|
        Check.positivityConcentration
          { species := species, tolerance := tol }
  | "lin_invariant" =>
      let name ← expectStringField json "name"
      let proofId ← expectStringField json "proofId"
      let weightsJson ← json.getObjVal? "weights"
      let weights ← parseWeights weightsJson
      let toleranceJson ← json.getObjVal? "tolerance"
      let tol ← parseTolerance toleranceJson
      let strict :=
        match json.getObjVal? "strict" with
        | Except.ok (Json.bool b) => b
        | _ => false
      pure <|
        Check.linearInvariant
          { name, proofId, weights, tolerance := tol, strict }
  | other =>
      Except.error s!"Unknown check type '{other}'"

private def isHexDigit (c : Char) : Bool :=
  let v := c.toNat
  ('0'.toNat ≤ v ∧ v ≤ '9'.toNat)
    ∨ ('a'.toNat ≤ v ∧ v ≤ 'f'.toNat)
    ∨ ('A'.toNat ≤ v ∧ v ≤ 'F'.toNat)

private def validateHash (hash : String) : Except String Unit := do
  if !hash.startsWith "sha256:" then
    Except.error "modelHash must start with 'sha256:'"
  else
    let hex := hash.drop 7
    if hex.length != 64 || hex.any (fun c => !isHexDigit c) then
      Except.error "modelHash must contain 64 hex characters"
    else
      pure ()

def fromJson? (json : Json) : Except String Bundle := do
  let schema ← expectStringField json "schema"
  if schema ≠ "veribiota.checks.v1" then
    Except.error s!"Unsupported checks schema '{schema}'"
  let toolchainJson ← json.getObjVal? "toolchain"
  let leanVer ← expectStringField toolchainJson "lean"
  let mathlibVer ← expectStringField toolchainJson "mathlib"
  let tactics? :=
    match toolchainJson.getObjVal? "tactics" with
    | Except.ok (Json.str s) => some s
    | _ => none
  let modelHash ← expectStringField json "modelHash"
  validateHash modelHash
  let generatedAt ← expectStringField json "generatedAt"
  let signature? ←
    match json.getObjVal? "signature" with
    | Except.error _ => pure none
    | Except.ok sigJson =>
        match IO.SignatureInfo.fromJson? sigJson with
        | Except.ok sig => pure (some sig)
        | Except.error err => Except.error err
  let checksJson ← json.getObjVal? "checks"
  let checks :=
    match checksJson with
    | Json.arr entries =>
        entries.data.mapM parseCheck
    | _ => Except.error "'checks' must be an array"
  let checks ← checks
  pure
    { schema
      , toolchain :=
          { lean := leanVer
            , mathlib := mathlibVer
            , tacticLib? := tactics? }
      , modelHash
      , generatedAt
      , checks
      , signature? }

def fromString? (payload : String) : Except String Bundle :=
  match Json.parse payload with
  | Except.ok json => fromJson? json
  | Except.error err => Except.error err

end Bundle

end Checks
end IO
end Biosim
