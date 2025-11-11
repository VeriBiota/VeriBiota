import Lean.Data.Json
import Biosim.IO.Shared

namespace Biosim
namespace ProofCert

open Lean

structure TheoremRecord where
  name : String
  statement : String
  proofId : String
  deriving Repr

structure LimitsInfo where
  domain : String
  assumptions : List String := []
  deriving Repr

structure Certificate where
  schema : String := "veribiota.certificate.v1"
  modelId? : Option String := none
  modelHash : String
  semantics : List String := []
  toolchain : IO.ToolchainInfo
  theorems : List TheoremRecord := []
  timestamp : String
  parameters? : Option Json := none
  limits? : Option LimitsInfo := none
  signature? : Option IO.SignatureInfo := none

namespace JsonHelpers

def mkObj (fields : List (String × Json)) : Json :=
  Json.mkObj fields

def optField (label : String) : Option String → List (String × Json)
  | none => []
  | some value => [(label, Json.str value)]

def optJson (label : String) : Option Json → List (String × Json)
  | none => []
  | some value => [(label, value)]

end JsonHelpers

open JsonHelpers

namespace TheoremRecord

open Lean

def fromJson? (json : Json) : Except String TheoremRecord := do
  let name ←
    match json.getObjVal? "name" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "theorem.name must be a string"
  let statement ←
    match json.getObjVal? "statement" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "theorem.statement must be a string"
  let proofId ←
    match json.getObjVal? "proofId" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "theorem.proofId must be a string"
  pure { name, statement, proofId }

end TheoremRecord

namespace LimitsInfo

open Lean

def fromJson? (json : Json) : Except String LimitsInfo := do
  let domain ←
    match json.getObjVal? "domain" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "limits.domain must be a string"
  let assumptions ←
    match json.getObjVal? "assumptions" with
    | Except.ok (Json.arr arr) =>
        arr.data.mapM fun
          | Json.str s => pure s
          | _ => Except.error "limits.assumptions must be strings"
    | Except.error _ => pure []
    | _ => Except.error "limits.assumptions must be an array"
  pure { domain, assumptions }

end LimitsInfo

def TheoremRecord.toJson (r : TheoremRecord) : Json :=
  mkObj
    [ ("name", Json.str r.name)
    , ("statement", Json.str r.statement)
    , ("proofId", Json.str r.proofId)
    ]

def LimitsInfo.toJson (info : LimitsInfo) : Json :=
  mkObj
    [ ("domain", Json.str info.domain)
    , ("assumptions", Json.arr (info.assumptions.map Json.str |>.toArray))
    ]

def Certificate.toJson (cert : Certificate) : Json :=
  mkObj <|
    [ ("schema", Json.str cert.schema) ]
    ++ optField "modelId" cert.modelId?
    ++ [ ("modelHash", Json.str cert.modelHash)
       , ("semantics", Json.arr (cert.semantics.map Json.str |>.toArray))
       , ("toolchain", cert.toolchain.toJson)
       , ("theorems", Json.arr (cert.theorems.map TheoremRecord.toJson |>.toArray))
       , ("timestamp", Json.str cert.timestamp)
       ]
    ++ optJson "parameters" cert.parameters?
    ++ (match cert.limits? with
        | none => []
        | some limits => [("limits", limits.toJson)])
    ++ (match cert.signature? with
        | none => []
        | some sig => [("signature", sig.toJson)])

def Certificate.render (cert : Certificate) (pretty := true) : String :=
  let json := cert.toJson
  if pretty then
    json.pretty 2
  else
    json.compress

/-- Parse a certificate JSON payload into the structured representation. -/
def Certificate.fromJson? (json : Json) : Except String Certificate := do
  let schema ←
    match json.getObjVal? "schema" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "schema must be a string"
  let modelId? ←
    match json.getObjVal? "modelId" with
    | Except.ok (Json.str s) => pure (some s)
    | Except.ok _ => Except.error "modelId must be a string"
    | Except.error _ => pure none
  let modelHash ←
    match json.getObjVal? "modelHash" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "modelHash must be a string"
  let semantics ←
    match json.getObjVal? "semantics" with
    | Except.ok (Json.arr arr) =>
        arr.data.mapM fun
          | Json.str s => pure s
          | _ => Except.error "semantics entries must be strings"
    | _ => Except.error "semantics must be an array"
  let toolchainJson ←
    match json.getObjVal? "toolchain" with
    | Except.ok value => pure value
    | Except.error err => Except.error err
  let toolchain ← IO.ToolchainInfo.fromJson? toolchainJson
  let theoremsJson ←
    match json.getObjVal? "theorems" with
    | Except.ok (Json.arr arr) => pure arr.data
    | _ => Except.error "theorems must be an array"
  let theorems ← theoremsJson.mapM TheoremRecord.fromJson?
  let timestamp ←
    match json.getObjVal? "timestamp" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "timestamp must be a string"
  let parameters? :=
    match json.getObjVal? "parameters" with
    | Except.ok value => some value
    | Except.error _ => none
  let limits? ←
    match json.getObjVal? "limits" with
    | Except.ok value =>
        match LimitsInfo.fromJson? value with
        | Except.ok info => pure (some info)
        | Except.error err => Except.error err
    | Except.error _ => pure none
  let signature? ←
    match json.getObjVal? "signature" with
    | Except.ok value =>
        match IO.SignatureInfo.fromJson? value with
        | Except.ok sig => pure (some sig)
        | Except.error err => Except.error err
    | Except.error _ => pure none
  pure
    { schema
      , modelId?
      , modelHash
      , semantics
      , toolchain
      , theorems
      , timestamp
      , parameters?
      , limits?
      , signature? }

def save (path : System.FilePath) (cert : Certificate) (pretty := true) :
    IO Unit := do
  IO.ensureParentDir path
  IO.FS.writeFile path (cert.render pretty)

end ProofCert
end Biosim
