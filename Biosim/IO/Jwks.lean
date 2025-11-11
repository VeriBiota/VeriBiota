import Lean.Data.Json
import Biosim.IO.Base64Url

namespace Biosim
namespace IO
namespace Jwks

open Lean

structure Jwk where
  kty : String
  crv : String
  kid : String
  x : String
  deriving Repr

structure Document where
  keys : List Jwk
  deriving Repr

def Jwk.fromJson? (json : Json) : Except String Jwk := do
  let kty ←
    match json.getObjVal? "kty" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "JWKS key missing kty"
  let crv ←
    match json.getObjVal? "crv" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "JWKS key missing crv"
  let kid ←
    match json.getObjVal? "kid" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "JWKS key missing kid"
  let x ←
    match json.getObjVal? "x" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "JWKS key missing x"
  pure { kty, crv, kid, x }

def Document.fromJson? (json : Json) : Except String Document := do
  match json.getObjVal? "keys" with
  | Except.ok (Json.arr arr) =>
      let keys ← arr.data.mapM Jwk.fromJson?
      pure { keys := keys }
  | _ => Except.error "'keys' must be an array"

def load (path : System.FilePath) : IO Document := do
  let contents ← IO.FS.readFile path
  match Json.parse contents with
  | Except.error err =>
      throw <| IO.userError s!"Failed to parse JWKS: {err}"
  | Except.ok json =>
      match Document.fromJson? json with
      | Except.ok doc => pure doc
      | Except.error err =>
          throw <| IO.userError s!"Invalid JWKS: {err}"

def findKey? (doc : Document) (kid : String) :
    Except String ByteArray := do
  match doc.keys.find? (fun k => k.kid = kid) with
  | none => Except.error s!"No key with kid '{kid}'"
  | some jwk =>
      if jwk.kty ≠ "OKP" ∨ jwk.crv ≠ "Ed25519" then
        Except.error s!"Unsupported key type for kid '{kid}'"
      else
        Base64Url.decode jwk.x

end Jwks
end IO
end Biosim
