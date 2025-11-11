import Lean.Data.Json
import Biosim.IO.Shared

namespace Biosim
namespace IO
namespace Model

open Lean

structure Meta where
  createdAt : String
  createdBy : String
  toolchain : ToolchainInfo

structure RateLaw where
  kind : String
  params : Json := Json.null

structure Stoich where
  coeffs : List (String × Nat)

structure ReactionEntry where
  name : String
  input : Stoich
  output : Stoich
  rate : RateLaw

structure Body where
  id : String
  species : List String
  parameters : Json := Json.null
  reactions : List ReactionEntry
  units : Json := Json.null

structure Document where
  schema : String := "veribiota.model.v1"
  meta : Meta
  model : Body
  hash : String := "hash:pending"

namespace Helpers

open Lean

def stoichToJson (s : Stoich) : Json :=
  Json.arr <|
    Array.mk <|
      s.coeffs.map fun (name, coeff) =>
        Json.mkObj [
          ("species", Json.str name)
        , ("coeff", Json.num (Lean.JsonNumber.fromNat coeff))
        ]

def rateToJson (r : RateLaw) : Json :=
  Json.mkObj <|
    [ ("kind", Json.str r.kind)
    , ("params", r.params)
    ]

def reactionToJson (r : ReactionEntry) : Json :=
  Json.mkObj [
    ("name", Json.str r.name)
  , ("in", stoichToJson r.input)
  , ("out", stoichToJson r.output)
  , ("rate", rateToJson r.rate)
  ]

def metaToJson (m : Meta) : Json :=
  Json.mkObj [
    ("createdAt", Json.str m.createdAt)
  , ("createdBy", Json.str m.createdBy)
  , ("toolchain", m.toolchain.toJson)
  ]

def bodyToJson (b : Body) : Json :=
  Json.mkObj [
    ("id", Json.str b.id)
  , ("species", Json.arr (Array.mk (b.species.map Json.str)))
  , ("parameters", b.parameters)
  , ("reactions", Json.arr (Array.mk (b.reactions.map reactionToJson)))
  , ("units", b.units)
  ]

end Helpers

open Helpers

def toJson (doc : Document) : Json :=
  Json.mkObj
    [ ("schema", Json.str doc.schema)
    , ("meta", metaToJson doc.meta)
    , ("model", bodyToJson doc.model)
    , ("hash", Json.str doc.hash)
    ]

open System

def render (doc : Document) (pretty := true) : String :=
  let json := toJson doc
  if pretty then json.pretty 2 else json.compress

def save (path : FilePath) (doc : Document) (pretty := true) :
    IO Document := do
  let provisional := { doc with hash := "sha256:pending" }
  let provisionalBytes := (render provisional pretty).toUTF8
  let provisionalHex ← Biosim.IO.sha256HexBytesNear path provisionalBytes
  let digestTag := s!"sha256:{provisionalHex}"
  let finalized := { doc with hash := digestTag }
  let payload := (render finalized pretty).toUTF8
  discard <| Biosim.IO.writeFileWithSha path payload
  pure finalized

end Model
end IO
end Biosim
