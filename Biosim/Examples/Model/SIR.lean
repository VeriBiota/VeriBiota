import Lean.Data.Json
import Biosim.IO.Model
import Biosim.IO.Shared

namespace Biosim
namespace Examples
namespace Model
namespace SIR

open IO
open IO.Model
open Lean

def reactionEntries : List ReactionEntry :=
  [ { name := "infect"
      , input := { coeffs := [("S", 1), ("I", 1)] }
      , output := { coeffs := [("I", 2)] }
      , rate := { kind := "mass_action", params := Json.mkObj [("k", Json.str "beta")] } }
  , { name := "recover"
      , input := { coeffs := [("I", 1)] }
      , output := { coeffs := [("R", 1)] }
      , rate := { kind := "mass_action", params := Json.mkObj [("k", Json.str "gamma")] } }
  ]

def document : Document :=
  { meta :=
      { createdAt := "2026-01-01T00:00:00Z"
        , createdBy := "biosim-cli"
        , toolchain := { lean := Lean.versionString, mathlib := "v4.9.0", tacticLib? := some "Invariant.lin@0.1" } }
    , model :=
      { id := "sir-demo"
        , species := ["S", "I", "R"]
        , parameters := Json.mkObj [("beta", Json.str "0.2"), ("gamma", Json.str "0.1")]
        , reactions := reactionEntries
        , units := Json.mkObj [("S", Json.str "count"), ("I", Json.str "count"), ("R", Json.str "count")] }
    }

end SIR
end Model
end Examples
end Biosim
