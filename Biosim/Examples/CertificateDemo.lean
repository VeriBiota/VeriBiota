import Lean.Data.Json
import Biosim.IO.Certificate
import Biosim.IO.Model
import Biosim.IO.Checks
import Biosim.IO.Base64Url
import Biosim.Examples.Model.SIR

open System

namespace Biosim
namespace Examples
namespace CertificateDemo

open ProofCert
open IO
open IO.Model
open IO.Checks
open Biosim.IO
open Biosim.IO.Base64Url
open Lean

/-- Signature plan describing how (or whether) artifacts are signed. -/
structure SigningPlan where
  mode : IO.SignatureMode := .unsigned
  kid? : Option String := none
  keyPath? : Option System.FilePath := none

instance : Inhabited SigningPlan := ⟨{}⟩

@[inline] def SigningPlan.requiresSignature (plan : SigningPlan) : Bool :=
  plan.mode.requiresSignature

private def shellQuote (s : String) : String :=
  "\"" ++ (s.replace "\"" "\\\"") ++ "\""

private def runOpensslSign (keyPath payloadPath : System.FilePath) :
    IO String := do
  let opensslEnv ← IO.getEnv "VERIBIOTA_OPENSSL"
  let opensslBin := opensslEnv.getD "openssl"
  let opensslQuoted := shellQuote opensslBin
  let baseCmds :=
    [ s!"set -o pipefail && {opensslQuoted} pkeyutl -sign -inkey {shellQuote keyPath.toString} -rawin -pkeyopt digest:none -in {shellQuote payloadPath.toString} | {opensslQuoted} base64 -A"
    , s!"set -o pipefail && {opensslQuoted} pkeyutl -sign -inkey {shellQuote keyPath.toString} -rawin -in {shellQuote payloadPath.toString} | {opensslQuoted} base64 -A" ]
  let rec loop
      | [] =>
          throw <| IO.userError "Signing failed: openssl unavailable or unsupported Ed25519 configuration."
      | cmd :: rest => do
          let child ← IO.Process.output { cmd := "bash", args := #["-lc", cmd] }
          if child.exitCode = 0 then
            pure child.stdout.trim
          else
            loop rest
  loop baseCmds

private def SigningPlan.signPayload (plan : SigningPlan)
    (hintPath : System.FilePath) (payload : ByteArray)
    (payloadHash : String) (canon : Biosim.IO.CanonicalizationInfo) :
    IO (Option IO.SignatureInfo) := do
  if !plan.requiresSignature then
    return none
  let some keyPath := plan.keyPath?
    | throw <| IO.userError "--sign-key required for selected signature mode"
  let some kid := plan.kid?
    | throw <| IO.userError "--sign-kid required for selected signature mode"
  if canon.scheme ≠ Biosim.IO.canonicalScheme then
    throw <| IO.userError s!"Canonicalization scheme mismatch (expected {Biosim.IO.canonicalScheme}, found {canon.scheme})"
  if canon.newlineTerminated = false then
    throw <| IO.userError "Canonicalization must be newline-terminated"
  if payload.size == 0 then
    throw <| IO.userError "Canonical payload cannot be empty"
  let lastByte := payload.get! (payload.size - 1)
  if lastByte ≠ 0x0A then
    throw <| IO.userError "Canonical payload must end with LF (0x0A)"
  let headerJson :=
    Json.mkObj
      [ ("alg", Json.str "EdDSA")
      , ("kid", Json.str kid)
      , ("typ", Json.str "JWT")
      , ("veribiotaCanon", Json.str Biosim.IO.canonicalScheme) ]
  let headerBytes := headerJson.compress.toUTF8
  let headerB64 := Base64Url.encode headerBytes
  let payloadB64 := Base64Url.encode payload
  let signingInput := s!"{headerB64}.{payloadB64}"
  let signingBytes := signingInput.toUTF8
  let tmp := Biosim.IO.tmpPath hintPath
  Biosim.IO.ensureParentDir tmp
  IO.FS.writeBinFile tmp signingBytes
  let signatureStd ←
    try runOpensslSign keyPath tmp
    finally
      try IO.FS.removeFile tmp catch _ => pure ()
  let signatureB64 := Base64Url.fromStandard signatureStd
  let issuedAt ← Biosim.IO.currentIsoTimestamp
  let jws := s!"{headerB64}.{payloadB64}.{signatureB64}"
  let sig : IO.SignatureInfo :=
    { alg := "Ed25519"
      , kid
      , issuedAt
      , payloadHash
      , canonicalization := canon
      , jws }
  pure <| some sig
def toolchainSnapshot : Biosim.IO.ToolchainInfo :=
  { lean := Lean.versionString
    , mathlib := "v4.9.0"
    , tacticLib? := some "Invariant.lin@0.1" }

def theoremEntries : List TheoremRecord :=
  [ { name := "infection_preserves_total"
      , statement := "totalPopulationInv conserved by infection"
      , proofId := "Biosim.Examples.SIR.infection_preserves_total" }
  , { name := "recovery_preserves_total"
      , statement := "totalPopulationInv conserved by recovery"
      , proofId := "Biosim.Examples.SIR.recovery_preserves_total" }
  ]

def parameterJson (β γ : String) : Json :=
  Json.mkObj [("beta", Json.str β), ("gamma", Json.str γ)]

def sirCertificate (βLabel γLabel modelHash : String) : Certificate :=
  { modelId? := some "sir-demo"
    , modelHash := modelHash
    , semantics := ["CTMC", "ODE"]
    , toolchain := toolchainSnapshot
    , theorems := theoremEntries
    , timestamp := "2026-01-01T00:00:00Z"
    , parameters? := some (parameterJson βLabel γLabel)
    , limits? := some { domain := "counts", assumptions := ["rates ≥ 0"] }
    , signature? := none }

/-- Concrete artifact layout used by the CLI and tests. -/
structure ArtifactPaths where
  root : FilePath
  model : FilePath
  certificate : FilePath
  checks : FilePath
  deriving Repr

namespace ArtifactPaths

def fromRoot (root : FilePath) (stem : String := "sir-demo") : ArtifactPaths :=
  let base := root.normalize
  let file := s!"{stem}.json"
  { root := base
    , model := base / "models" / file
    , certificate := base / "certificates" / file
    , checks := base / "checks" / file }

def default : ArtifactPaths :=
  fromRoot "artifacts"

end ArtifactPaths

def modelPath : FilePath := ArtifactPaths.default.model
def certificatePath : FilePath := ArtifactPaths.default.certificate
def checksPath : FilePath := ArtifactPaths.default.checks

def sirCheckerBundle (modelHash : String) : Checks.Bundle :=
  { modelHash := modelHash
    , toolchain := toolchainSnapshot
    , generatedAt := "2026-01-01T00:00:00Z"
    , checks :=
        [ Check.positivityCounts { species := ["S", "I", "R"] }
        , Check.positivityConcentration { species := ["S", "I", "R"], tolerance := 1e-12 }
        , Check.linearInvariant
            { name := "infection_preserves_total"
              , proofId := "Biosim.Examples.SIR.infection_preserves_total"
              , weights := [("S", 1), ("I", 1), ("R", 1)]
              , tolerance := { mode := .absolute, value := 0.0 }
              , strict := true }
        , Check.linearInvariant
            { name := "recovery_preserves_total"
              , proofId := "Biosim.Examples.SIR.recovery_preserves_total"
              , weights := [("S", 1), ("I", 1), ("R", 1)]
              , tolerance := { mode := .absolute, value := 0.0 }
              , strict := true }
        ]
    }

structure EmitResult where
  model : System.FilePath
  certificate : System.FilePath
  checks : System.FilePath
  checksDigest : String
  deriving Repr

def saveArtifacts (paths : ArtifactPaths)
    (plan : SigningPlan := {}) (pretty := true)
    (modelSpec : IO.Model.Spec := Biosim.Examples.Model.SIR.spec) :
    IO EmitResult := do
  let modelDoc ← Model.save paths.model modelSpec pretty
  let baseCert :=
    { (sirCertificate "0.2" "0.1" modelDoc.hash)
        with signature? := none }
  let certCanonical := baseCert.render pretty
  let certBytes := certCanonical.toUTF8
  let certHashHex ← Biosim.IO.sha256HexBytesNear paths.certificate certBytes
  let certPayloadHash := s!"sha256:{certHashHex}"
  let certSig? ←
    plan.signPayload paths.certificate certBytes certPayloadHash baseCert.canonicalization
  let finalCert := { baseCert with signature? := certSig? }
  let finalCertBytes := (finalCert.render pretty).toUTF8
  discard <| Biosim.IO.writeFileWithSha paths.certificate finalCertBytes
  let unsignedBundle := { (sirCheckerBundle modelDoc.hash) with signature? := none }
  let bundleCanonical := unsignedBundle.render pretty
  let bundleBytes := bundleCanonical.toUTF8
  let bundleHashHex ← Biosim.IO.sha256HexBytesNear paths.checks bundleBytes
  let bundlePayloadHash := s!"sha256:{bundleHashHex}"
  let bundleSig? ←
    plan.signPayload paths.checks bundleBytes bundlePayloadHash unsignedBundle.canonicalization
  let finalBundle := { unsignedBundle with signature? := bundleSig? }
  let finalBundleBytes := (finalBundle.render pretty).toUTF8
  let digest ← Biosim.IO.writeFileWithSha paths.checks finalBundleBytes
  pure
    { model := paths.model
      , certificate := paths.certificate
      , checks := paths.checks
      , checksDigest := digest }

def saveDefaultArtifacts : IO Unit := do
  discard <| saveArtifacts ArtifactPaths.default {}

end CertificateDemo
end Examples
end Biosim
