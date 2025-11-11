import Lean.Data.Json
import Biosim.IO.Shared
import Biosim.IO.Checks
import Biosim.IO.Certificate
import Biosim.Examples.CertificateDemo
import Biosim.CLI.Verify

open Lean
open System
open Biosim.Examples.CertificateDemo
open Biosim.ProofCert
open Biosim.CLI
open Biosim.IO (SignatureMode)
open Biosim.IO.SignatureMode

def toolkitVersion : String := "0.10.1-pilot"

/-- CLI options for emitting artifacts. -/
structure CliConfig where
  outDir : FilePath := "artifacts"
  emitConfirmed : Bool := false
  pretty : Bool := true
  sigMode? : Option SignatureMode := none
  signKey? : Option FilePath := none
  signKid? : Option String := none
  deriving Inhabited

def usage : String :=
  String.intercalate "\n"
    [ "Usage:"
    , "  veribiota --emit-all [--out DIR] [--sig-mode MODE] [--sign-key PATH] [--sign-kid KID]"
    , "  veribiota verify (checks|cert) <path> --jwks JWKS [--sig-mode MODE] [--print-details]"
    , "  veribiota verify results <checks.json> <results.jsonl>"
    , "  veribiota --canon <artifact.json> [--out OUTPUT]"
    , "  veribiota --checks-schema"
    , ""
    , "Common options:"
    , "  --emit-all / --emit-checks  Allow overwriting artifacts (required for emit)."
    , "  --out DIR                  Override artifact directory (default: artifacts)."
    , "  --sig-mode MODE            unsigned | signed-soft | signed-enforced."
    , "  --sign-key PATH            Ed25519 private key (required in signed modes)."
    , "  --sign-kid ID              Key identifier recorded in signatures."
    , "  --compact                  Emit minified JSON."
    ]

def verifyUsage : String :=
  String.intercalate "\n"
    [ "Verification usage:"
    , "  veribiota verify (checks|cert) <path> --jwks JWKS [--sig-mode MODE] [--print-details]"
    , "  veribiota verify results <checks.json> <results.jsonl>"
    ]

def canonUsage : String :=
  "Usage: veribiota --canon <artifact.json> [--out output.json]"

def parseVerifyKind : String → Except String VerifyKind
  | "checks" => Except.ok .checks
  | "cert" => Except.ok .cert
  | other => Except.error s!"Unknown verification target '{other}'"

partial def parseArgsAux : CliConfig → Bool → List String →
    Except String (CliConfig × Bool)
  | cfg, showHelp, [] => Except.ok (cfg, showHelp)
  | cfg, _, "--help" :: _ => Except.ok (cfg, true)
  | cfg, showHelp, "--emit-checks" :: rest =>
      parseArgsAux { cfg with emitConfirmed := true } showHelp rest
  | cfg, showHelp, "--emit-all" :: rest =>
      parseArgsAux { cfg with emitConfirmed := true } showHelp rest
  | cfg, showHelp, "--compact" :: rest =>
      parseArgsAux { cfg with pretty := false } showHelp rest
  | cfg, showHelp, "--out" :: dir :: rest =>
      parseArgsAux { cfg with outDir := FilePath.mk dir } showHelp rest
  | cfg, showHelp, "--sig-mode" :: mode :: rest =>
      match SignatureMode.ofString? mode with
      | some sigMode =>
          parseArgsAux { cfg with sigMode? := some sigMode } showHelp rest
      | none =>
          Except.error s!"Unknown signature mode '{mode}'"
  | _, _, "--sig-mode" :: [] =>
      Except.error "Missing value after --sig-mode"
  | cfg, showHelp, "--sign-key" :: path :: rest =>
      parseArgsAux { cfg with signKey? := some (FilePath.mk path) } showHelp rest
  | _, _, "--sign-key" :: [] =>
      Except.error "Missing path after --sign-key"
  | cfg, showHelp, "--sign-kid" :: kid :: rest =>
      parseArgsAux { cfg with signKid? := some kid } showHelp rest
  | _, _, "--sign-kid" :: [] =>
      Except.error "Missing value after --sign-kid"
  | _, _, "--out" :: [] =>
      Except.error "Missing path after --out"
  | _, _, flag :: _ =>
      Except.error s!"Unknown flag '{flag}'"

def parseArgs (args : List String) : Except String (CliConfig × Bool) :=
  parseArgsAux {} false args

partial def parseVerifyArgsAux (cfg : VerifyConfig) :
    List String → Except String VerifyConfig
  | [] => Except.ok cfg
  | "--jwks" :: path :: rest =>
      parseVerifyArgsAux { cfg with jwksPath? := some (FilePath.mk path) } rest
  | "--jwks" :: [] =>
      Except.error "Missing path after --jwks"
  | "--sig-mode" :: mode :: rest =>
      match SignatureMode.ofString? mode with
      | some sig => parseVerifyArgsAux { cfg with sigMode := sig } rest
      | none => Except.error s!"Unknown signature mode '{mode}'"
  | "--sig-mode" :: [] =>
      Except.error "Missing value after --sig-mode"
  | "--print-details" :: rest =>
      parseVerifyArgsAux { cfg with printDetails := true } rest
  | flag :: _ =>
      Except.error s!"Unknown verify option '{flag}'"

def parseVerifyArgs : List String → Except String VerifyConfig
  | kindStr :: pathStr :: rest => do
      let kind ← parseVerifyKind kindStr
      let base : VerifyConfig :=
        { kind := kind
          , target := FilePath.mk pathStr }
      parseVerifyArgsAux base rest
  | _ => Except.error verifyUsage

def printShaLines (result : EmitResult) : IO Unit := do
  let certSha ← Biosim.IO.sha256Hex result.certificate
  let checksSha ← Biosim.IO.sha256Hex result.checks
  IO.println s!"SHA256 {result.certificate}={certSha}"
  IO.println s!"SHA256 {result.checks}={checksSha}"

def biosimMain (cfg : CliConfig) (plan : SigningPlan) : IO Unit := do
  let paths := ArtifactPaths.fromRoot cfg.outDir
  let result ← saveArtifacts paths plan cfg.pretty
  IO.println s!"VeriBiota biosim toolkit v{toolkitVersion}"
  IO.println s!"Model JSON: {result.model}"
  IO.println s!"Certificate JSON: {result.certificate}"
  IO.println s!"Checks JSON: {result.checks}"
  IO.println s!"Checks digest: {result.checksDigest}"
  printShaLines result

def canonicalizeArtifact (input : FilePath) (output? : Option FilePath := none) :
    IO Unit := do
  let contents ← IO.FS.readFile input
  let canonical :=
    match Biosim.IO.Checks.Bundle.fromString? contents with
    | Except.ok bundle => Except.ok (bundle.render true)
    | Except.error _ =>
        match Json.parse contents with
        | Except.error err => Except.error err
        | Except.ok json =>
            match Certificate.fromJson? json with
            | Except.ok cert =>
                let rendered := cert.render true
                let normalized :=
                  if rendered.endsWith "\n" then rendered else rendered ++ "\n"
                Except.ok normalized
            | Except.error err => Except.error err
  match canonical with
  | Except.error err =>
      throw <| IO.userError s!"Failed to canonicalize {input}: {err}"
  | Except.ok payload =>
      let outPath :=
        match output? with
        | some explicit => explicit
        | none => input.withExtension "canon.json"
      IO.FS.createDirAll (outPath.parent.getD (FilePath.mk "."))
      IO.FS.writeFile outPath payload
      IO.println s!"Canonical artifact written to {outPath}"

def describeSchema : IO Unit := do
  IO.println "veribiota.checks.v1"
  IO.println "canonicalization: veribiota-canon-v1 (newlineTerminated)"

def verifyResults (checksPath resultsPath : FilePath) : IO UInt32 := do
  let checksPayload ← IO.FS.readFile checksPath
  let bundle ←
    match Biosim.IO.Checks.Bundle.fromString? checksPayload with
    | Except.ok b => pure b
    | Except.error err =>
        IO.eprintln s!"Failed to parse checks: {err}"
        return (1 : UInt32)
  let digestTag := s!"sha256:{← Biosim.IO.sha256Hex checksPath}"
  let contents ← IO.FS.readFile resultsPath
  let lines := contents.splitOn "\n"
  let mut lineNo := 0
  let mut processed := 0
  for line in lines do
    lineNo := lineNo + 1
    let trimmed := line.trim
    if trimmed.isEmpty then
      continue
    processed := processed + 1
    let json ←
      match Json.parse trimmed with
      | Except.ok j => pure j
      | Except.error err =>
          IO.eprintln s!"Invalid JSON on line {lineNo}: {err}"
          return (1 : UInt32)
    let modelHash ←
      match json.getObjVal? "modelHash" with
      | Except.ok (Json.str s) => pure s
      | _ =>
          IO.eprintln s!"Missing modelHash on line {lineNo}"
          return (1 : UInt32)
    if modelHash ≠ bundle.modelHash then
      IO.eprintln s!"modelHash mismatch on line {lineNo}: expected {bundle.modelHash}, found {modelHash}"
      return (1 : UInt32)
    let digest? :=
      match json.getObjVal? "checksDigest" with
      | Except.ok (Json.str s) => some s
      | _ =>
          match json.getObjVal? "checksSha256" with
          | Except.ok (Json.str s) => some s
          | _ => none
    match digest? with
    | some value =>
        if value ≠ digestTag then
          IO.eprintln s!"checks digest mismatch on line {lineNo}: expected {digestTag}, found {value}"
          return (1 : UInt32)
    | none => pure ()
  IO.println s!"Results OK: {resultsPath} ({processed} records, modelHash {bundle.modelHash})"
  return (0 : UInt32)

def parseCanonCommand : List String → Except String (FilePath × Option FilePath)
  | input :: rest =>
      let rec loop (out? : Option FilePath) : List String → Except String (Option FilePath)
        | [] => Except.ok out?
        | "--out" :: value :: tl => loop (some (FilePath.mk value)) tl
        | flag :: _ => Except.error s!"Unknown canon option '{flag}'"
      do
        let out? ← loop none rest
        pure (FilePath.mk input, out?)
  | [] => Except.error canonUsage

def runCli (args : List String) : IO UInt32 := do
  match args with
  | "--checks-schema" :: _ =>
      describeSchema
      pure 0
  | "--canon" :: rest =>
      match parseCanonCommand rest with
      | Except.error err =>
          IO.eprintln err
          IO.println canonUsage
          pure 1
      | Except.ok (input, out?) =>
          try
            canonicalizeArtifact input out?
            pure 0
          catch err =>
            IO.eprintln s!"{err}"
            pure 1
  | "verify" :: "results" :: checks :: results :: trailing =>
      if trailing ≠ [] then
        IO.eprintln verifyUsage
        pure 1
      else
        verifyResults (FilePath.mk checks) (FilePath.mk results)
  | "verify" :: rest =>
      match parseVerifyArgs rest with
      | Except.error err =>
          IO.eprintln err
          IO.println verifyUsage
          pure 1
      | Except.ok cfg =>
          runVerify cfg
  | _ =>
      match parseArgs args with
      | Except.error err =>
          IO.eprintln err
          IO.println usage
          pure 1
      | Except.ok (_, true) =>
          IO.println usage
          pure 0
      | Except.ok (cfg, false) =>
          if !cfg.emitConfirmed then
            IO.eprintln "Refusing to overwrite artifacts without --emit-all (or --emit-checks)."
            IO.println usage
            pure 1
          else
            let sigEnv? ← IO.getEnv "VERIBIOTA_SIG_MODE"
            let envMode? ←
              match sigEnv? with
              | none => pure none
              | some raw =>
                  match SignatureMode.ofString? raw with
                  | some mode => pure (some mode)
                  | none => do
                      IO.eprintln s!"Ignoring unknown VERIBIOTA_SIG_MODE='{raw}'"
                      pure none
            let chosenMode? :=
              match cfg.sigMode? with
              | some mode => some mode
              | none => envMode?
            let sigMode := chosenMode?.getD SignatureMode.unsigned
            let envKey? ← IO.getEnv "VERIBIOTA_SIG_KEY"
            let envKid? ← IO.getEnv "VERIBIOTA_SIG_KID"
            let signKey? :=
              match cfg.signKey? with
              | some k => some k
              | none => envKey?.map FilePath.mk
            let signKid? :=
              match cfg.signKid? with
              | some kid => some kid
              | none => envKid?
            if sigMode.requiresSignature && signKey?.isNone then
              IO.eprintln "Signature mode requires --sign-key (or VERIBIOTA_SIG_KEY)."
              pure 1
            else if sigMode.requiresSignature && signKid?.isNone then
              IO.eprintln "Signature mode requires --sign-kid (or VERIBIOTA_SIG_KID)."
              pure 1
            else
              let plan : SigningPlan :=
                { mode := sigMode
                  , keyPath? := signKey?
                  , kid? := signKid? }
              biosimMain cfg plan
              pure 0

def argsFromEnv (cliArgs : List String) : IO (List String) := do
  match ← IO.getEnv "VERIBIOTA_ARGS_JSON" with
  | none => pure cliArgs
  | some raw =>
      match Json.parse raw with
      | Except.ok (Json.arr arr) =>
          let rec loop (items : List Json) (acc : List String) :
              Except String (List String) :=
            match items with
            | [] => Except.ok acc.reverse
            | Json.str s :: tl => loop tl (s :: acc)
            | _ :: _ => Except.error "CLI args must be strings"
          match loop arr.data [] with
          | Except.ok args => pure args
          | Except.error err =>
              IO.eprintln s!"Failed to decode VERIBIOTA_ARGS_JSON: {err}"
              pure []
      | Except.ok _ =>
          IO.eprintln "VERIBIOTA_ARGS_JSON must be a JSON array"
          pure []
      | Except.error err =>
          IO.eprintln s!"Invalid VERIBIOTA_ARGS_JSON: {err}"
          pure []

unsafe def main (cliArgs : List String) : IO Unit := do
  let args ← argsFromEnv cliArgs
  let code ← runCli args
  if code = 0 then
    pure ()
  else
    IO.Process.exit (UInt8.ofNat code.toNat)
