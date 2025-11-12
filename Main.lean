import Lean.Data.Json
import Biosim.IO.Shared
import Biosim.IO.Checks
import Biosim.IO.Certificate
import Biosim.IO.Importer
import Biosim.Examples.CertificateDemo
import Biosim.CLI.Verify

open Lean
open System
open Biosim.Examples.CertificateDemo
open Biosim.ProofCert
open Biosim.CLI
open Biosim.IO (SignatureMode)
open Biosim.IO.SignatureMode

def toolkitVersion : String := "0.10.2-pilot"

/-- CLI options for emitting artifacts. -/
structure CliConfig where
  outDir : FilePath := "artifacts"
  emitConfirmed : Bool := false
  pretty : Bool := true
  sigMode? : Option SignatureMode := none
  signKey? : Option FilePath := none
  signKid? : Option String := none
  deriving Inhabited

structure ImportConfig where
  input? : Option FilePath := none
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
    , "  veribiota import --in MODEL.json --emit-all [--out DIR]"
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

def importUsage : String :=
  String.intercalate "\n"
    [ "Model import usage:"
    , "  veribiota import --in MODEL.json --emit-all [--out DIR] [--compact]"
    , "    [--sig-mode MODE] [--sign-key PATH] [--sign-kid KID]"
    ]

def verifyUsage : String :=
  String.intercalate "\n"
    [ "Verification usage:"
    , "  veribiota verify (checks|cert) <path> --jwks JWKS [--sig-mode MODE] [--print-details]"
    , "  veribiota verify results <checks.json> <results.jsonl>"
    ]

def canonUsage : String :=
  "Usage: veribiota --canon <artifact.json> [--out output.json]"

/-- Simulation config for the minimal SIR demo. -/
structure SimConfig where
  steps : Nat := 80
  dt : Float := 0.25
  outPath? : Option FilePath := none
  ssa : Bool := false
  counts : Bool := false
  deriving Inhabited

def simUsage : String :=
  String.intercalate "\n"
    [ "Simulate usage:"
    , "  veribiota simulate [--steps N] [--dt SECS] [--out results.jsonl]"
    , "    Emits a minimal SIR trajectory and a JSONL results file, then verifies against checks."
    ]

partial def parseSimArgsAux : SimConfig → List String → Except String SimConfig
  | cfg, [] => Except.ok cfg
  | cfg, "--steps" :: n :: rest =>
      match n.toNat? with
      | some v => parseSimArgsAux { cfg with steps := v } rest
      | none => Except.error "--steps must be a natural number"
  | cfg, "--dt" :: s :: rest =>
      let parsed : Option Float :=
        match Lean.Json.parse s with
        | Except.ok (Lean.Json.num num) => some num.toFloat
        | _ => none
      match parsed with
      | some v => parseSimArgsAux { cfg with dt := v } rest
      | none => Except.error "--dt must be a JSON number (e.g., 0.25)"
  | cfg, "--ssa" :: rest =>
      parseSimArgsAux { cfg with ssa := true } rest
  | cfg, "--counts" :: rest =>
      parseSimArgsAux { cfg with counts := true } rest
  | cfg, "--out" :: path :: rest =>
      parseSimArgsAux { cfg with outPath? := some (FilePath.mk path) } rest
  | _, flag :: _ => Except.error s!"Unknown simulate option '{flag}'"

def parseSimArgs (args : List String) : Except String SimConfig :=
  parseSimArgsAux {} args

def sirStep (β γ : Float) (dt : Float) (S I R : Float) : (Float × Float × Float) :=
  -- Simple SIR with population-normalized infection
  let total := S + I + R
  let N := if total < 1.0 then 1.0 else total
  let inf := β * S * I / N
  let recov := γ * I
  let dS := -inf
  let dI := inf - recov
  let dR := recov
  (S + dt * dS, I + dt * dI, R + dt * dR)

-- SSA stub: discrete-like step using same hazard form but continuous update
def ssaStep (β γ : Float) (dt : Float) (S I R : Float) : (Float × Float × Float) :=
  sirStep β γ dt S I R

def jsonFromFloat! (x : Float) : Lean.Json :=
  match Lean.JsonNumber.fromFloat? x with
  | Sum.inr num => Lean.Json.num num
  | Sum.inl _ => Lean.Json.num (Lean.JsonNumber.fromInt 0)

def writeResultsJsonl (outPath : FilePath) (modelHash checksDigest : String)
    (samples : List (Float × Float × Float × Float)) (emitCounts : Bool) : IO Unit := do
  Biosim.IO.ensureParentDir outPath
  IO.FS.withFile outPath IO.FS.Mode.write fun h => do
    for (t, s, i, r) in samples do
      let line := Lean.Json.mkObj
        ([ ("t", jsonFromFloat! t)
         , ("conc", Lean.Json.arr #[
              jsonFromFloat! s
            , jsonFromFloat! i
            , jsonFromFloat! r ])
         , ("modelHash", Lean.Json.str modelHash)
         , ("checksDigest", Lean.Json.str checksDigest) ] ++
         (if emitCounts then
            [ ("counts", Lean.Json.arr #[
                  jsonFromFloat! s
                , jsonFromFloat! i
                , jsonFromFloat! r ]) ]
          else []))
      h.putStr (line.compress)
      h.putStr "\n"

def runSimulate (cfg : SimConfig) : IO UInt32 := do
  -- Ensure baseline artifacts exist (model/cert/checks) under build/artifacts
  let paths := Biosim.Examples.CertificateDemo.ArtifactPaths.fromRoot "build/artifacts"
  discard <| Biosim.Examples.CertificateDemo.saveArtifacts paths {}
  let checksPath := paths.checks
  let checksHex ← Biosim.IO.sha256Hex checksPath
  let checksDigest := s!"sha256:{checksHex}"
  -- Load model hash from certificate (or checks)
  let certJson ← do
    let s ← IO.FS.readFile paths.certificate
    match Lean.Json.parse s with
    | Except.ok j => pure j
    | Except.error err =>
        IO.eprintln s!"Failed to parse certificate JSON: {err}"
        return (1 : UInt32)
  let modelHash :=
    match certJson.getObjVal? "modelHash" with
    | Except.ok (Lean.Json.str s) => s
    | _ => "sha256:unknown"
  -- Parameters and initial conditions for demo SIR
  let β : Float := 0.2
  let γ : Float := 0.1
  let resultsPath := cfg.outPath?.getD (FilePath.mk "build/results/sir-sim.jsonl")
  if cfg.ssa then
    let mut t : Float := 0.0
    let mut S : Float := 999.0
    let mut I : Float := 1.0
    let mut R : Float := 0.0
    let mut samples : List (Float × Float × Float × Float) := []
    for _ in [0:cfg.steps] do
      samples := (t, S, I, R) :: samples
      let (S', I', R') := ssaStep β γ cfg.dt S I R
      t := t + cfg.dt
      S := S'
      I := I'
      R := R'
    let out := samples.reverse
    writeResultsJsonl resultsPath modelHash checksDigest out cfg.counts
    IO.println s!"simulate (SSA): wrote {out.length} snapshots to {resultsPath}"
    let (_, s0, i0, r0) := out.headD (0.0, 0.0, 0.0, 0.0)
    let (tLast, sN, iN, rN) := out.getLastD (0.0, 0.0, 0.0, 0.0)
    IO.println s!"t0: S={s0} I={i0} R={r0}"
    IO.println s!"tN={tLast}: S={sN} I={iN} R={rN}"
  else
    let mut t : Float := 0.0
    let mut S : Float := 999.0
    let mut I : Float := 1.0
    let mut R : Float := 0.0
    let mut samples : List (Float × Float × Float × Float) := []
    for _ in [0:cfg.steps] do
      samples := (t, S, I, R) :: samples
      let (S', I', R') := sirStep β γ cfg.dt S I R
      t := t + cfg.dt
      S := S'
      I := I'
      R := R'
    let out := samples.reverse
    writeResultsJsonl resultsPath modelHash checksDigest out cfg.counts
    IO.println s!"simulate (ODE): wrote {out.length} snapshots to {resultsPath}"
    let (_, s0, i0, r0) := out.headD (0.0, 0.0, 0.0, 0.0)
    let (tLast, sN, iN, rN) := out.getLastD (0.0, 0.0, 0.0, 0.0)
    IO.println s!"t0: S={s0} I={i0} R={r0}"
    IO.println s!"tN={tLast}: S={sN} I={iN} R={rN}"
  -- Print verification hint and attempt Rust evaluator if present
  IO.println s!"Verify: ./veribiota verify results {checksPath} {resultsPath}"
  let debugEval := FilePath.mk "target/debug/biosim-eval"
  let releaseEval := FilePath.mk "target/release/biosim-eval"
  let debugExists ← debugEval.pathExists
  let releaseExists ← releaseEval.pathExists
  if releaseExists then
    let child ← IO.Process.output
      { cmd := releaseEval.toString
        , args := #["--checks", checksPath.toString, "--results", resultsPath.toString] }
    IO.println child.stdout
  else if debugExists then
    let child ← IO.Process.output
      { cmd := debugEval.toString
        , args := #["--checks", checksPath.toString, "--results", resultsPath.toString] }
    IO.println child.stdout
  else
    IO.println "(optional) Build Rust evaluator: cargo build --manifest-path engine/biosim-checks/Cargo.toml --bin biosim-eval"
  pure 0
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
      if kid.trim.isEmpty then
        Except.error "--sign-kid value cannot be empty"
      else
        parseArgsAux { cfg with signKid? := some kid } showHelp rest
  | _, _, "--sign-kid" :: [] =>
      Except.error "Missing value after --sign-kid"
  | _, _, "--out" :: [] =>
      Except.error "Missing path after --out"
  | _, _, flag :: _ =>
      Except.error s!"Unknown flag '{flag}'"

def parseArgs (args : List String) : Except String (CliConfig × Bool) :=
  parseArgsAux {} false args

partial def parseImportArgsAux :
    ImportConfig → List String → Except String ImportConfig
  | cfg, [] =>
      match cfg.input? with
      | some _ => Except.ok cfg
      | none => Except.error "Missing model input (--in PATH)"
  | cfg, "--in" :: path :: rest =>
      parseImportArgsAux { cfg with input? := some (FilePath.mk path) } rest
  | _, "--in" :: [] =>
      Except.error "Missing value after --in"
  | cfg, "--emit-all" :: rest =>
      parseImportArgsAux { cfg with emitConfirmed := true } rest
  | cfg, "--emit-checks" :: rest =>
      parseImportArgsAux { cfg with emitConfirmed := true } rest
  | cfg, "--out" :: dir :: rest =>
      parseImportArgsAux { cfg with outDir := FilePath.mk dir } rest
  | _, "--out" :: [] =>
      Except.error "Missing path after --out"
  | cfg, "--compact" :: rest =>
      parseImportArgsAux { cfg with pretty := false } rest
  | cfg, "--sig-mode" :: mode :: rest =>
      match SignatureMode.ofString? mode with
      | some sig => parseImportArgsAux { cfg with sigMode? := some sig } rest
      | none => Except.error s!"Unknown signature mode '{mode}'"
  | _, "--sig-mode" :: [] =>
      Except.error "Missing value after --sig-mode"
  | cfg, "--sign-key" :: path :: rest =>
      parseImportArgsAux { cfg with signKey? := some (FilePath.mk path) } rest
  | _, "--sign-key" :: [] =>
      Except.error "Missing path after --sign-key"
  | cfg, "--sign-kid" :: kid :: rest =>
      if kid.trim.isEmpty then
        Except.error "--sign-kid value cannot be empty"
      else
        parseImportArgsAux { cfg with signKid? := some kid } rest
  | _, "--sign-kid" :: [] =>
      Except.error "Missing value after --sign-kid"
  | cfg, arg :: rest =>
      if cfg.input?.isNone then
        parseImportArgsAux { cfg with input? := some (FilePath.mk arg) } rest
      else
        Except.error s!"Unknown import option '{arg}'"

def parseImportArgs (args : List String) : Except String ImportConfig :=
  parseImportArgsAux {} args

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
  IO.println s!"canonicalization: {Biosim.IO.canonicalScheme} (newlineTerminated)"

def runImport (cfg : ImportConfig) : IO UInt32 := do
  if !cfg.emitConfirmed then
    IO.eprintln "Refusing to overwrite artifacts without --emit-all."
    IO.println importUsage
    return 1
  let some input := cfg.input?
    | do
        IO.eprintln "Missing model input (--in PATH)."
        return 1
  let spec ← Biosim.IO.Importer.fromFile input
  match Biosim.IO.Importer.validate spec with
  | Except.error err =>
      IO.eprintln s!"Model validation failed: {err}"
      return 1
  | Except.ok _ => pure ()
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
  let envKid? :=
    match ← IO.getEnv "VERIBIOTA_SIG_KID" with
    | some kid =>
        if kid.trim.isEmpty then none else some kid
    | none => none
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
    return 1
  else if sigMode.requiresSignature && signKid?.isNone then
    IO.eprintln "Signature mode requires --sign-kid (or VERIBIOTA_SIG_KID)."
    return 1
  let plan : SigningPlan :=
    { mode := sigMode
      , keyPath? := signKey?
      , kid? := signKid? }
  let paths := ArtifactPaths.fromRoot cfg.outDir spec.id
  let result ← saveArtifacts paths plan cfg.pretty spec
  IO.println s!"VeriBiota biosim toolkit v{toolkitVersion}"
  IO.println s!"Model JSON: {result.model}"
  IO.println s!"Certificate JSON: {result.certificate}"
  IO.println s!"Checks JSON: {result.checks}"
  IO.println s!"Checks digest: {result.checksDigest}"
  printShaLines result
  return 0

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
  | "simulate" :: rest =>
      match parseSimArgs rest with
      | Except.error err =>
          IO.eprintln err
          IO.println simUsage
          pure 1
      | Except.ok cfg =>
          runSimulate cfg
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
  | "import" :: rest =>
      match parseImportArgs rest with
      | Except.error err =>
          IO.eprintln err
          IO.println importUsage
          pure 1
      | Except.ok cfg =>
          runImport cfg
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
            let envKid? :=
              match ← IO.getEnv "VERIBIOTA_SIG_KID" with
              | some kid =>
                  if kid.trim.isEmpty then none else some kid
              | none => none
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
