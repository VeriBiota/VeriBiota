import Lean.Data.Json
import Biosim
import Biosim.IO.Checks
import Biosim.IO.Certificate
import Biosim.IO.Base64Url
import Biosim.Examples.CertificateDemo
import Biosim.CLI.Verify

open Lean
open System
open Biosim.IO
open Biosim.IO.Checks
open Biosim.IO.Base64Url
open Biosim.ProofCert
open Biosim.Examples.CertificateDemo
open Biosim.CLI

namespace Tests

private def assertM (cond : Bool) (msg : String) : IO Unit :=
  unless cond do
    throw <| IO.userError msg

private def assertEq {α} [DecidableEq α] (a b : α) (msg : String) : IO Unit :=
  assertM (decide (a = b)) msg

private def assertBytesEq (a b : ByteArray) (msg : String) : IO Unit := do
  if decide (a.data = b.data) then
    pure ()
  else
    throw <| IO.userError msg

private def readBytes (path : FilePath) : IO ByteArray :=
  IO.FS.readBinFile path

private def writeBytes (path : FilePath) (bytes : ByteArray) : IO Unit :=
  IO.FS.writeBinFile path bytes

private def withTestDir (tag : String) (k : FilePath → IO Unit) : IO Unit := do
  let parent := FilePath.mk "Tests/tmp" / tag
  IO.FS.createDirAll parent
  let nonce ← IO.rand 0 1000000
  let dir := parent / s!"case-{nonce}"
  IO.FS.createDirAll dir
  k dir

private def enforceCRLF (path : FilePath) : IO Unit := do
  let contents ← IO.FS.readFile path
  IO.FS.writeFile path (contents.replace "\n" "\r\n")

private def canonicalizeChecks (path : FilePath) : IO ByteArray := do
  let contents ← IO.FS.readFile path
  match Checks.Bundle.fromString? contents with
  | Except.error err => throw <| IO.userError s!"Failed to parse checks: {err}"
  | Except.ok bundle =>
      let bytes := (bundle.render true).toUTF8
      writeBytes path bytes
      pure bytes

private def canonicalizeCert (path : FilePath) : IO ByteArray := do
  let contents ← IO.FS.readFile path
  match Json.parse contents with
  | Except.error err => throw <| IO.userError s!"Failed to parse certificate: {err}"
  | Except.ok json =>
      match Certificate.fromJson? json with
      | Except.error err => throw <| IO.userError s!"Invalid certificate: {err}"
      | Except.ok cert =>
          let bytes := (cert.render true).toUTF8
          writeBytes path bytes
          pure bytes

private def runCmd (cmd : String) : IO Unit := do
  let child ← IO.Process.output { cmd := "bash", args := #["-lc", cmd] }
  if child.exitCode ≠ 0 then
    throw <| IO.userError s!"Command failed: {cmd}\n{child.stderr}"

private def ed25519SpkiPrefix : ByteArray :=
  ByteArray.mk
    #[0x30, 0x2a, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x03, 0x21, 0x00]

structure SigningFixture where
  root : FilePath
  checksPath : FilePath
  certPath : FilePath
  jwksPath : FilePath
  originalChecks : ByteArray
  originalCert : ByteArray

noncomputable def generateSignedArtifacts (dir : FilePath) :
    IO SigningFixture := do
  let keyPath := dir / "test-ed25519.pem"
  let pubDer := dir / "test-ed25519.der"
  let jwksPath := dir / "test-jwks.json"
  let kid := "tests-demo-kid"
  runCmd s!"openssl genpkey -algorithm ed25519 -out {keyPath.toString}"
  runCmd s!"openssl pkey -in {keyPath.toString} -pubout -outform DER -out {pubDer.toString}"
  let der ← IO.FS.readBinFile pubDer
  unless der.size = ed25519SpkiPrefix.size + 32 do
    throw <| IO.userError "Unexpected DER size for Ed25519 public key"
  let raw := der.extract ed25519SpkiPrefix.size der.size
  let x := Base64Url.encode raw
  let jwkJson :=
    Json.mkObj
      [ ("kty", Json.str "OKP")
      , ("crv", Json.str "Ed25519")
      , ("kid", Json.str kid)
      , ("x", Json.str x) ]
  let jwksJson :=
    Json.mkObj [("keys", Json.arr #[jwkJson])]
  IO.FS.writeFile jwksPath (jwksJson.pretty 2)
  let paths := Biosim.Examples.CertificateDemo.ArtifactPaths.fromRoot dir
  let plan : SigningPlan :=
    { mode := .signedSoft
      , keyPath? := some keyPath
      , kid? := some kid }
  discard <| Biosim.Examples.CertificateDemo.saveArtifacts paths plan
  let checksBytes ← readBytes paths.checks
  let certBytes ← readBytes paths.certificate
  pure
    { root := dir
      , checksPath := paths.checks
      , certPath := paths.certificate
      , jwksPath
      , originalChecks := checksBytes
      , originalCert := certBytes }

private def mutateChecks (path : FilePath)
    (f : Checks.Bundle → Except String Checks.Bundle) : IO Unit := do
  let contents ← IO.FS.readFile path
  match Checks.Bundle.fromString? contents with
  | Except.error err => throw <| IO.userError s!"Failed to parse checks: {err}"
  | Except.ok bundle =>
      match f bundle with
      | Except.error err => throw <| IO.userError err
      | Except.ok mutated =>
          IO.FS.writeFile path (mutated.render true)

private def mutatePayload (path : FilePath) : IO Unit :=
  mutateChecks path fun bundle =>
    Except.ok
      { bundle with generatedAt := bundle.generatedAt ++ "-tampered" }

private def mutateSignature (path : FilePath)
    (g : SignatureInfo → SignatureInfo) : IO Unit :=
  mutateChecks path fun bundle =>
    match bundle.signature? with
    | none => Except.error "Missing signature"
    | some sig =>
        Except.ok { bundle with signature? := some (g sig) }

private def dropSignature (path : FilePath) : IO Unit :=
  mutateChecks path fun bundle =>
    Except.ok { bundle with signature? := none }

private def readJson (path : FilePath) : IO Json := do
  let contents ← IO.FS.readFile path
  match Json.parse contents with
  | Except.ok json => pure json
  | Except.error err =>
      throw <| IO.userError s!"Failed to parse {path}: {err}"

private def parseJsonString (payload : String) : IO Json := do
  match Json.parse payload with
  | Except.ok json => pure json
  | Except.error err =>
      throw <| IO.userError s!"Failed to parse JSON payload: {err}"

private def getStringField (j : Json) (field : String) : IO String := do
  match j.getObjVal? field with
  | Except.ok (Json.str s) => pure s
  | Except.ok _ => throw <| IO.userError s!"Field '{field}' is not a string"
  | Except.error err => throw <| IO.userError s!"{err}"

private def getBoolField (j : Json) (field : String) : IO Bool := do
  match j.getObjVal? field with
  | Except.ok (Json.bool b) => pure b
  | Except.ok _ => throw <| IO.userError s!"Field '{field}' is not a boolean"
  | Except.error err => throw <| IO.userError s!"{err}"

private def arrayIncludes (arr : Json) (value : String) : Bool :=
  match arr with
  | Json.arr entries => entries.any fun j => j == Json.str value
  | _ => false

private def jsonArrayStrings (j : Json) : Except String (List String) :=
  match j with
  | Json.arr entries =>
      entries.toList.mapM fun entry =>
        match entry with
        | Json.str s => Except.ok s
        | _ => Except.error "Expected string entries"
  | _ => Except.error "Expected JSON array of strings"

private def containsSubstring (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def checkSemantics (j : Json) : IO Unit := do
  match j.getObjVal? "semantics" with
  | Except.ok arr =>
      assertM (arrayIncludes arr "CTMC") "Certificate semantics missing CTMC"
      assertM (arrayIncludes arr "ODE") "Certificate semantics missing ODE"
  | Except.error err =>
      throw <| IO.userError err

private def checkTheorems (j : Json) : IO Unit := do
  match j.getObjVal? "theorems" with
  | Except.ok (Json.arr entries) =>
      let names := entries.map fun entry =>
        match entry.getObjVal? "name" with
        | Except.ok (Json.str s) => s
        | _ => ""
      assertM (names.contains "infection_preserves_total")
        "Certificate missing infection invariant"
      assertM (names.contains "recovery_preserves_total")
        "Certificate missing recovery invariant"
  | _ => throw <| IO.userError "Certificate missing theorem entries"

private def readChecksString : IO String :=
  IO.FS.readFile Biosim.Examples.CertificateDemo.checksPath

private def goldenSample : Checks.Bundle :=
  { toolchain :=
      { lean := "4.12.0"
        , mathlib := "5f8c1ad"
        , tacticLib? := some "Invariant.lin@0.1" }
    , modelHash := "sha256:cafebabe0123456789cafebabe0123456789cafebabe0123456789cafebabe01"
    , generatedAt := "2025-11-10T17:00:00Z"
    , checks :=
        [ Check.positivityCounts { species := ["S", "I", "R"] }
        , Check.linearInvariant
            { name := "N"
              , proofId := "9c2a"
              , weights := [("S", 1), ("I", 1), ("R", 1)]
              , tolerance := { mode := .absolute, value := 0.0 }
              , strict := true }
        ]
    }

private def goldenPath : FilePath := "Tests/golden/checks_min.json"

private def assertGoldenSnapshot : IO Unit := do
  let expected ← IO.FS.readFile goldenPath
  let actual := goldenSample.render
  assertM (expected = actual) "Golden checks snapshot drifted"

private def roundTripChecks : IO Unit := do
  let contents ← readChecksString
  match Checks.Bundle.fromString? contents with
  | Except.error err =>
      throw <| IO.userError s!"Failed to parse emitted checks JSON: {err}"
  | Except.ok bundle =>
      assertM (bundle.render = contents)
        "Checks JSON is not stable under round-trip rendering"

private def corruptionTest : IO Unit := do
  let missingSchema :=
    String.intercalate "\n"
      [ "{"
      , "  \"modelHash\": \"sha256:0000\","
      , "  \"generatedAt\": \"now\","
      , "  \"toolchain\": {\"lean\":\"4\",\"mathlib\":\"x\"},"
      , "  \"checks\": []"
      , "}"
      ]
  match Checks.Bundle.fromString? missingSchema with
  | Except.ok _ =>
      throw <| IO.userError "Missing schema was not rejected"
  | Except.error err =>
      assertM (containsSubstring err "schema")
        "Missing schema error message not descriptive"
  let badHash :=
    String.intercalate "\n"
      [ "{"
      , "  \"schema\": \"veribiota.checks.v1\","
      , "  \"modelHash\": \"badhash\","
      , "  \"generatedAt\": \"now\","
      , "  \"toolchain\": {\"lean\":\"4\",\"mathlib\":\"x\"},"
      , "  \"checks\": []"
      , "}"
      ]
  match Checks.Bundle.fromString? badHash with
  | Except.ok _ =>
      throw <| IO.userError "Invalid hash format was not rejected"
  | Except.error err =>
      assertM (containsSubstring err "modelHash")
        "Invalid hash error message not descriptive"

private def largeModelTest : IO Unit := do
  let species :=
    (List.range 200).map fun idx => s!"X{idx}"
  let weights := species.map fun name => (name, 1)
  let zeros := String.mk (List.replicate 64 '0')
  let bundle : Checks.Bundle :=
    { toolchain := { lean := "4.9.0", mathlib := "demo", tacticLib? := some "Invariant.lin@0.1" }
      , modelHash := "sha256:" ++ zeros
      , generatedAt := "2026-01-01T00:00:00Z"
      , checks :=
          [ Check.positivityCounts { species := species }
          , Check.linearInvariant
              { name := "mass"
                , proofId := "demo.mass"
                , weights := weights
                , tolerance := { mode := .relative, value := 1e-9 }
                , strict := false }
          ]
      }
  let payload := bundle.render
  assertM (payload.length < 1500000)
    "Large checks bundle exceeded size guardrail"

private def schemaManifestGuard : IO Unit := do
  let manifestPath := FilePath.mk "profiles/manifest.json"
  let manifestExists ← manifestPath.pathExists
  assertM manifestExists s!"Missing profile manifest at {manifestPath}"
  let manifestJson ← readJson manifestPath
  let profiles :=
    [ ("global_affine_v1", "schemas/align/global_affine_v1.schema.json",
        ["VB_ALIGN_CORE_001", "VB_ALIGN_CORE_002"])
    , ("edit_script_v1", "schemas/edit/edit_script_v1.schema.json",
        ["VB_EDIT_001"])
    , ("edit_script_normal_form_v1", "schemas/edit/edit_script_normal_form_v1.schema.json",
        ["VB_EDIT_001", "VB_EDIT_002"])
    , ("prime_edit_plan_v1", "schemas/prime/prime_edit_plan_v1.schema.json",
        ["VB_PE_001", "VB_EDIT_001"])
    , ("pair_hmm_bridge_v1", "schemas/hmm/pair_hmm_bridge_v1.schema.json",
        ["VB_HMM_001", "VB_HMM_002"])
    , ("read_set_conservation_v1", "schemas/pipeline/read_set_conservation_v1.schema.json",
        ["VB_PIPE_001", "VB_PIPE_002"])
    , ("vcf_normalization_v1", "schemas/variant/vcf_normalization_v1.schema.json",
        ["VB_VCF_001", "VB_VCF_002"])
    , ("offtarget_score_sanity_v1", "schemas/crispr/offtarget_score_sanity_v1.schema.json",
        ["VB_OFF_001"])
    , ("snapshot_signature_v1", "schemas/provenance/snapshot_signature_v1.schema.json",
        ["VB_SIG_001"])
    ]
  for (name, schemaPathStr, expectedTheorems) in profiles do
    let entry ←
      match manifestJson.getObjVal? name with
      | Except.ok v => pure v
      | Except.error err =>
          throw <| IO.userError s!"Manifest missing {name}: {err}"
    match entry with
    | Json.obj _ =>
        let schemaHash ← getStringField entry "schema"
        let schemaPath := FilePath.mk schemaPathStr
        let schemaExists ← schemaPath.pathExists
        assertM schemaExists s!"Schema path not found for {name}: {schemaPathStr}"
        let actual ← Biosim.IO.sha256Hex schemaPath
        assertEq schemaHash s!"sha256:{actual}"
          s!"Schema hash mismatch for {name}"
        match entry.getObjVal? "theorems" with
        | Except.ok thJson =>
            match jsonArrayStrings thJson with
            | Except.ok ths =>
                assertM (ths = expectedTheorems)
                  s!"Theorem list mismatch for {name}"
            | Except.error err =>
                throw <| IO.userError s!"Invalid theorems for {name}: {err}"
        | Except.error err =>
            throw <| IO.userError s!"Missing theorem list for {name}: {err}"
    | _ =>
        throw <| IO.userError s!"Manifest entry for {name} must be an object"

private def snapshotSignatureTest : IO Unit := do
  let tmpDir := FilePath.mk "Tests/tmp/snapshot-signature"
  IO.FS.createDirAll tmpDir
  let fixturePath := FilePath.mk "Tests/profiles/global_affine_v1/match_pass.json"
  let fixtureJson ← readJson fixturePath
  let inputJson ←
    match fixtureJson.getObjVal? "input" with
    | Except.ok v => pure v
    | Except.error err => throw <| IO.userError s!"Fixture missing input: {err}"
  let inputPath := tmpDir / "input.json"
  IO.FS.writeFile inputPath (inputJson.pretty 2)
  let sigPath := tmpDir / "signature.json"
  let child ← IO.Process.output
    { cmd := "./veribiota"
      , args := #["check", "alignment", "global_affine_v1", inputPath.toString, "--snapshot-out", sigPath.toString]
      , stderr := .piped }
  assertEq child.exitCode.toNat 0 "Snapshot signature run failed"
  let sigExists ← sigPath.pathExists
  assertM sigExists s!"Snapshot signature not written to {sigPath}"
  let sigJson ← readJson sigPath
  let profile ← getStringField sigJson "snapshot_profile"
  assertEq profile "global_affine_v1" "Snapshot profile mismatch"
  let verification ← getStringField sigJson "verification_result"
  assertEq verification "passed" "Snapshot verification_result mismatch"
  let snapshotHash ← getStringField sigJson "snapshot_hash"
  let expectedHash := s!"sha256:{← Biosim.IO.sha256Hex inputPath}"
  assertEq snapshotHash expectedHash "Snapshot hash mismatch"
  let manifestJson ← readJson (FilePath.mk "profiles/manifest.json")
  let gaEntry ←
    match manifestJson.getObjVal? "global_affine_v1" with
    | Except.ok v => pure v
    | Except.error err => throw <| IO.userError s!"Manifest missing global_affine_v1: {err}"
  let schemaHash ← getStringField gaEntry "schema"
  let schemaPath ← getStringField gaEntry "schema_path"
  let sigSchema ← getStringField sigJson "schema_hash"
  assertEq sigSchema schemaHash "Snapshot schema hash mismatch"
  let sigSchemaId ← getStringField sigJson "schema_id"
  assertEq sigSchemaId schemaPath "Snapshot schema_id mismatch"
  let theoremsJson ←
    match sigJson.getObjVal? "theorem_ids" with
    | Except.ok v => pure v
    | Except.error err => throw <| IO.userError s!"Snapshot missing theorem_ids: {err}"
  let theorems ←
    match jsonArrayStrings theoremsJson with
    | Except.ok v => pure v
    | Except.error err => throw <| IO.userError s!"Snapshot theorem_ids invalid: {err}"
  assertM (theorems.contains "VB_ALIGN_CORE_001") "Snapshot missing VB_ALIGN_CORE_001"
  assertM (theorems.contains "VB_ALIGN_CORE_002") "Snapshot missing VB_ALIGN_CORE_002"
  match sigJson.getObjVal? "instance_summary" with
  | Except.ok (Json.obj _) => pure ()
  | _ => throw <| IO.userError "Snapshot missing instance_summary object"

private def assertJsonEq (expected actual : Json) (ctx : String) : IO Unit := do
  let expStr := expected.compress
  let actStr := actual.compress
  if expStr = actStr then
    pure ()
  else
    throw <| IO.userError s!"JSON mismatch for {ctx}"

private def runProfileGoldenSuite (profileName : String) (cliArgs : List String)
    (dir : FilePath) : IO Unit := do
  match ← IO.getEnv "VERIBIOTA_PROFILE_FILTER" with
  | some raw =>
      let filters := raw.splitOn "," |>.map String.trim |>.filter (· ≠ "")
      if filters ≠ [] && !(filters.contains profileName) then
        IO.println s!"[profile-test] skipping {profileName} (filtered)"
        return ()
      else
        pure ()
  | none => pure ()
  let dirExists ← dir.pathExists
  assertM dirExists s!"Profile fixtures missing at {dir}"
  let ls ← IO.Process.output
    { cmd := "bash"
      , args := #["-lc", s!"ls -1 {dir}/**/*.json"]
      , stderr := .piped }
  if ls.exitCode ≠ 0 then
    throw <| IO.userError s!"Failed to enumerate profile fixtures: {ls.stderr}"
  let cases := ls.stdout.splitOn "\n" |>.filter fun s => !s.trim.isEmpty
  assertM (cases.length > 0) "No profile fixtures found"
  let tmpDir := FilePath.mk "Tests/tmp/profile-fixtures"
  IO.FS.createDirAll tmpDir
  for pathStr in cases do
    let entryPath := FilePath.mk pathStr
    let payload ← IO.FS.readFile entryPath
    let parsed ← parseJsonString payload
    let input ←
      match parsed.getObjVal? "input" with
      | Except.ok v => pure v
      | Except.error err =>
          throw <| IO.userError s!"Fixture {entryPath} missing input: {err}"
    let expected ←
      match parsed.getObjVal? "expected" with
      | Except.ok v => pure v
      | Except.error err =>
          throw <| IO.userError s!"Fixture {entryPath} missing expected: {err}"
    let expectedExit : Nat :=
      match parsed.getObjValAs? Nat "exit" with
      | Except.ok v => v
      | Except.error _ => 0
    let base := entryPath.fileName.getD "case"
    let inputPath := tmpDir / s!"{base}.input.json"
    IO.FS.writeFile inputPath (input.pretty 2)
    let child ← IO.Process.output
      { cmd := "./veribiota"
        , args := (cliArgs ++ [inputPath.toString]).toArray
        , stderr := .piped }
    assertEq child.exitCode.toNat expectedExit
      s!"Unexpected exit for {entryPath}"
    let actualJson ← parseJsonString child.stdout
    assertJsonEq expected actualJson s!"{entryPath}"

private def checkRuntimeChecks (j : Json) : IO Unit := do
  match j.getObjVal? "checks" with
  | Except.ok (Json.arr entries) =>
      let hasCounts :=
        entries.any fun entry =>
          match entry.getObjVal? "type" with
          | Except.ok (Json.str ty) => ty = "positivity_counts"
          | _ => false
      let hasConc :=
        entries.any fun entry =>
          match entry.getObjVal? "type" with
          | Except.ok (Json.str ty) => ty = "positivity_conc"
          | _ => false
      let hasInvariant :=
        entries.any fun entry =>
          match entry.getObjVal? "type" with
          | Except.ok (Json.str ty) =>
              if ty = "lin_invariant" then
                match entry.getObjVal? "proofId" with
                | Except.ok (Json.str _) => true
                | _ => false
              else
                false
          | _ => false
      assertM hasCounts "Checks JSON missing positivity_counts entry"
      assertM hasConc "Checks JSON missing positivity_conc entry"
      assertM hasInvariant "Checks JSON missing lin_invariant entry with proofId"
  | _ => throw <| IO.userError "Checks JSON missing `checks` array"

noncomputable def determinismTest : IO Unit := do
  withTestDir "determinism" fun dir => do
    let paths := Biosim.Examples.CertificateDemo.ArtifactPaths.fromRoot dir
    discard <| Biosim.Examples.CertificateDemo.saveArtifacts paths {}
    let firstModel ← readBytes paths.model
    let firstCert ← readBytes paths.certificate
    let firstChecks ← readBytes paths.checks
    discard <| Biosim.Examples.CertificateDemo.saveArtifacts paths {}
    let secondModel ← readBytes paths.model
    let secondCert ← readBytes paths.certificate
    let secondChecks ← readBytes paths.checks
    assertBytesEq firstModel secondModel "Model JSON is not deterministic"
    assertBytesEq firstCert secondCert "Certificate JSON is not deterministic"
    assertBytesEq firstChecks secondChecks "Checks JSON is not deterministic"

noncomputable def crlfNormalizationTest : IO Unit := do
  withTestDir "crlf" fun dir => do
    let paths := Biosim.Examples.CertificateDemo.ArtifactPaths.fromRoot dir
    discard <| Biosim.Examples.CertificateDemo.saveArtifacts paths {}
    let origCert ← readBytes paths.certificate
    let origChecks ← readBytes paths.checks
    enforceCRLF paths.certificate
    enforceCRLF paths.checks
    let canonCert ← canonicalizeCert paths.certificate
    let canonChecks ← canonicalizeChecks paths.checks
    assertBytesEq canonCert origCert "Certificate canonicalization failed after CRLF"
    assertBytesEq canonChecks origChecks "Checks canonicalization failed after CRLF"

noncomputable def tamperExitCodesTest : IO Unit := do
  withTestDir "tamper" fun dir => do
    let fixture ← generateSignedArtifacts dir
    let cfg : VerifyConfig :=
      { kind := VerifyKind.checks
        , target := fixture.checksPath
        , jwksPath? := some fixture.jwksPath
        , sigMode := SignatureMode.signedEnforced }
    let okCode ← runVerify cfg
    assertEq okCode 0 "Expected verification success"
    mutatePayload fixture.checksPath
    let codePayload ← runVerify cfg
    assertEq codePayload exitHashMismatch
      "Payload tamper should trigger hash mismatch"
    writeBytes fixture.checksPath fixture.originalChecks
    mutateSignature fixture.checksPath fun sig =>
      { sig with jws := "A" ++ sig.jws.drop 1 }
    let codeSig ← runVerify cfg
    assertEq codeSig exitInvalidSignature
      "Signature tamper should trigger invalid signature"
    writeBytes fixture.checksPath fixture.originalChecks
    mutateSignature fixture.checksPath fun sig =>
      { sig with canonicalization := { sig.canonicalization with scheme := "veribiota-canon-vX" } }
    let codeCanon ← runVerify cfg
    assertEq codeCanon exitCanonicalMismatch
      "Canonical mismatch not detected"
    writeBytes fixture.checksPath fixture.originalChecks
    dropSignature fixture.checksPath
    let codeMissing ← runVerify cfg
    assertEq codeMissing exitMissingSignature
      "Missing signature not detected"

/-- Integration test: regenerate artifacts and validate metadata. -/
noncomputable def run : IO Unit := do
  determinismTest
  crlfNormalizationTest
  tamperExitCodesTest
  Biosim.Examples.CertificateDemo.saveDefaultArtifacts
  assertGoldenSnapshot
  let modelPath := Biosim.Examples.CertificateDemo.modelPath
  let certPath := Biosim.Examples.CertificateDemo.certificatePath
  let checksPath := Biosim.Examples.CertificateDemo.checksPath
  let modelExists ← modelPath.pathExists
  assertM modelExists s!"Model artifact missing at {modelPath}"
  let certExists ← certPath.pathExists
  assertM certExists s!"Certificate artifact missing at {certPath}"
  let checksExists ← checksPath.pathExists
  assertM checksExists s!"Checks artifact missing at {checksPath}"
  let shaPath := checksPath.addExtension "sha256"
  let shaExists ← shaPath.pathExists
  assertM shaExists s!"Checks digest missing at {shaPath}"
  let modelJson ← readJson modelPath
  let certJson ← readJson certPath
  let checksJson ← readJson checksPath
  let modelHash ← getStringField modelJson "hash"
  let certHash ← getStringField certJson "modelHash"
  let checksHash ← getStringField checksJson "modelHash"
  assertM (modelHash = certHash) "Certificate modelHash does not match model artifact hash"
  assertM (modelHash = checksHash) "Checks modelHash does not match model artifact hash"
  checkSemantics certJson
  checkTheorems certJson
  checkRuntimeChecks checksJson
  roundTripChecks
  corruptionTest
  largeModelTest
  schemaManifestGuard
  snapshotSignatureTest
  runProfileGoldenSuite "global_affine_v1" ["check", "alignment", "global_affine_v1"]
    (FilePath.mk "Tests/profiles/global_affine_v1")
  runProfileGoldenSuite "edit_script_v1" ["check", "edit", "edit_script_v1"]
    (FilePath.mk "Tests/profiles/edit_script_v1")
  runProfileGoldenSuite "edit_script_normal_form_v1" ["check", "edit", "edit_script_normal_form_v1"]
    (FilePath.mk "Tests/profiles/edit_script_normal_form_v1")
  runProfileGoldenSuite "prime_edit_plan_v1" ["check", "prime", "prime_edit_plan_v1"]
    (FilePath.mk "Tests/profiles/prime_edit_plan_v1")
  runProfileGoldenSuite "pair_hmm_bridge_v1" ["check", "hmm", "pair_hmm_bridge_v1"]
    (FilePath.mk "Tests/profiles/pair_hmm_bridge_v1")
  runProfileGoldenSuite "vcf_normalization_v1" ["check", "vcf", "vcf_normalization_v1"]
    (FilePath.mk "Tests/profiles/vcf_normalization_v1")
  IO.println "Artifact integration test passed"

noncomputable unsafe def main : IO Unit :=
  run

end Tests
