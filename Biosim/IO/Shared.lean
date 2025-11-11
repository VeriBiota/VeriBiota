import Lean.Data.Json
open System
open Lean

namespace Biosim
namespace IO

/-- Signature enforcement mode for artifact emission. -/
inductive SignatureMode
  | unsigned
  | signedSoft
  | signedEnforced
  deriving DecidableEq, Repr

namespace SignatureMode

def ofString? (input : String) : Option SignatureMode :=
  let normalized := input.trim.map Char.toLower
  match normalized with
  | "unsigned" => some .unsigned
  | "signed-soft" => some .signedSoft
  | "signed_enforced" => some .signedEnforced
  | "signed-enforced" => some .signedEnforced
  | "signedsoft" => some .signedSoft
  | "signedenforced" => some .signedEnforced
  | _ => none

def requiresSignature : SignatureMode → Bool
  | .unsigned => false
  | _ => true

def description (mode : SignatureMode) : String :=
  match mode with
  | .unsigned => "unsigned"
  | .signedSoft => "signed-soft"
  | .signedEnforced => "signed-enforced"

end SignatureMode

/-- Toolchain metadata propagated into every artifact. -/
structure ToolchainInfo where
  lean : String
  mathlib : String
  tacticLib? : Option String := none
  deriving Repr

/-- Canonicalization metadata recorded alongside signatures. -/
structure CanonicalizationInfo where
  scheme : String
  newlineTerminated : Bool := true
  deriving Repr

/-- Signature block shared by certificates and checks bundles. -/
structure SignatureInfo where
  alg : String
  kid : String
  issuedAt : String
  payloadHash : String
  canonicalization : CanonicalizationInfo
  jws : String
  deriving Repr

namespace ToolchainInfo

/-- Canonical JSON shape used by most artifacts (certificates/models). -/
def toJson (info : ToolchainInfo) : Json :=
  Json.mkObj <|
    [("lean", Json.str info.lean), ("mathlib", Json.str info.mathlib)]
    ++ match info.tacticLib? with
      | none => []
      | some v => [("tacticLib", Json.str v)]

def fromJson? (json : Json) : Except String ToolchainInfo := do
  let lean ←
    match json.getObjVal? "lean" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "toolchain.lean must be a string"
  let mathlib ←
    match json.getObjVal? "mathlib" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "toolchain.mathlib must be a string"
  let tacticLib? :=
    match json.getObjVal? "tacticLib" with
    | Except.ok (Json.str s) => some s
    | _ => none
  pure { lean, mathlib, tacticLib? }

/-- JSON encoding specialized for runtime check bundles. -/
def toChecksJson (info : ToolchainInfo) : Json :=
  Json.mkObj <|
    [("lean", Json.str info.lean), ("mathlib", Json.str info.mathlib)]
    ++ match info.tacticLib? with
      | none => []
      | some v => [("tactics", Json.str v)]

end ToolchainInfo

namespace CanonicalizationInfo

def toJson (info : CanonicalizationInfo) : Json :=
  Json.mkObj
    [ ("scheme", Json.str info.scheme)
    , ("newlineTerminated", Json.bool info.newlineTerminated) ]

def fromJson? (json : Json) : Except String CanonicalizationInfo := do
  let scheme ←
    match json.getObjVal? "scheme" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "canonicalization.scheme must be a string"
  let newline ←
    match json.getObjVal? "newlineTerminated" with
    | Except.ok (Json.bool b) => pure b
    | _ => pure true
  pure { scheme, newlineTerminated := newline }

end CanonicalizationInfo

namespace SignatureInfo

def toJson (info : SignatureInfo) : Json :=
  Json.mkObj
    [ ("alg", Json.str info.alg)
    , ("kid", Json.str info.kid)
    , ("issuedAt", Json.str info.issuedAt)
    , ("payloadHash", Json.str info.payloadHash)
    , ("canonicalization", info.canonicalization.toJson)
    , ("jws", Json.str info.jws) ]

open Lean in
def fromJson? (json : Json) : Except String SignatureInfo := do
  let alg ←
    match json.getObjVal? "alg" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "signature.alg must be a string"
  let kid ←
    match json.getObjVal? "kid" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "signature.kid must be a string"
  let issuedAt ←
    match json.getObjVal? "issuedAt" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "signature.issuedAt must be a string"
  let payloadHash ←
    match json.getObjVal? "payloadHash" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "signature.payloadHash must be a string"
  let canonJson ←
    match json.getObjVal? "canonicalization" with
    | Except.ok v => pure v
    | Except.error err => Except.error err
  let canon ← CanonicalizationInfo.fromJson? canonJson
  let jws ←
    match json.getObjVal? "jws" with
    | Except.ok (Json.str s) => pure s
    | _ => Except.error "signature.jws must be a string"
  pure { alg, kid, issuedAt, payloadHash, canonicalization := canon, jws }

end SignatureInfo

/-- Ensure the parent directory for a file path exists. -/
def ensureParentDir (path : FilePath) : IO Unit := do
  match path.parent with
  | some dir => IO.FS.createDirAll dir
  | none => pure ()

/-- Deterministic temporary path anchored next to the final artifact. -/
def tmpPath (path : FilePath) : FilePath :=
  let suffix := (path.fileName.getD "artifact") ++ ".tmp"
  match path.parent with
  | some dir => dir / suffix
  | none => FilePath.mk suffix

/-- Temporary sibling file used for auxiliary operations (e.g., signature verification). -/
def tmpSibling (path : FilePath) (tag : String) : FilePath :=
  let base := path.fileName.getD "artifact"
  let fname := s!"{base}.{tag}.tmp"
  match path.parent with
  | some dir => dir / fname
  | none => FilePath.mk fname

/-- Atomically replace the target file with the provided bytes. -/
def writeFileAtomic (path : FilePath) (bytes : ByteArray) : IO Unit := do
  ensureParentDir path
  let tmp := tmpPath path
  IO.FS.withFile tmp IO.FS.Mode.write fun handle => do
    handle.write bytes
    handle.flush
  IO.FS.rename tmp path

private def tryShaCmd (cmd : String) (args : List String) (path : FilePath) :
    IO (Option String) := do
  let argArray := (args ++ [path.toString]).toArray
  let child ← IO.Process.output {cmd := cmd, args := argArray}
  if child.exitCode != 0 then
    pure none
  else
    let line := child.stdout.trim
    match line.split (fun c => c = ' ' || c = '\t') |>.filter (· ≠ "") with
    | hash :: _ => pure <| some hash
    | _ => pure none

/-- Compute a hexadecimal SHA256 digest for a file using common system utilities. -/
def sha256Hex (path : FilePath) : IO String := do
  let candidates :=
    [("sha256sum", ["-b"]), ("shasum", ["-a", "256"])]
  let rec loop
      | [] => throw <| IO.userError "Unable to locate sha256 utility (tried sha256sum, shasum)."
      | (cmd, args) :: rest => do
          match ← tryShaCmd cmd args path with
          | some hash => pure hash
          | none => loop rest
  loop candidates

/-- Compute the SHA256 of an in-memory payload by parking it next to the final artifact. -/
def sha256HexBytesNear (hint : FilePath) (bytes : ByteArray) : IO String := do
  let tmp := tmpPath hint
  ensureParentDir tmp
  IO.FS.writeBinFile tmp bytes
  try
    sha256Hex tmp
  finally
    try IO.FS.removeFile tmp catch _ => pure ()

/-- ISO-8601 UTC timestamp helper used for signature metadata. -/
def currentIsoTimestamp : IO String := do
  let child ← IO.Process.output
    { cmd := "date", args := #["-u", "+%Y-%m-%dT%H:%M:%SZ"] }
  if child.exitCode != 0 then
    throw <| IO.userError s!"Failed to obtain timestamp: {child.stderr}"
  else
    pure child.stdout.trim

/-- Write bytes atomically and emit a `.sha256` sidecar with the digest tag. -/
def writeFileWithSha (path : FilePath) (bytes : ByteArray) : IO String := do
  writeFileAtomic path bytes
  let digest := ← sha256Hex path
  let tag := s!"sha256:{digest}"
  let sidecar := path.addExtension "sha256"
  writeFileAtomic sidecar (s!"{tag}\n".toUTF8)
  return tag

end IO
end Biosim
