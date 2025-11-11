import Lean.Data.Json
import Biosim.IO.Shared
import Biosim.IO.Checks
import Biosim.IO.Certificate
import Biosim.IO.Base64Url
import Biosim.IO.Jwks

open Lean
open System
open Biosim.IO
open Biosim.IO.Base64Url
open Biosim.ProofCert

namespace Biosim
namespace CLI

def exitInvalidSignature : UInt32 := 2
def exitHashMismatch : UInt32 := 3
def exitCanonicalMismatch : UInt32 := 4
def exitMissingSignature : UInt32 := 5

inductive VerifyKind
  | checks
  | cert
  deriving DecidableEq

structure VerifyConfig where
  kind : VerifyKind
  target : System.FilePath
  jwksPath? : Option System.FilePath := none
  sigMode : SignatureMode := .signedSoft
  printDetails : Bool := false

inductive VerificationError
  | missingSignature
  | hashMismatch
  | canonicalMismatch (msg : String)
  | invalidSignature (msg : String)

def VerificationError.exitCode : VerificationError → UInt32
  | .missingSignature => exitMissingSignature
  | .hashMismatch => exitHashMismatch
  | .canonicalMismatch _ => exitCanonicalMismatch
  | .invalidSignature _ => exitInvalidSignature

private def mapCanon {α} : Except String α → Except VerificationError α
  | Except.ok v => Except.ok v
  | Except.error err => Except.error (.canonicalMismatch err)

private def mapSignature {α} : Except String α → Except VerificationError α
  | Except.ok v => Except.ok v
  | Except.error err => Except.error (.invalidSignature err)

private def utf8ToCanonical (bytes : ByteArray) :
    Except VerificationError String :=
  match String.fromUTF8? bytes with
  | some s => Except.ok s
  | none => Except.error (.canonicalMismatch "Invalid UTF-8 payload")

private def expectStringField (value : Lean.Json) (field : String) :
    Except VerificationError String :=
  match value with
  | Lean.Json.str s => Except.ok s
  | _ => Except.error (.canonicalMismatch s!"Missing or non-string '{field}' field")

def payloadBytesForChecks (bundle : Biosim.IO.Checks.Bundle) : ByteArray :=
  ( { bundle with signature? := none }.render true ).toUTF8

def payloadBytesForCert (cert : ProofCert.Certificate) : ByteArray :=
  ( { cert with signature? := none }.render true ).toUTF8

def payloadHashTag (path : System.FilePath) (bytes : ByteArray) :
    IO String := do
  let hex ← Biosim.IO.sha256HexBytesNear path bytes
  pure s!"sha256:{hex}"

def cleanupFiles (paths : List System.FilePath) : IO Unit := do
  for path in paths do
    try
      IO.FS.removeFile path
    catch _ => pure ()

private def describeToolchain (info : Biosim.IO.ToolchainInfo) : String :=
  match info.tacticLib? with
  | some t => s!"lean={info.lean} mathlib={info.mathlib} tactics={t}"
  | none => s!"lean={info.lean} mathlib={info.mathlib}"

private def printSignatureDetails (sig? : Option SignatureInfo) : IO Unit := do
  match sig? with
  | none =>
      IO.println "  signature: <none>"
  | some sig =>
      IO.println s!"  signature.kid={sig.kid}"
      IO.println s!"  signature.payloadHash={sig.payloadHash}"
      IO.println s!"  canonicalization={sig.canonicalization.scheme}"

private def printChecksDetails (bundle : Biosim.IO.Checks.Bundle) : IO Unit := do
  IO.println s!"  schema: {bundle.schema}"
  IO.println s!"  modelHash: {bundle.modelHash}"
  IO.println s!"  toolchain: {describeToolchain bundle.toolchain}"
  IO.println s!"  checks: {bundle.checks.length}"
  printSignatureDetails bundle.signature?

private def printCertificateDetails (cert : ProofCert.Certificate) : IO Unit := do
  IO.println s!"  schema: {cert.schema}"
  IO.println s!"  modelHash: {cert.modelHash}"
  IO.println s!"  semantics: {String.intercalate ", " cert.semantics}"
  IO.println s!"  toolchain: {describeToolchain cert.toolchain}"
  IO.println s!"  theorems: {cert.theorems.length}"
  printSignatureDetails cert.signature?

def ed25519SpkiPrefix : ByteArray :=
  ByteArray.mk
    #[(0x30 : UInt8), 0x2a, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x03, 0x21, 0x00]

def buildSpki (raw : ByteArray) : ByteArray :=
  ed25519SpkiPrefix ++ raw

def verifyWithOpenssl (target : System.FilePath)
    (message signature pubKey : ByteArray) : IO Bool := do
  let derPath := Biosim.IO.tmpSibling target "jwks.der"
  let pemPath := Biosim.IO.tmpSibling target "jwks.pem"
  let msgPath := Biosim.IO.tmpSibling target "jws.msg"
  let sigPath := Biosim.IO.tmpSibling target "jws.sig"
  try
    IO.FS.writeBinFile derPath (buildSpki pubKey)
    IO.FS.writeBinFile msgPath message
    IO.FS.writeBinFile sigPath signature
    let pemResult ← IO.Process.output
      { cmd := "openssl"
        , args := #["pkey", "-inform", "DER", "-pubin",
            "-in", derPath.toString, "-out", pemPath.toString] }
    if pemResult.exitCode ≠ 0 then
      IO.eprintln pemResult.stderr
      return false
    let verifyResult ← IO.Process.output
      { cmd := "openssl"
        , args := #["pkeyutl", "-verify", "-pubin",
            "-inkey", pemPath.toString,
            "-rawin", "-in", msgPath.toString,
            "-sigfile", sigPath.toString] }
    if verifyResult.exitCode ≠ 0 then
      IO.eprintln verifyResult.stderr
    return verifyResult.exitCode = 0
  finally
    cleanupFiles [derPath, pemPath, msgPath, sigPath]

def verifyJws (sig : SignatureInfo) (payloadBytes : ByteArray)
    (target : System.FilePath) (jwks : Biosim.IO.Jwks.Document) :
    IO (Except VerificationError Unit) := do
  let parse : Except VerificationError
      (String × String × ByteArray × ByteArray) := do
    match sig.jws.splitOn "." with
    | [headerPart, payloadPart, signaturePart] =>
        let headerBytes ← mapCanon (decode headerPart)
        let headerStr ← utf8ToCanonical headerBytes
        let headerJson ← mapCanon (Lean.Json.parse headerStr)
        let headerKidJson ← mapCanon (headerJson.getObjVal? "kid")
        let headerKid ← expectStringField headerKidJson "kid"
        let headerAlgJson ← mapCanon (headerJson.getObjVal? "alg")
        let headerAlg ← expectStringField headerAlgJson "alg"
        let headerCanonJson ← mapCanon (headerJson.getObjVal? "veribiotaCanon")
        let headerCanon ← expectStringField headerCanonJson "veribiotaCanon"
        if headerAlg ≠ "EdDSA" then
          throw (.canonicalMismatch s!"Unsupported JWS alg '{headerAlg}'")
        if headerKid ≠ sig.kid then
          throw (.canonicalMismatch "Header kid mismatch")
        if headerCanon ≠ sig.canonicalization.scheme then
          throw (.canonicalMismatch "Canonicalization scheme mismatch")
        let payloadDecoded ← mapCanon (decode payloadPart)
        if payloadDecoded.data ≠ payloadBytes.data then
          throw (.canonicalMismatch "Payload bytes do not match canonical rendering")
        let signatureBytes ← mapCanon (decode signaturePart)
        let pubKeyBytes ← mapSignature (Biosim.IO.Jwks.findKey? jwks headerKid)
        pure (headerPart, payloadPart, signatureBytes, pubKeyBytes)
    | _ =>
        throw (.canonicalMismatch "JWS must contain three segments")
  match parse with
  | Except.error err => return Except.error err
  | Except.ok (headerPart, payloadPart, signatureBytes, pubKeyBytes) => do
      let signingInput := s!"{headerPart}.{payloadPart}"
      let messageBytes := signingInput.toUTF8
      let ok ← verifyWithOpenssl target messageBytes signatureBytes pubKeyBytes
      if ok then
        return Except.ok ()
      else
        return Except.error (.invalidSignature "OpenSSL signature verification failed")

def verifySignatureBlock (cfg : VerifyConfig) (signature? : Option SignatureInfo)
    (payloadBytes : ByteArray) (target : System.FilePath)
    (jwks? : Option Biosim.IO.Jwks.Document) :
    IO (Except VerificationError Unit) := do
  if !cfg.sigMode.requiresSignature then
    return Except.ok ()
  let some sig := signature?
    | return Except.error .missingSignature
  let some jwks := jwks?
    | return Except.error (.invalidSignature "JWKS document required")
  if sig.alg ≠ "Ed25519" then
    return Except.error (.canonicalMismatch s!"Unsupported signature alg '{sig.alg}'")
  if sig.canonicalization.scheme ≠ "veribiota-canon-v1" ∨
      sig.canonicalization.newlineTerminated = false then
    return Except.error (.canonicalMismatch "Canonicalization metadata mismatch")
  let tag ← payloadHashTag target payloadBytes
  if tag ≠ sig.payloadHash then
    return Except.error VerificationError.hashMismatch
  verifyJws sig payloadBytes target jwks

def handleVerificationError (err : VerificationError) : IO UInt32 := do
  match err with
  | .missingSignature =>
      IO.eprintln "Missing signature but signed mode is enforced."
  | .hashMismatch =>
      IO.eprintln "Payload hash mismatch (sha256 tag differs)."
  | .canonicalMismatch msg =>
      IO.eprintln s!"Canonicalization mismatch: {msg}"
  | .invalidSignature msg =>
      IO.eprintln s!"Invalid signature: {msg}"
  return err.exitCode

def verifyChecks (cfg : VerifyConfig) (jwks? : Option Biosim.IO.Jwks.Document) :
    IO UInt32 := do
  let contents ← IO.FS.readFile cfg.target
  match Biosim.IO.Checks.Bundle.fromString? contents with
  | Except.error err =>
      IO.eprintln s!"Failed to parse checks: {err}"
      return (1 : UInt32)
  | Except.ok bundle =>
      let payloadBytes := payloadBytesForChecks bundle
      match ← verifySignatureBlock cfg bundle.signature? payloadBytes cfg.target jwks? with
      | Except.ok _ =>
          IO.println s!"Checks OK: {cfg.target}"
          if cfg.printDetails then
            printChecksDetails bundle
          return (0 : UInt32)
      | Except.error err =>
          handleVerificationError err

def verifyCert (cfg : VerifyConfig) (jwks? : Option Biosim.IO.Jwks.Document) :
    IO UInt32 := do
  let contents ← IO.FS.readFile cfg.target
  match Lean.Json.parse contents with
  | Except.error err =>
      IO.eprintln s!"Failed to parse certificate JSON: {err}"
      return (1 : UInt32)
  | Except.ok json =>
      match ProofCert.Certificate.fromJson? json with
      | Except.error err =>
          IO.eprintln s!"Invalid certificate: {err}"
          return (1 : UInt32)
      | Except.ok cert =>
          let payloadBytes := payloadBytesForCert cert
          match ← verifySignatureBlock cfg cert.signature? payloadBytes cfg.target jwks? with
          | Except.ok _ =>
              IO.println s!"Certificate OK: {cfg.target}"
              if cfg.printDetails then
                printCertificateDetails cert
              return (0 : UInt32)
          | Except.error err =>
              handleVerificationError err

def runVerify (cfg : VerifyConfig) : IO UInt32 := do
  let jwks? ←
    if cfg.sigMode.requiresSignature then
      match cfg.jwksPath? with
      | some path =>
          try
            let doc ← Biosim.IO.Jwks.load path
            pure (some doc)
          catch err =>
            IO.eprintln s!"Failed to load JWKS: {err}"
            return (1 : UInt32)
      | none =>
          IO.eprintln "--jwks is required for signed modes."
          return (1 : UInt32)
    else
      pure none
  match cfg.kind with
  | .checks => verifyChecks cfg jwks?
  | .cert => verifyCert cfg jwks?

end CLI
end Biosim
