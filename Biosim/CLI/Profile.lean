import Lean.Data.Json
import Biosim.IO.Shared
import Biosim.VeriBiota.Alignment.GlobalAffineV1
import Biosim.VeriBiota.Edit.EditScriptNormalFormV1
import Biosim.VeriBiota.Edit.EditScriptV1
import Biosim.VeriBiota.HMM.PairHMMBridgeV1
import Biosim.VeriBiota.Prime.PrimeEditPlanV1
import Biosim.VeriBiota.VCF.Normalization

open Lean
open Biosim.VeriBiota.Alignment
open Biosim.VeriBiota.Edit
open System

namespace Biosim
namespace CLI
namespace Profile

def profileUsage : String :=
  String.intercalate "\n"
    [ "Usage:"
    , "  veribiota check alignment global_affine_v1 <input.json> [--snapshot-out PATH] [--compact]"
    , "  veribiota check edit edit_script_v1 <input.json> [--snapshot-out PATH] [--compact]"
    , "  veribiota check edit edit_script_normal_form_v1 <input.json> [--snapshot-out PATH] [--compact]"
    , "  veribiota check prime prime_edit_plan_v1 <input.json> [--snapshot-out PATH] [--compact]"
    , "  veribiota check hmm pair_hmm_bridge_v1 <input.json> [--snapshot-out PATH] [--compact]"
    , "  veribiota check vcf vcf_normalization_v1 <input.json> [--snapshot-out PATH] [--compact]"
    ]

private def jsonInt (i : Int) : Json :=
  Json.num (JsonNumber.fromInt i)

private def jsonNat (n : Nat) : Json :=
  Json.num (JsonNumber.fromNat n)

private def jsonFloat (f : Float) : Json :=
  match JsonNumber.fromFloat? f with
  | Sum.inr num => Json.num num
  | _ => Json.num (JsonNumber.fromInt 0)

private def decodeTraceOp (opStr : String) : Except String GlobalAffineV1.TraceOp :=
  match opStr with
  | "M" => Except.ok GlobalAffineV1.TraceOp.M
  | "I" => Except.ok GlobalAffineV1.TraceOp.I
  | "D" => Except.ok GlobalAffineV1.TraceOp.D
  | other => Except.error s!"Unknown trace op '{other}'"

private def engineInfo (ver : String) (buildId : String) : Json :=
  Json.mkObj
    [ ("veribiota_version", Json.str ver)
    , ("lean_version", Json.str Lean.versionString)
    , ("build_id", Json.str buildId)
    ]

partial def readStdinAll (h : IO.FS.Stream) (acc : ByteArray := ByteArray.empty) : IO ByteArray := do
  let chunk ← h.read 4096
  if chunk.isEmpty then
    pure acc
  else
    readStdinAll h (acc ++ chunk)

private def readJsonInputWithRaw (path : FilePath) :
    IO (Except String (Json × ByteArray)) := do
  if path.toString = "-" then
    let stdin ← IO.getStdin
    let bytes ← readStdinAll stdin
    let contents ←
      match String.fromUTF8? bytes with
      | some s => pure s
      | none => pure ""
    match Json.parse contents with
    | Except.ok j => pure <| Except.ok (j, bytes)
    | Except.error err => pure <| Except.error err
  else
    let contents ← IO.FS.readFile path
    let bytes := contents.toUTF8
    pure <| (Json.parse contents).map (fun j => (j, bytes))

private def requireField {α} : Except String α → String → Except String α
  | Except.ok v, _ => Except.ok v
  | Except.error _, label => Except.error s!"missing or invalid field '{label}'"

structure ManifestEntry where
  schemaPath : String
  schemaHash : String
  theorems : List String

private def loadManifestEntry (profileId : String) : IO ManifestEntry := do
  let manifestPath := FilePath.mk "profiles/manifest.json"
  let contents ← IO.FS.readFile manifestPath
  let manifest ←
    match Json.parse contents with
    | Except.ok j => pure j
    | Except.error msg =>
        throw <| IO.userError s!"Failed to parse manifest: {msg}"
  let entry ←
    match manifest.getObjVal? profileId with
    | Except.ok v => pure v
    | Except.error err =>
        throw <| IO.userError s!"Manifest missing {profileId}: {err}"
  let schemaPath ←
    match entry.getObjValAs? String "schema_path" with
    | Except.ok v => pure v
    | Except.error err =>
        throw <| IO.userError s!"Manifest missing schema_path for {profileId}: {err}"
  let schemaHash ←
    match entry.getObjValAs? String "schema" with
    | Except.ok v => pure v
    | Except.error err =>
        throw <| IO.userError s!"Manifest missing schema hash for {profileId}: {err}"
  let theorems ←
    match entry.getObjVal? "theorems" with
    | Except.ok (Json.arr arr) =>
        let names := arr.toList.mapMaybe fun j =>
          match j with
          | Json.str s => some s
          | _ => none
        if names = [] then
          throw <| IO.userError s!"Manifest theorems for {profileId} are empty or malformed"
        else
          pure names
    | Except.ok _ =>
        throw <| IO.userError s!"Manifest theorems for {profileId} must be an array"
    | Except.error err =>
        throw <| IO.userError s!"Manifest missing theorems for {profileId}: {err}"
  pure { schemaPath, schemaHash, theorems }

private def emitSnapshotSignature (outPath : FilePath) (profileId profileVersion status : String)
    (instanceSummary : Json) (rawInput : ByteArray) (inputHint : FilePath)
    (ver buildId : String) : IO Unit := do
  let manifest ← loadManifestEntry profileId
  let timestamp ← Biosim.IO.currentIsoTimestamp
  let digestHex ← Biosim.IO.sha256HexBytesNear inputHint rawInput
  let payload :=
    Json.mkObj
      [ ("snapshot_profile", Json.str profileId)
      , ("snapshot_profile_version", Json.str profileVersion)
      , ("snapshot_hash", Json.str s!"sha256:{digestHex}")
      , ("schema_hash", Json.str manifest.schemaHash)
      , ("schema_id", Json.str manifest.schemaPath)
      , ("theorem_ids", Json.arr <| manifest.theorems.map Json.str |>.toArray)
      , ("veribiota_build_id", Json.str buildId)
      , ("veribiota_version", Json.str ver)
      , ("lean_version", Json.str Lean.versionString)
      , ("timestamp_utc", Json.str timestamp)
      , ("verification_result", Json.str status)
      , ("instance_summary", instanceSummary)
      ]
  let bytes := (payload.pretty 2).toUTF8
  Biosim.IO.writeFileAtomic outPath bytes

def decodeAlignmentInstance (j : Json) : Except String GlobalAffineV1.Instance := do
  let seqA ← requireField (j.getObjValAs? String "seqA") "seqA"
  let seqB ← requireField (j.getObjValAs? String "seqB") "seqB"
  let scoringJson ← requireField (j.getObjVal? "scoring") "scoring"
  let matchScore ← requireField (scoringJson.getObjValAs? Int "match") "scoring.match"
  let mismatch ← requireField (scoringJson.getObjValAs? Int "mismatch") "scoring.mismatch"
  let gapOpen ← requireField (scoringJson.getObjValAs? Int "gap_open") "scoring.gap_open"
  let gapExtend ← requireField (scoringJson.getObjValAs? Int "gap_extend") "scoring.gap_extend"
  let scoring : GlobalAffineV1.Scoring := { matchScore, mismatch, gapOpen, gapExtend }

  let witnessJson ← requireField (j.getObjVal? "witness") "witness"
  let score ← requireField (witnessJson.getObjValAs? Int "score") "witness.score"
  let traceJson ← requireField (witnessJson.getObjVal? "trace") "witness.trace"
  let traceArr ← requireField (traceJson.getArr?) "witness.trace"
  let trace ← traceArr.foldlM (m := Except String) (init := ([] : List GlobalAffineV1.TraceOp)) fun acc t => do
    let opStr ← t.getObjValAs? String "op"
    let op ← decodeTraceOp opStr
    pure (acc.concat op)

  pure
    { seqA
      , seqB
      , scoring
      , witness := { score, trace } }

private def renderAlignmentPayload (inst : GlobalAffineV1.Instance) (specScore : Int)
    (traceResult : Except String Int) (status : String)
    (alignmentOk : Bool) (ver : String) (buildId : String)
    (err? : Option String := none) : (Json × Json) :=
  let traceScoreField : List (String × Json) :=
    match traceResult with
    | Except.ok traceScore => [("trace_score", jsonInt traceScore)]
    | Except.error _ => []
  let detailFields : List (String × Json) :=
    [ ("seqA_length", jsonNat inst.seqA.length)
    , ("seqB_length", jsonNat inst.seqB.length)
    , ("dp_score", jsonInt specScore)
    , ("witness_score", jsonInt inst.witness.score)
    , ("trace_length", jsonNat inst.witness.trace.length)
    , ("alignment_matches_spec", Json.bool alignmentOk)
    ] ++ traceScoreField ++
    match err? with
    | some msg => [("error", Json.str msg)]
    | none => []
  let instanceObj := Json.mkObj detailFields
  let payload := Json.mkObj
    [ ("profile", Json.str GlobalAffineV1.profileId)
    , ("profile_version", Json.str "1.0.0")
    , ("status", Json.str status)
    , ("theorems", Json.arr <| GlobalAffineV1.coreTheorems.map Json.str |>.toArray)
    , ("instance", instanceObj)
    , ("engine", engineInfo ver buildId)
    , ("signature", Json.null) -- placeholder until signing is wired up
    ]
  (payload, instanceObj)

/-- Run the `global_affine_v1` profile against a JSON input file. -/
def runGlobalAffineProfile (inputPath : FilePath) (pretty : Bool := true)
    (ver : String := "dev") (buildId : String := "dev")
    (snapshotOut? : Option FilePath := none) : IO UInt32 := do
  let jsonRaw? ← readJsonInputWithRaw inputPath
  let (json, rawBytes) ←
    match jsonRaw? with
    | Except.ok pair => pure pair
    | Except.error msg =>
        let payload := Json.mkObj
          [ ("profile", Json.str GlobalAffineV1.profileId)
          , ("profile_version", Json.str "1.0.0")
          , ("status", Json.str "error")
          , ("theorems", Json.arr <| GlobalAffineV1.coreTheorems.map Json.str |>.toArray)
          , ("instance", Json.mkObj [("error", Json.str msg)])
          , ("engine", engineInfo ver buildId)
          , ("signature", Json.null)
          ]
        IO.println (if pretty then payload.pretty else payload.compress)
        return 1
  let inst? := decodeAlignmentInstance json
  let inst ←
    match inst? with
    | Except.ok inst => pure inst
    | Except.error msg =>
        let payload := Json.mkObj
          [ ("profile", Json.str GlobalAffineV1.profileId)
          , ("profile_version", Json.str "1.0.0")
          , ("status", Json.str "error")
          , ("theorems", Json.arr <| GlobalAffineV1.coreTheorems.map Json.str |>.toArray)
          , ("instance", Json.mkObj [("error", Json.str msg)])
          , ("engine", engineInfo ver buildId)
          , ("signature", Json.null)
          ]
        IO.println (if pretty then payload.pretty else payload.compress)
        return 1
  let specScore := GlobalAffineV1.specGlobalAffine inst.seqA inst.seqB inst.scoring
  let traceResult := GlobalAffineV1.scoreTrace inst.seqA inst.seqB inst.scoring inst.witness.trace
  match traceResult with
  | Except.error err =>
      let (payload, _) := renderAlignmentPayload inst specScore traceResult "error" false ver buildId (some err)
      IO.println (if pretty then payload.pretty else payload.compress)
      pure 1
  | Except.ok traceScore =>
      let alignmentOk := traceScore = inst.witness.score ∧ specScore = inst.witness.score
      let status := if alignmentOk then "passed" else "failed"
      let exitCode : UInt32 := if alignmentOk then 0 else 2
      let (payload, instanceObj) :=
        renderAlignmentPayload inst specScore traceResult status alignmentOk ver buildId none
      IO.println (if pretty then payload.pretty else payload.compress)
      match snapshotOut? with
      | none => pure exitCode
      | some out =>
          if status = "passed" ∨ status = "failed" then
            try
              emitSnapshotSignature out GlobalAffineV1.profileId "1.0.0" status instanceObj rawBytes inputPath ver buildId
              pure exitCode
            catch err =>
              IO.eprintln s!"Snapshot signature failed: {err}"
              pure 1
          else
            pure exitCode

private def decodeEditType (s : String) : Except String EditScriptV1.EditType :=
  match s with
  | "ins" => Except.ok EditScriptV1.EditType.ins
  | "del" => Except.ok EditScriptV1.EditType.del
  | "sub" => Except.ok EditScriptV1.EditType.sub
  | other => Except.error s!"Unknown edit type '{other}'"

private def decodeEditEntry (e : Json) (label : String := "edits") :
    Except String EditScriptV1.Edit := do
  let tyStr ← requireField (e.getObjValAs? String "type") s!"{label}[].type"
  let ty ← decodeEditType tyStr
  let pos ← requireField (e.getObjValAs? Nat "pos") s!"{label}[].pos"
  let len :=
    match e.getObjValAs? Nat "len" with
    | Except.ok v => v
    | Except.error _ => 0
  let payload :=
    match e.getObjValAs? String "payload" with
    | Except.ok p => p
    | Except.error _ => ""
  pure { type := ty, pos, len, payload }

private def decodeEditsArray (editsJson : Json) (label : String := "edits") :
    Except String (List EditScriptV1.Edit) := do
  let editsArr ← requireField (editsJson.getArr?) label
  editsArr.foldlM (m := Except String) (init := ([] : List EditScriptV1.Edit)) fun acc e => do
    let edit ← decodeEditEntry e label
    pure (acc.concat edit)

def decodeEditScriptInstance (j : Json) : Except String EditScriptV1.Instance := do
  let seqA ← requireField (j.getObjValAs? String "seqA") "seqA"
  let seqB ← requireField (j.getObjValAs? String "seqB") "seqB"
  let editsJson ← requireField (j.getObjVal? "edits") "edits"
  let edits ← decodeEditsArray editsJson "edits"
  pure { seqA, seqB, edits }

def decodeEditScriptNormalFormInstance (j : Json) :
    Except String EditScriptNormalFormV1.Instance := do
  let seqA ← requireField (j.getObjValAs? String "seqA") "seqA"
  let seqB ← requireField (j.getObjValAs? String "seqB") "seqB"
  let editsJson ← requireField (j.getObjVal? "edits") "edits"
  let edits ← decodeEditsArray editsJson "edits"
  let normalizedEdits? ←
    match j.getObjVal? "normalized_edits" with
    | Except.ok normJson =>
        match decodeEditsArray normJson "normalized_edits" with
    | Except.ok v => pure (some v)
    | Except.error err => Except.error err
    | Except.error _ => pure none
  pure { seqA, seqB, edits, normalizedEdits? }

def decodePrimeEditPlanInstance (j : Json) :
    Except String PrimeEditPlanV1.Instance := do
  let refSeq ← requireField (j.getObjValAs? String "ref_seq") "ref_seq"
  let targetSeq ← requireField (j.getObjValAs? String "target_seq") "target_seq"
  let pegJson ← requireField (j.getObjVal? "pegRNA") "pegRNA"
  let spacer ← requireField (pegJson.getObjValAs? String "spacer") "pegRNA.spacer"
  let pam ← requireField (pegJson.getObjValAs? String "pam") "pegRNA.pam"
  let rtTemplate ← requireField (pegJson.getObjValAs? String "rt_template") "pegRNA.rt_template"
  let pbs ← requireField (pegJson.getObjValAs? String "pbs") "pegRNA.pbs"
  let pegRNA : PrimeEditPlanV1.PegRNA := { spacer, pam, rtTemplate, pbs }
  let nick? ←
    match j.getObjVal? "nick" with
    | Except.ok nickJson =>
        let nSpacer ← requireField (nickJson.getObjValAs? String "spacer") "nick.spacer"
        let nPam ← requireField (nickJson.getObjValAs? String "pam") "nick.pam"
        let position :=
          match nickJson.getObjValAs? Nat "position" with
          | Except.ok v => v
          | Except.error _ => 0
        pure (some ({ spacer := nSpacer, pam := nPam, position } : PrimeEditPlanV1.Nick))
    | Except.error _ => pure none
  let editsJson ← requireField (j.getObjVal? "net_edit_script") "net_edit_script"
  let netEditScript ← decodeEditsArray editsJson "net_edit_script"
  pure { refSeq, targetSeq, pegRNA, nick?, netEditScript }

def decodeDPScoring (j : Json) : Except String GlobalAffineV1.Scoring := do
  let matchScore ← requireField (j.getObjValAs? Int "match") "dp_scoring.match"
  let mismatch ← requireField (j.getObjValAs? Int "mismatch") "dp_scoring.mismatch"
  let gapOpen ← requireField (j.getObjValAs? Int "gap_open") "dp_scoring.gap_open"
  let gapExtend ← requireField (j.getObjValAs? Int "gap_extend") "dp_scoring.gap_extend"
  pure { matchScore, mismatch, gapOpen, gapExtend }

def decodeHMMParams (j : Json) : Except String PairHMMBridgeV1.HMMParams := do
  let transJson ← requireField (j.getObjVal? "transition") "hmm_params.transition"
  let emJson ← requireField (j.getObjVal? "emission") "hmm_params.emission"
  let fieldFloat (obj : Json) (name lbl : String) :=
    requireField (obj.getObjValAs? Float name) lbl
  let transition : PairHMMBridgeV1.Transition :=
    { matchToMatch := ← fieldFloat transJson "match_to_match" "transition.match_to_match"
      , matchToIns := ← fieldFloat transJson "match_to_ins" "transition.match_to_ins"
      , matchToDel := ← fieldFloat transJson "match_to_del" "transition.match_to_del"
      , insToMatch := ← fieldFloat transJson "ins_to_match" "transition.ins_to_match"
      , insToIns := ← fieldFloat transJson "ins_to_ins" "transition.ins_to_ins"
      , delToMatch := ← fieldFloat transJson "del_to_match" "transition.del_to_match"
      , delToDel := ← fieldFloat transJson "del_to_del" "transition.del_to_del" }
  let emission : PairHMMBridgeV1.Emission :=
    { match := ← fieldFloat emJson "match" "emission.match"
      , mismatch := ← fieldFloat emJson "mismatch" "emission.mismatch"
      , gap := ← fieldFloat emJson "gap" "emission.gap" }
  pure { transition, emission }

def decodePairHMMBridgeInstance (j : Json) :
    Except String PairHMMBridgeV1.Instance := do
  let seqA ← requireField (j.getObjValAs? String "seqA") "seqA"
  let seqB ← requireField (j.getObjValAs? String "seqB") "seqB"
  let dpJson ← requireField (j.getObjVal? "dp_scoring") "dp_scoring"
  let dpScoring ← decodeDPScoring dpJson
  let hmmJson ← requireField (j.getObjVal? "hmm_params") "hmm_params"
  let hmmParams ← decodeHMMParams hmmJson
  let dpScore ← requireField (j.getObjValAs? Float "dp_score") "dp_score"
  let hmmScore ← requireField (j.getObjValAs? Float "hmm_score") "hmm_score"
  pure { seqA, seqB, dpScoring, hmmParams, dpScore, hmmScore }

def decodeAltArray (j : Json) (label : String) : Except String String := do
  let arr ← requireField (j.getArr?) label
  match arr.toList with
  | [] => Except.error s!"{label} must have at least one alt"
  | h :: _ =>
      match h with
      | Json.str s => Except.ok s
      | _ => Except.error s!"{label} alt entries must be strings"

def decodeVcfVariant (locus : Json) (block : Json) (label : String) :
    Except String VCF.Normalization.Variant := do
  let chrom ← requireField (locus.getObjValAs? String "chrom") s!"{label}.locus.chrom"
  let pos ← requireField (locus.getObjValAs? Nat "pos") s!"{label}.locus.pos"
  let ref ← requireField (block.getObjValAs? String "ref") s!"{label}.ref"
  let alt ← decodeAltArray block s!"{label}.alt"
  pure { chrom, pos, ref, alt }

def decodeVcfNormalizationInstance (j : Json) :
    Except String VCF.Normalization.Instance := do
  let inputVcfHash ← requireField (j.getObjValAs? String "input_vcf_hash") "input_vcf_hash"
  let normalizedVcfHash ← requireField (j.getObjValAs? String "normalized_vcf_hash") "normalized_vcf_hash"
  let referenceFastaHash? :=
    match j.getObjValAs? String "reference_fasta_hash" with
    | Except.ok v => some v
    | Except.error _ => none
  let variantsJson ← requireField (j.getObjVal? "variants") "variants"
  let variantsArr ← requireField (variantsJson.getArr?) "variants"
  let variants ← variantsArr.foldlM (m := Except String)
      (init := ([] : List VCF.Normalization.VariantRecord)) fun acc vj => do
    let locusJson ← requireField (vj.getObjVal? "locus") "variants[].locus"
    let origJson ← requireField (vj.getObjVal? "original") "variants[].original"
    let normJson ← requireField (vj.getObjVal? "normalized") "variants[].normalized"
    let orig ← decodeVcfVariant locusJson origJson "variants[].original"
    let normPos ← requireField (normJson.getObjValAs? Nat "pos") "variants[].normalized.pos"
    let norm ← decodeVcfVariant
      (Json.mkObj [("chrom", Json.str orig.chrom), ("pos", jsonNat normPos)])
      normJson "variants[].normalized"
    let ops :=
      match vj.getObjVal? "operations" with
      | Except.ok (Json.arr ops) =>
          ops.toList.foldl (fun acc op =>
            match op with
            | Json.str s => acc ++ [s]
            | _ => acc) []
      | _ => []
    pure (acc.concat { original := orig, normalized := norm, operations := ops })
  pure { inputVcfHash, normalizedVcfHash, referenceFastaHash?, variants }

private def renderEditScriptPayload (inst : EditScriptV1.Instance) (status : String)
    (holds : Bool) (ver : String) (buildId : String)
    (err? : Option String := none) : (Json × Json) :=
  let detailFields : List (String × Json) :=
    [ ("seqA_length", jsonNat inst.seqA.length)
    , ("seqB_length", jsonNat inst.seqB.length)
    , ("edit_count", jsonNat inst.edits.length)
    , ("applied_ok", Json.bool holds)
    ] ++
    match err? with
    | some msg => [("error", Json.str msg)]
    | none => []
  let instanceObj := Json.mkObj detailFields
  let payload := Json.mkObj
    [ ("profile", Json.str EditScriptV1.profileId)
    , ("profile_version", Json.str EditScriptV1.profileVersion)
    , ("status", Json.str status)
    , ("theorems", Json.arr <| EditScriptV1.coreTheorems.map Json.str |>.toArray)
    , ("instance", instanceObj)
    , ("engine", engineInfo ver buildId)
    , ("signature", Json.null)
    ]
  (payload, instanceObj)

private def renderEditScriptNormalFormPayload (inst : EditScriptNormalFormV1.Instance)
    (status : String) (holds : Bool) (normalFormOk : Bool)
    (ver : String) (buildId : String)
    (normalizedAppliedOk? : Option Bool := none)
    (err? : Option String := none) : (Json × Json) :=
  let normalizedFields : List (String × Json) :=
    match inst.normalizedEdits?, normalizedAppliedOk? with
    | some edits, some ok =>
        [ ("normalized_edit_count", jsonNat edits.length)
        , ("normalized_applied_ok", Json.bool ok) ]
    | _, _ => []
  let detailFields : List (String × Json) :=
    [ ("seqA_length", jsonNat inst.seqA.length)
    , ("seqB_length", jsonNat inst.seqB.length)
    , ("edit_count", jsonNat inst.edits.length)
    , ("applied_ok", Json.bool holds)
    , ("normal_form", Json.bool normalFormOk)
    ] ++ normalizedFields ++
    match err? with
    | some msg => [("error", Json.str msg)]
    | none => []
  let instanceObj := Json.mkObj detailFields
  let payload := Json.mkObj
    [ ("profile", Json.str EditScriptNormalFormV1.profileId)
    , ("profile_version", Json.str EditScriptNormalFormV1.profileVersion)
    , ("status", Json.str status)
    , ("theorems", Json.arr <| EditScriptNormalFormV1.coreTheorems.map Json.str |>.toArray)
    , ("instance", instanceObj)
    , ("engine", engineInfo ver buildId)
    , ("signature", Json.null)
    ]
  (payload, instanceObj)

private def renderPrimeEditPlanPayload (inst : PrimeEditPlanV1.Instance) (status : String)
    (appliedOk pamOk boundsOk : Bool) (ver : String) (buildId : String)
    (err? : Option String := none) : (Json × Json) :=
  let nickFields : List (String × Json) :=
    match inst.nick? with
    | some nick =>
        [ ("nick_present", Json.bool true)
        , ("nick_position", jsonNat nick.position) ]
    | none => [("nick_present", Json.bool false)]
  let detailFields : List (String × Json) :=
    [ ("ref_seq_length", jsonNat inst.refSeq.length)
    , ("target_seq_length", jsonNat inst.targetSeq.length)
    , ("edit_count", jsonNat inst.netEditScript.length)
    , ("pegRNA_pbs_length", jsonNat inst.pegRNA.pbs.length)
    , ("pegRNA_rt_length", jsonNat inst.pegRNA.rtTemplate.length)
    , ("net_edit_applied", Json.bool appliedOk)
    , ("pam_aligned", Json.bool pamOk)
    , ("lengths_within_bounds", Json.bool boundsOk)
    ] ++ nickFields ++
    match err? with
    | some msg => [("error", Json.str msg)]
    | none => []
  let instanceObj := Json.mkObj detailFields
  let payload := Json.mkObj
    [ ("profile", Json.str PrimeEditPlanV1.profileId)
    , ("profile_version", Json.str PrimeEditPlanV1.profileVersion)
    , ("status", Json.str status)
    , ("theorems", Json.arr <| PrimeEditPlanV1.coreTheorems.map Json.str |>.toArray)
    , ("instance", instanceObj)
    , ("engine", engineInfo ver buildId)
    , ("signature", Json.null)
    ]
  (payload, instanceObj)

private def renderPairHMMBridgePayload (inst : PairHMMBridgeV1.Instance) (status : String)
    (specScore : Int) (bridgeOk : Bool) (dpSpecOk : Bool)
    (ver : String) (buildId : String) (err? : Option String := none) : (Json × Json) :=
  let detailFields : List (String × Json) :=
    [ ("seqA_length", jsonNat inst.seqA.length)
    , ("seqB_length", jsonNat inst.seqB.length)
    , ("dp_score_witness", jsonFloat inst.dpScore)
    , ("dp_score_spec", jsonInt specScore)
    , ("hmm_score_witness", jsonFloat inst.hmmScore)
    , ("dp_matches_spec", Json.bool dpSpecOk)
    , ("dp_hmm_bridge_ok", Json.bool bridgeOk)
    ] ++
    match err? with
    | some msg => [("error", Json.str msg)]
    | none => []
  let instanceObj := Json.mkObj detailFields
  let payload := Json.mkObj
    [ ("profile", Json.str PairHMMBridgeV1.profileId)
    , ("profile_version", Json.str PairHMMBridgeV1.profileVersion)
    , ("status", Json.str status)
    , ("theorems", Json.arr <| PairHMMBridgeV1.coreTheorems.map Json.str |>.toArray)
    , ("instance", instanceObj)
    , ("engine", engineInfo ver buildId)
    , ("signature", Json.null)
    ]
  (payload, instanceObj)

private def renderVcfNormalizationPayload (inst : VCF.Normalization.Instance) (status : String)
    (results : List Bool) (ver : String) (buildId : String)
    (err? : Option String := none) : (Json × Json) :=
  let total := inst.variants.length
  let okCount := results.count (· = true)
  let detailFields : List (String × Json) :=
    [ ("variant_count", jsonNat total)
    , ("normalized_ok_count", jsonNat okCount)
    , ("all_variants_normalized", Json.bool (okCount = total))
    , ("input_vcf_hash", Json.str inst.inputVcfHash)
    , ("normalized_vcf_hash", Json.str inst.normalizedVcfHash)
    ] ++
    (match inst.referenceFastaHash? with
     | some h => [("reference_fasta_hash", Json.str h)]
     | none => []) ++
    (match err? with
     | some msg => [("error", Json.str msg)]
     | none => [])
  let instanceObj := Json.mkObj detailFields
  let payload := Json.mkObj
    [ ("profile", Json.str VCF.Normalization.profileId)
    , ("profile_version", Json.str VCF.Normalization.profileVersion)
    , ("status", Json.str status)
    , ("theorems", Json.arr <| VCF.Normalization.coreTheorems.map Json.str |>.toArray)
    , ("instance", instanceObj)
    , ("engine", engineInfo ver buildId)
    , ("signature", Json.null)
    ]
  (payload, instanceObj)

/-- Run the `edit_script_v1` profile against a JSON input file. -/
def runEditScriptProfile (inputPath : FilePath) (pretty : Bool := true)
    (ver : String := "dev") (buildId : String := "dev")
    (snapshotOut? : Option FilePath := none) : IO UInt32 := do
  let jsonRaw? ← readJsonInputWithRaw inputPath
  let (json, rawBytes) ←
    match jsonRaw? with
    | Except.ok pair => pure pair
    | Except.error msg =>
        let payload := Json.mkObj
          [ ("profile", Json.str EditScriptV1.profileId)
          , ("profile_version", Json.str EditScriptV1.profileVersion)
          , ("status", Json.str "error")
          , ("theorems", Json.arr <| EditScriptV1.coreTheorems.map Json.str |>.toArray)
          , ("instance", Json.mkObj [("error", Json.str msg)])
          , ("engine", engineInfo ver buildId)
          , ("signature", Json.null)
          ]
        IO.println (if pretty then payload.pretty else payload.compress)
        return 1
  let inst? := decodeEditScriptInstance json
  let inst ←
    match inst? with
    | Except.ok inst => pure inst
    | Except.error msg =>
        let payload := Json.mkObj
          [ ("profile", Json.str EditScriptV1.profileId)
          , ("profile_version", Json.str EditScriptV1.profileVersion)
          , ("status", Json.str "error")
          , ("theorems", Json.arr <| EditScriptV1.coreTheorems.map Json.str |>.toArray)
          , ("instance", Json.mkObj [("error", Json.str msg)])
          , ("engine", engineInfo ver buildId)
          , ("signature", Json.null)
          ]
        IO.println (if pretty then payload.pretty else payload.compress)
        return 1
  let applied := EditScriptV1.applyEdits inst.seqA inst.edits
  match applied with
  | none =>
      let (payload, _) := renderEditScriptPayload inst "error" false ver buildId (some "invalid edit script")
      IO.println (if pretty then payload.pretty else payload.compress)
      pure 1
  | some result =>
      let ok := result = inst.seqB
      let status := if ok then "passed" else "failed"
      let exitCode : UInt32 := if ok then 0 else 2
      let (payload, instanceObj) := renderEditScriptPayload inst status ok ver buildId none
      IO.println (if pretty then payload.pretty else payload.compress)
      match snapshotOut? with
      | none => pure exitCode
      | some out =>
          if status = "passed" ∨ status = "failed" then
            try
              emitSnapshotSignature out EditScriptV1.profileId EditScriptV1.profileVersion status instanceObj rawBytes inputPath ver buildId
              pure exitCode
            catch err =>
              IO.eprintln s!"Snapshot signature failed: {err}"
              pure 1
          else
            pure exitCode

/-- Run the `edit_script_normal_form_v1` profile against a JSON input file. -/
def runEditScriptNormalFormProfile (inputPath : FilePath) (pretty : Bool := true)
    (ver : String := "dev") (buildId : String := "dev")
    (snapshotOut? : Option FilePath := none) : IO UInt32 := do
  let jsonRaw? ← readJsonInputWithRaw inputPath
  let (json, rawBytes) ←
    match jsonRaw? with
    | Except.ok pair => pure pair
    | Except.error msg =>
        let payload := Json.mkObj
          [ ("profile", Json.str EditScriptNormalFormV1.profileId)
          , ("profile_version", Json.str EditScriptNormalFormV1.profileVersion)
          , ("status", Json.str "error")
          , ("theorems", Json.arr <| EditScriptNormalFormV1.coreTheorems.map Json.str |>.toArray)
          , ("instance", Json.mkObj [("error", Json.str msg)])
          , ("engine", engineInfo ver buildId)
          , ("signature", Json.null)
          ]
        IO.println (if pretty then payload.pretty else payload.compress)
        return 1
  let inst? := decodeEditScriptNormalFormInstance json
  let inst ←
    match inst? with
    | Except.ok inst => pure inst
    | Except.error msg =>
        let payload := Json.mkObj
          [ ("profile", Json.str EditScriptNormalFormV1.profileId)
          , ("profile_version", Json.str EditScriptNormalFormV1.profileVersion)
          , ("status", Json.str "error")
          , ("theorems", Json.arr <| EditScriptNormalFormV1.coreTheorems.map Json.str |>.toArray)
          , ("instance", Json.mkObj [("error", Json.str msg)])
          , ("engine", engineInfo ver buildId)
          , ("signature", Json.null)
          ]
        IO.println (if pretty then payload.pretty else payload.compress)
        return 1
  let applied := EditScriptV1.applyEdits inst.seqA inst.edits
  let normalizedApplied? :=
    match inst.normalizedEdits? with
    | none => none
    | some edits => some (EditScriptV1.applyEdits inst.seqA edits)
  match applied with
  | none =>
      let (payload, _) := renderEditScriptNormalFormPayload inst "error" false false ver buildId none
        (some "invalid edit script")
      IO.println (if pretty then payload.pretty else payload.compress)
      pure 1
  | some appliedSeq =>
      match normalizedApplied? with
      | some none =>
          let (payload, _) := renderEditScriptNormalFormPayload inst "error" false false ver buildId none
            (some "invalid normalized edit script")
          IO.println (if pretty then payload.pretty else payload.compress)
          pure 1
      | some (some normSeq) =>
          let appliedOk := appliedSeq = inst.seqB
          let normalizedOk := normSeq = inst.seqB
          let normalFormOk := EditScriptNormalFormV1.isNormalForm inst.seqA inst.edits
          match EditScriptNormalFormV1.checkInstance inst with
          | isTrue _ =>
              let (payload, instanceObj) :=
                renderEditScriptNormalFormPayload inst "passed" true normalFormOk ver buildId
                  (some normalizedOk) none
              IO.println (if pretty then payload.pretty else payload.compress)
              match snapshotOut? with
              | none => pure 0
              | some out =>
                  try
                    emitSnapshotSignature out EditScriptNormalFormV1.profileId EditScriptNormalFormV1.profileVersion
                      "passed" instanceObj rawBytes inputPath ver buildId
                    pure 0
                  catch err =>
                    IO.eprintln s!"Snapshot signature failed: {err}"
                    pure 1
          | isFalse _ =>
              let (payload, instanceObj) :=
                renderEditScriptNormalFormPayload inst "failed" appliedOk normalFormOk ver buildId
                  (some normalizedOk) none
              IO.println (if pretty then payload.pretty else payload.compress)
              match snapshotOut? with
              | none => pure 2
              | some out =>
                  try
                    emitSnapshotSignature out EditScriptNormalFormV1.profileId EditScriptNormalFormV1.profileVersion
                      "failed" instanceObj rawBytes inputPath ver buildId
                    pure 2
                  catch err =>
                    IO.eprintln s!"Snapshot signature failed: {err}"
                    pure 1
      | none =>
          let appliedOk := appliedSeq = inst.seqB
          let normalFormOk := EditScriptNormalFormV1.isNormalForm inst.seqA inst.edits
          match EditScriptNormalFormV1.checkInstance inst with
          | isTrue _ =>
              let (payload, instanceObj) :=
                renderEditScriptNormalFormPayload inst "passed" appliedOk normalFormOk ver buildId none none
              IO.println (if pretty then payload.pretty else payload.compress)
              match snapshotOut? with
              | none => pure 0
              | some out =>
                  try
                    emitSnapshotSignature out EditScriptNormalFormV1.profileId EditScriptNormalFormV1.profileVersion
                      "passed" instanceObj rawBytes inputPath ver buildId
                    pure 0
                  catch err =>
                    IO.eprintln s!"Snapshot signature failed: {err}"
                    pure 1
          | isFalse _ =>
              let (payload, instanceObj) :=
                renderEditScriptNormalFormPayload inst "failed" appliedOk normalFormOk ver buildId none none
              IO.println (if pretty then payload.pretty else payload.compress)
              match snapshotOut? with
              | none => pure 2
              | some out =>
                  try
                    emitSnapshotSignature out EditScriptNormalFormV1.profileId EditScriptNormalFormV1.profileVersion
                      "failed" instanceObj rawBytes inputPath ver buildId
                    pure 2
                  catch err =>
                    IO.eprintln s!"Snapshot signature failed: {err}"
                    pure 1

/-- Run the `prime_edit_plan_v1` profile. -/
def runPrimeEditPlanProfile (inputPath : FilePath) (pretty : Bool := true)
    (ver : String := "dev") (buildId : String := "dev")
    (snapshotOut? : Option FilePath := none) : IO UInt32 := do
  let jsonRaw? ← readJsonInputWithRaw inputPath
  let (json, rawBytes) ←
    match jsonRaw? with
    | Except.ok pair => pure pair
    | Except.error msg =>
        let payload := Json.mkObj
          [ ("profile", Json.str PrimeEditPlanV1.profileId)
          , ("profile_version", Json.str PrimeEditPlanV1.profileVersion)
          , ("status", Json.str "error")
          , ("theorems", Json.arr <| PrimeEditPlanV1.coreTheorems.map Json.str |>.toArray)
          , ("instance", Json.mkObj [("error", Json.str msg)])
          , ("engine", engineInfo ver buildId)
          , ("signature", Json.null)
          ]
        IO.println (if pretty then payload.pretty else payload.compress)
        return 1
  let inst? := decodePrimeEditPlanInstance json
  let inst ←
    match inst? with
    | Except.ok inst => pure inst
    | Except.error msg =>
        let payload := Json.mkObj
          [ ("profile", Json.str PrimeEditPlanV1.profileId)
          , ("profile_version", Json.str PrimeEditPlanV1.profileVersion)
          , ("status", Json.str "error")
          , ("theorems", Json.arr <| PrimeEditPlanV1.coreTheorems.map Json.str |>.toArray)
          , ("instance", Json.mkObj [("error", Json.str msg)])
          , ("engine", engineInfo ver buildId)
          , ("signature", Json.null)
          ]
        IO.println (if pretty then payload.pretty else payload.compress)
        return 1
  let applied? := EditScriptV1.applyEdits inst.refSeq inst.netEditScript
  match applied? with
  | none =>
      let (payload, _) :=
        renderPrimeEditPlanPayload inst "error" false false false ver buildId (some "invalid net_edit_script")
      IO.println (if pretty then payload.pretty else payload.compress)
      pure 1
  | some appliedSeq =>
      let appliedOk := appliedSeq = inst.targetSeq
      let boundsOk :=
        let pbsLen := inst.pegRNA.pbs.length
        let rtLen := inst.pegRNA.rtTemplate.length
        pbsLen ≥ 8 ∧ pbsLen ≤ 20 ∧ rtLen ≥ 10 ∧ rtLen ≤ 80
      let pamOk := inst.refSeq.startsWith (inst.pegRNA.spacer ++ inst.pegRNA.pam)
      let specOk :=
        match PrimeEditPlanV1.checkInstance inst with
        | isTrue _ => true
        | isFalse _ => false
      let status := if specOk then "passed" else "failed"
      let exitCode : UInt32 := if specOk then 0 else 2
      let (payload, instanceObj) :=
        renderPrimeEditPlanPayload inst status appliedOk pamOk boundsOk ver buildId none
      IO.println (if pretty then payload.pretty else payload.compress)
      match snapshotOut? with
      | none => pure exitCode
      | some out =>
          if status = "passed" ∨ status = "failed" then
            try
              emitSnapshotSignature out PrimeEditPlanV1.profileId PrimeEditPlanV1.profileVersion
                status instanceObj rawBytes inputPath ver buildId
              pure exitCode
            catch err =>
              IO.eprintln s!"Snapshot signature failed: {err}"
              pure 1
          else
            pure exitCode

/-- Run the `pair_hmm_bridge_v1` profile. -/
def runPairHMMBridgeProfile (inputPath : FilePath) (pretty : Bool := true)
    (ver : String := "dev") (buildId : String := "dev")
    (snapshotOut? : Option FilePath := none) : IO UInt32 := do
  let jsonRaw? ← readJsonInputWithRaw inputPath
  let (json, rawBytes) ←
    match jsonRaw? with
    | Except.ok pair => pure pair
    | Except.error msg =>
        let payload := Json.mkObj
          [ ("profile", Json.str PairHMMBridgeV1.profileId)
          , ("profile_version", Json.str PairHMMBridgeV1.profileVersion)
          , ("status", Json.str "error")
          , ("theorems", Json.arr <| PairHMMBridgeV1.coreTheorems.map Json.str |>.toArray)
          , ("instance", Json.mkObj [("error", Json.str msg)])
          , ("engine", engineInfo ver buildId)
          , ("signature", Json.null)
          ]
        IO.println (if pretty then payload.pretty else payload.compress)
        return 1
  let inst? := decodePairHMMBridgeInstance json
  let inst ←
    match inst? with
    | Except.ok inst => pure inst
    | Except.error msg =>
        let payload := Json.mkObj
          [ ("profile", Json.str PairHMMBridgeV1.profileId)
          , ("profile_version", Json.str PairHMMBridgeV1.profileVersion)
          , ("status", Json.str "error")
          , ("theorems", Json.arr <| PairHMMBridgeV1.coreTheorems.map Json.str |>.toArray)
          , ("instance", Json.mkObj [("error", Json.str msg)])
          , ("engine", engineInfo ver buildId)
          , ("signature", Json.null)
          ]
        IO.println (if pretty then payload.pretty else payload.compress)
        return 1
  let specScore := GlobalAffineV1.specGlobalAffine inst.seqA inst.seqB inst.dpScoring
  let epsilon : Float := 1.0
  let dpSpecOk := Float.abs (inst.dpScore - Float.ofInt specScore) ≤ epsilon
  let specOk :=
    match PairHMMBridgeV1.checkInstance inst with
    | isTrue _ => true
    | isFalse _ => false
  let status := if specOk then "passed" else "failed"
  let exitCode : UInt32 := if specOk then 0 else 2
  let (payload, instanceObj) :=
    renderPairHMMBridgePayload inst status specScore specOk dpSpecOk ver buildId none
  IO.println (if pretty then payload.pretty else payload.compress)
  match snapshotOut? with
  | none => pure exitCode
  | some out =>
      if status = "passed" ∨ status = "failed" then
        try
          emitSnapshotSignature out PairHMMBridgeV1.profileId PairHMMBridgeV1.profileVersion
            status instanceObj rawBytes inputPath ver buildId
          pure exitCode
        catch err =>
          IO.eprintln s!"Snapshot signature failed: {err}"
          pure 1
      else
        pure exitCode

/-- Run the `vcf_normalization_v1` profile. -/
def runVcfNormalizationProfile (inputPath : FilePath) (pretty : Bool := true)
    (ver : String := "dev") (buildId : String := "dev")
    (snapshotOut? : Option FilePath := none) : IO UInt32 := do
  let jsonRaw? ← readJsonInputWithRaw inputPath
  let (json, rawBytes) ←
    match jsonRaw? with
    | Except.ok pair => pure pair
    | Except.error msg =>
        let payload := Json.mkObj
          [ ("profile", Json.str VCF.Normalization.profileId)
          , ("profile_version", Json.str VCF.Normalization.profileVersion)
          , ("status", Json.str "error")
          , ("theorems", Json.arr <| VCF.Normalization.coreTheorems.map Json.str |>.toArray)
          , ("instance", Json.mkObj [("error", Json.str msg)])
          , ("engine", engineInfo ver buildId)
          , ("signature", Json.null)
          ]
        IO.println (if pretty then payload.pretty else payload.compress)
        return 1
  let inst? := decodeVcfNormalizationInstance json
  let inst ←
    match inst? with
    | Except.ok inst => pure inst
    | Except.error msg =>
        let payload := Json.mkObj
          [ ("profile", Json.str VCF.Normalization.profileId)
          , ("profile_version", Json.str VCF.Normalization.profileVersion)
          , ("status", Json.str "error")
          , ("theorems", Json.arr <| VCF.Normalization.coreTheorems.map Json.str |>.toArray)
          , ("instance", Json.mkObj [("error", Json.str msg)])
          , ("engine", engineInfo ver buildId)
          , ("signature", Json.null)
          ]
        IO.println (if pretty then payload.pretty else payload.compress)
        return 1
  let results := inst.variants.map fun r => decide (VCF.Normalization.recordHolds r)
  let allOk := results.all (· = true)
  let status := if allOk then "passed" else "failed"
  let exitCode : UInt32 := if allOk then 0 else 2
  let (payload, instanceObj) := renderVcfNormalizationPayload inst status results ver buildId none
  IO.println (if pretty then payload.pretty else payload.compress)
  match snapshotOut? with
  | none => pure exitCode
  | some out =>
      try
        emitSnapshotSignature out VCF.Normalization.profileId VCF.Normalization.profileVersion
          status instanceObj rawBytes inputPath ver buildId
        pure exitCode
      catch err =>
        IO.eprintln s!"Snapshot signature failed: {err}"
        pure 1

end Profile
end CLI
end Biosim
