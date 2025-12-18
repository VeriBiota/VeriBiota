import Lean.Data.Json

namespace Biosim
namespace VeriBiota
namespace Provenance
namespace SnapshotSignatureV1

open Lean

/-- Manifest metadata bound into every emitted snapshot signature. -/
structure ManifestEntry where
  schemaPath : String
  schemaHash : String
  theorems : List String
  deriving Repr, DecidableEq

/-- `snapshot_signature_v1` payload (provenance, not a cryptographic signature). -/
structure SnapshotSignature where
  snapshotProfile : String
  snapshotProfileVersion : String
  snapshotHash : String
  schemaHash : String
  schemaId : String
  theoremIds : List String
  veribiotaBuildId : String
  veribiotaVersion : String
  leanVersion : String
  timestampUtc : String
  verificationResult : String
  instanceSummary : Json

namespace SnapshotSignature

def mkFromDigest (profileId profileVersion status : String) (instanceSummary : Json)
    (digestHex : String) (manifest : ManifestEntry) (ver buildId timestampUtc : String) :
    SnapshotSignature :=
  { snapshotProfile := profileId
    , snapshotProfileVersion := profileVersion
    , snapshotHash := s!"sha256:{digestHex}"
    , schemaHash := manifest.schemaHash
    , schemaId := manifest.schemaPath
    , theoremIds := manifest.theorems
    , veribiotaBuildId := buildId
    , veribiotaVersion := ver
    , leanVersion := Lean.versionString
    , timestampUtc := timestampUtc
    , verificationResult := status
    , instanceSummary := instanceSummary }

def toJson (sig : SnapshotSignature) : Json :=
  Json.mkObj
    [ ("snapshot_profile", Json.str sig.snapshotProfile)
    , ("snapshot_profile_version", Json.str sig.snapshotProfileVersion)
    , ("snapshot_hash", Json.str sig.snapshotHash)
    , ("schema_hash", Json.str sig.schemaHash)
    , ("schema_id", Json.str sig.schemaId)
    , ("theorem_ids", Json.arr <| sig.theoremIds.map Json.str |>.toArray)
    , ("veribiota_build_id", Json.str sig.veribiotaBuildId)
    , ("veribiota_version", Json.str sig.veribiotaVersion)
    , ("lean_version", Json.str sig.leanVersion)
    , ("timestamp_utc", Json.str sig.timestampUtc)
    , ("verification_result", Json.str sig.verificationResult)
    , ("instance_summary", sig.instanceSummary)
    ]

theorem mkFromDigest_binds_manifest (profileId profileVersion status : String)
    (instanceSummary : Json) (digestHex : String) (manifest : ManifestEntry)
    (ver buildId timestampUtc : String) :
    let sig :=
      mkFromDigest profileId profileVersion status instanceSummary digestHex
        manifest ver buildId timestampUtc
    sig.snapshotHash = s!"sha256:{digestHex}" ∧
      sig.schemaHash = manifest.schemaHash ∧
      sig.schemaId = manifest.schemaPath ∧
      sig.theoremIds = manifest.theorems := by
  simp [mkFromDigest]

end SnapshotSignature

end SnapshotSignatureV1
end Provenance
end VeriBiota
end Biosim
