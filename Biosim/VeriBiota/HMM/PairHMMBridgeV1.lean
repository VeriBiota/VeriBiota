import Biosim.VeriBiota.Alignment.GlobalAffineV1

namespace Biosim
namespace VeriBiota
namespace HMM
namespace PairHMMBridgeV1

open Alignment
open Alignment.GlobalAffineV1

structure Transition where
  matchToMatch : Float
  matchToIns : Float
  matchToDel : Float
  insToMatch : Float
  insToIns : Float
  delToMatch : Float
  delToDel : Float
  deriving Repr

structure Emission where
  matchScore : Float
  mismatch : Float
  gap : Float
  deriving Repr

structure HMMParams where
  transition : Transition
  emission : Emission
  deriving Repr

structure Instance where
  seqA : String
  seqB : String
  dpScoring : GlobalAffineV1.Scoring
  hmmParams : HMMParams
  dpScore : Float
  hmmScore : Float
  deriving Repr

def profileId : String := "pair_hmm_bridge_v1"
def profileVersion : String := "1.0.0"
def coreTheorems : List String := ["VB_HMM_001", "VB_HMM_002"]

private def epsilon : Float := 1.0

def SpecHolds (inst : Instance) : Prop :=
  let spec := GlobalAffineV1.specGlobalAffine inst.seqA inst.seqB inst.dpScoring
  let specF := Float.ofInt spec
  Float.abs (inst.dpScore - specF) ≤ epsilon ∧
    Float.abs (inst.dpScore - inst.hmmScore) ≤ epsilon

def checkInstance (inst : Instance) : Decidable (SpecHolds inst) := by
  unfold SpecHolds
  infer_instance

end PairHMMBridgeV1
end HMM
end VeriBiota
end Biosim
