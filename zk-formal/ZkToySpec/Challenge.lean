import ArenaCore.Admission

/-!
# ZkToySpec.Challenge — a DEMO toy challenge for the np-udr-stark pipeline test (M2)

**Not a governed challenge.**  A local, minimal `ChallengeSpec` used to run the
complete formal pipeline (L1–L4, L7, L8, the real formal checker) end to end before
the NEAR AIR (L6) lands.  It plays the role `NearSpec.Challenge` plays for the NEAR
challenge: it is a *trusted* package for the toy checker run, depends only on
`ArenaCore`, and the judge's Expected module is rendered from it.

Relation ("square root of a byte"): the claim is one byte `b`, a witness is a natural
`w` with `w * w = b`.  Claim bytes: exactly `[b]`.
-/

namespace ZkToySpec

open ArenaCore

def decode : Bytes → Option UInt8
  | [b] => some b
  | _ => none

def encode (b : UInt8) : Bytes := [b]

def challengeSpec : ChallengeSpec where
  Claim := UInt8
  Witness := Nat
  Rel := fun b w => w * w = b.toNat
  Domain := fun _ => True
  decodeClaim := decode
  encodeClaim := encode
  decode_encode := fun _ => rfl

/-- Security model from the profile JSON's `model` string (as `NearSpec`). -/
def secModelOf (s : String) : SecModel :=
  if s = "random_oracle" then .randomOracle else .standard

def assumptionOf (s : String) : List AssumptionId :=
  if s = "sha256-collision-resistance" then [.sha256CollisionResistance]
  else if s = "random-oracle-fiat-shamir-sha256" then [.sha256RandomOracle]
  else []

def profileOf (id model : String) (targetBits : Nat) (allowed : List String)
    (maxProverQueriesLog2 maxHashQueriesLog2 : Nat) : SecurityProfile where
  id := id
  model := secModelOf model
  targetBits := targetBits
  allowedAssumptions := allowed.flatMap assumptionOf
  maxProverQueriesLog2 := maxProverQueriesLog2
  maxHashQueriesLog2 := maxHashQueriesLog2

def challengeParamsWith (profile : SecurityProfile)
    (verifyFuel maxProofBytes maxReductionFuel : Nat) : ChallengeParams where
  spec := challengeSpec
  profile := profile
  verifyFuel := verifyFuel
  maxProofBytes := maxProofBytes
  maxReductionFuel := maxReductionFuel

end ZkToySpec
