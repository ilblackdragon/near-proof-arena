import ArenaCore.Admission
import NearSpec.ClaimCodec

/-!
# The canonical `ArenaCore.ChallengeSpec` / `ChallengeParams` instance

for challenge `near-transfer-receipt-v1` (statement
`near/pv86/receipt-transfer-batch/v0`, claim format `near-arena-claim-v1`).

* `challengeSpec` — `Claim` = well-formed claims (`WfClaim`), `Witness`,
  `Rel` = `NearRelation`, `Domain` = the claim-level domain, and the strict
  `claim.bin` codec with its proved round trip.
* `challengeParamsWith …` — the judge's Expected module instantiates this with
  values spliced (as literals) from the frozen `ChallengeDefinition`
  (`security_profile`, `formal_params`); `challengeParams` is the canonical
  instance with the values chosen for v1 (documented in
  `spec/near-transfer-receipt-v1.md` §12). The two coincide when the
  definition carries the canonical values (`challengeParams_canonical`).
-/

namespace NearSpec.TransferV1

open ArenaCore

def challengeSpec : ChallengeSpec where
  Claim := WfClaim
  Witness := Witness
  Rel := WfClaim.Rel
  Domain := WfClaim.ClaimDomain
  decodeClaim := WfClaim.decode
  encodeClaim := WfClaim.encode
  decode_encode := WfClaim.decode_encode

/-- Security model from the profile JSON's `model` string. Unknown strings
map to the *standard* model, which never authorises the ROM game. -/
def secModelOf (s : String) : SecModel :=
  if s = "random_oracle" then .randomOracle else .standard

/-- Assumption ids of `security/assumptions/*.json` → `ArenaCore.AssumptionId`.
Unknown ids are dropped (never widen what is allowed). -/
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

/-- `security/profiles/validity-classical-128.json`. -/
def profileValidityClassical128 : SecurityProfile :=
  profileOf "validity-classical-128" "random_oracle" 128
    ["sha256-collision-resistance", "random-oracle-fiat-shamir-sha256"] 40 64

/-- v1 resource parameters (see spec doc §12):
* `maxProofBytes` = 8 MiB: a re-execution proof carrying the full witness
  (`max_witness_bytes` 4 MiB) and the receipts (`max_request_bytes` 128 KiB)
  fits with room for framing.
* `verifyFuel` = 2^30 NPAI fuel: ~128 instructions per byte of a maximal proof.
* `maxReductionFuel` = 2^30: same budget for an explicit CR reduction. -/
def verifyFuelV1 : Nat := 1073741824
def maxProofBytesV1 : Nat := 8388608
def maxReductionFuelV1 : Nat := 1073741824

def challengeParams : ChallengeParams :=
  challengeParamsWith profileValidityClassical128 verifyFuelV1 maxProofBytesV1 maxReductionFuelV1

theorem challengeParams_canonical :
    challengeParamsWith
      (profileOf "validity-classical-128" "random_oracle" 128
        ["sha256-collision-resistance", "random-oracle-fiat-shamir-sha256"] 40 64)
      1073741824 8388608 1073741824 = challengeParams := rfl

/-- The profile resolves to the ROM model with both governed assumptions. -/
example : profileValidityClassical128.model = .randomOracle ∧
    profileValidityClassical128.allowedAssumptions =
      [.sha256CollisionResistance, .sha256RandomOracle] := by decide

end NearSpec.TransferV1
