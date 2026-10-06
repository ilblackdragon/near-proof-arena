import ArenaCore.Admission
import NearSpec.Challenge
import NearSpecV3.ChunkValidationV0
import NearSpecV3.ClaimV3Props

/-!
# `ArenaCore.ChallengeSpec` instance for `near/pv86/chunk-validation/v0`, domain D0

Draft challenge `near-chunk-validation-d0` (`challenges/drafts/near-chunk-validation-d0.draft.json`).

* `Claim` = well-formed v3 claims (`spec/claim-v3.md`); `encodeClaim`/`decodeClaim` =
  the `near-arena-claim-v3` codec with the proved round trip (`decodeClaim_encode`).
* `Witness` = the raw `witness.bin` bytes (`near-arena-witness-v3`: the real nearcore
  `ChunkStateWitness` borsh + contract code). Decoding is part of the relation: the
  relation, not a decoder outside it, decides what a valid witness is.
* `Rel c w` = `RelD0 c.encode w` = `Rel ∧ InD0` (spec §6): nearcore's chunk validator,
  answering store/epoch queries from `c`, accepts `w` for the endorsed chunk of `c`, and
  the chunk is in D0. Every `Rel_D0` proof therefore establishes the full statement.
* `Domain c` = the claim admits a D0 witness (completeness precondition only).

The same `Claim` type and codec serve every domain `Dk`; a future `Dk` instance changes
`Rel` (to `RelDk`, with `RelDk ⇒ Rel`) and `Domain`, never the formats.
-/

namespace NearSpecV3

open ArenaCore

abbrev WfClaim := { c : Claim // c.wf = true }

def WfClaim.encode (c : WfClaim) : List UInt8 := c.1.encode

def WfClaim.decode (bs : List UInt8) : Option WfClaim :=
  match decodeClaim bs with
  | some c => if h : c.wf = true then some ⟨c, h⟩ else none
  | none => none

theorem WfClaim.decode_encode (c : WfClaim) : WfClaim.decode c.encode = some c := by
  unfold WfClaim.decode WfClaim.encode
  rw [decodeClaim_encode c.1 c.2]
  simp [c.2]

def WfClaim.Rel (c : WfClaim) (w : List UInt8) : Prop := RelD0 c.1.encode w

def WfClaim.Domain (c : WfClaim) : Prop := ∃ w, WfClaim.Rel c w

def challengeSpec : ChallengeSpec where
  Claim := WfClaim
  Witness := List UInt8
  Rel := WfClaim.Rel
  Domain := WfClaim.Domain
  decodeClaim := WfClaim.decode
  encodeClaim := WfClaim.encode
  decode_encode := WfClaim.decode_encode

def challengeParamsWith (profile : SecurityProfile)
    (verifyFuel maxProofBytes maxReductionFuel : Nat) : ChallengeParams where
  spec := challengeSpec
  profile := profile
  verifyFuel := verifyFuel
  maxProofBytes := maxProofBytes
  maxReductionFuel := maxReductionFuel

def verifyFuelV3 : Nat := 1073741824
def maxProofBytesV3 : Nat := 67108864
def maxReductionFuelV3 : Nat := 1073741824

def challengeParams : ChallengeParams :=
  challengeParamsWith NearSpec.TransferV1.profileValidityClassical128 verifyFuelV3 maxProofBytesV3
    maxReductionFuelV3

end NearSpecV3
