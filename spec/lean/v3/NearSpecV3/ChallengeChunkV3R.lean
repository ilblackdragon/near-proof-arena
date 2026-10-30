import NearSpecV3.ChallengeChunkV3
import NearSpecV3.RungsDefs

/-!
# `near-chunk-v3` v3.1: the rungs as restrictions of `RelD3`

The successor of `ChallengeChunkV3` (v3.0, whose statement is the union of four transcriptions;
that module and its draft are left unchanged). Decision of 2026-10-30 (option 1): each rung is the
top relation restricted to its domain, `RelRungDk := RelD3 ∧ InRungDk` (`Rungs.lean`). The challenge
relation is still the union over the rungs,

  `RelChunkV3R c w := RelRungD0 c w ∨ RelRungD1 c w ∨ RelRungD2 c w ∨ RelD3 c w`,

but now `RelChunkV3R ↔ RelD3` is a theorem (`relChunkV3R_iff`): one transcription is in the trusted
surface. The tiers, rank, admission parameters and the 64 MiB witness bound are v3.0's. A candidate
declaring tier `t` is sound for `RelTierR t`; `sound_liftR` lifts that to the statement. Lower-tier
verifiers are admitted for the rung relations, which include `RelD3`; the fast checkers reach them
only together with a D2 run (`Rungs.rungD1_of_checks` and siblings).
-/

namespace NearSpecV3

open ArenaCore

/-- The rung relation of a tier (v3.1). -/
def RelTierR : Tier → Bytes → Bytes → Prop
  | .d0a => RelRungD0a B0
  | .d0 => RelRungD0
  | .d1 => RelRungD1
  | .d2 => RelRungD2
  | .d3a => D3.RelD3
  | .d1a => RelRungD1a B0

/-- The challenge relation (v3.1). -/
def RelChunkV3R (c w : Bytes) : Prop :=
  RelRungD0 c w ∨ RelRungD1 c w ∨ RelRungD2 c w ∨ D3.RelD3 c w

/-- **`rel_mono`** (v3.1): every tier's relation is a projection into the statement. -/
theorem rel_monoR (t : Tier) (c w : Bytes) (h : RelTierR t c w) : RelChunkV3R c w := by
  cases t with
  | d0a => exact Or.inl (rungD0a_rungD0 h)
  | d0 => exact Or.inl h
  | d1 => exact Or.inr (Or.inl h)
  | d2 => exact Or.inr (Or.inr (Or.inl h))
  | d3a => exact Or.inr (Or.inr (Or.inr h))
  | d1a => exact Or.inr (Or.inl (rungD1a_rungD1 h))

/-- The statement is `RelD3`. -/
theorem relChunkV3R_iff (c w : Bytes) : RelChunkV3R c w ↔ D3.RelD3 c w := by
  constructor
  · rintro (h | h | h | h)
    · exact h.1
    · exact h.1
    · exact h.1
    · exact h
  · exact fun h => Or.inr (Or.inr (Or.inr h))

/-- Every tier relation implies `RelD3`. -/
theorem relTierR_relD3 (t : Tier) (c w : Bytes) (h : RelTierR t c w) : D3.RelD3 c w :=
  (relChunkV3R_iff c w).1 (rel_monoR t c w h)

def WfClaim.RelTierR (t : Tier) (c : WfClaim) (w : List UInt8) : Prop := NearSpecV3.RelTierR t c.1.encode w
def WfClaim.DomainTierR (t : Tier) (c : WfClaim) : Prop :=
  ∃ w, WfClaim.RelTierR t c w ∧ w.length ≤ maxWitnessChunk
def WfClaim.RelChunkR (c : WfClaim) (w : List UInt8) : Prop := RelChunkV3R c.1.encode w

def challengeSpecChunkR (t : Tier) : ChallengeSpec where
  Claim := WfClaim
  Witness := List UInt8
  Rel := WfClaim.RelTierR t
  Domain := WfClaim.DomainTierR t
  decodeClaim := WfClaim.decode
  encodeClaim := WfClaim.encode
  decode_encode := WfClaim.decode_encode

def challengeSpecChunkTopR : ChallengeSpec where
  Claim := WfClaim
  Witness := List UInt8
  Rel := WfClaim.RelChunkR
  Domain := fun c => ∃ w, WfClaim.RelChunkR c w
  decodeClaim := WfClaim.decode
  encodeClaim := WfClaim.encode
  decode_encode := WfClaim.decode_encode

def challengeParamsChunkRWith (t : Tier) (profile : SecurityProfile)
    (verifyFuel maxProofBytes maxReductionFuel : Nat) : ChallengeParams where
  spec := challengeSpecChunkR t
  profile := profile
  verifyFuel := verifyFuel
  maxProofBytes := maxProofBytes
  maxReductionFuel := maxReductionFuel

def challengeParamsChunkR (t : Tier) : ChallengeParams :=
  challengeParamsChunkRWith t NearSpec.TransferV1.profileValidityClassical128 verifyFuelV3
    maxProofBytesV3 maxReductionFuelV3

theorem inLang_monoR (t : Tier) (cb : Bytes) :
    (challengeSpecChunkR t).InLang cb → challengeSpecChunkTopR.InLang cb := by
  rintro ⟨c, hc, w, hw⟩
  exact ⟨c, hc, w, rel_monoR t c.1.encode w hw⟩

theorem sound_liftR (t : Tier) (v : Verifier) (pub : Bytes)
    (h : DeterministicSound (challengeSpecChunkR t).InLang v pub) :
    DeterministicSound challengeSpecChunkTopR.InLang v pub :=
  fun cb pb hacc => inLang_monoR t cb (h cb pb hacc)

/-- info: 'NearSpecV3.relChunkV3R_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms relChunkV3R_iff

end NearSpecV3
