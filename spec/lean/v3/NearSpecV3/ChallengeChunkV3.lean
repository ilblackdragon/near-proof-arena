import NearSpecV3.ChallengeV3
import NearSpecV3.ChunkValidationD1
import NearSpecV3.ChunkValidationD2
import NearSpecV3.D3.FunctionCall

/-!
# `near-chunk-v3`: one challenge for the formalized chunk state-transition domains

The statement is NEAR's stateless chunk validation (`validate_chunk_state_witness`) over the largest
formalized domain. Each domain rung `Rel_Dk = Rel ∧ InDk` is a Lean transcription of nearcore,
difftested against it (`spec/near-chunk-validation-d{0,1,2,3}.md`). The challenge relation is

  `RelChunkV3 c w := RelD0 c w ∨ RelD1 c w ∨ RelD2 c w ∨ RelD3 c w`.

Semantically this is `Rel ∧ (InD0 ∨ InD1 ∨ InD2 ∨ InD3α) = Rel ∧ InD3α`, because the domains are
nested. That nesting is **tested, not proved**: D0 ⊂ D1 ⊂ D2 on the public fixtures and corpora,
and D2 ⊂ D3 on the D3 corpora. The disjunction makes the statement independent of that test
evidence. Every rung's acceptance is a nearcore-endorsed witness, so their union is one too.

**Tiers and the admission obligations.** A candidate declares a tier `t ∈ {D0, D1, D2, D3α}` and is
admitted under the standard `AdmissionStatement` of `challengeParamsChunk t`. That gives soundness
w.r.t. `RelTier t` and completeness on `DomainTier t`.

`rel_mono` and `sound_lift` lift soundness to the challenge statement: a verifier sound for `Rel_Dk`
is sound for `RelChunkV3`. A D0-only succinct prover and a full D3α re-executor are therefore admitted
to the same challenge for the same claim of soundness. They differ only in their proven coverage.
Outside its tier a candidate may answer `UNSUPPORTED`; that is never a soundness failure.

A future rung (D4, D∞) is added as a new disjunct in a versioned successor. `rel_mono` keeps
holding for the existing tiers.
-/

namespace NearSpecV3

open ArenaCore

/-- The declared coverage tiers, in increasing domain order. -/
inductive Tier where
  | d0 | d1 | d2 | d3a
  deriving DecidableEq, Repr

def Tier.rank : Tier → Nat
  | .d0 => 0 | .d1 => 1 | .d2 => 2 | .d3a => 3

/-- The rung relation of a tier, on claim and witness bytes. -/
def RelTier : Tier → Bytes → Bytes → Prop
  | .d0 => RelD0
  | .d1 => RelD1
  | .d2 => RelD2
  | .d3a => D3.RelD3

/-- The challenge relation: any formalized rung endorses the witness. -/
def RelChunkV3 (c w : Bytes) : Prop := RelD0 c w ∨ RelD1 c w ∨ RelD2 c w ∨ D3.RelD3 c w

/-- **`rel_mono`**: every rung's relation implies the challenge relation. -/
theorem rel_mono (t : Tier) (c w : Bytes) (h : RelTier t c w) : RelChunkV3 c w := by
  cases t with
  | d0 => exact Or.inl h
  | d1 => exact Or.inr (Or.inl h)
  | d2 => exact Or.inr (Or.inr (Or.inl h))
  | d3a => exact Or.inr (Or.inr (Or.inr h))

/-! ## `ChallengeSpec` instances -/

def WfClaim.RelTier (t : Tier) (c : WfClaim) (w : List UInt8) : Prop := NearSpecV3.RelTier t c.1.encode w
def WfClaim.DomainTier (t : Tier) (c : WfClaim) : Prop := ∃ w, WfClaim.RelTier t c w
def WfClaim.RelChunk (c : WfClaim) (w : List UInt8) : Prop := RelChunkV3 c.1.encode w

/-- The spec a candidate declaring tier `t` is admitted under: soundness w.r.t. `Rel_t`,
completeness on the claims that have a `Rel_t` witness. -/
def challengeSpecChunk (t : Tier) : ChallengeSpec where
  Claim := WfClaim
  Witness := List UInt8
  Rel := WfClaim.RelTier t
  Domain := WfClaim.DomainTier t
  decodeClaim := WfClaim.decode
  encodeClaim := WfClaim.encode
  decode_encode := WfClaim.decode_encode

/-- The challenge statement (the language every admitted verifier is sound for). -/
def challengeSpecChunkTop : ChallengeSpec where
  Claim := WfClaim
  Witness := List UInt8
  Rel := WfClaim.RelChunk
  Domain := fun c => ∃ w, WfClaim.RelChunk c w
  decodeClaim := WfClaim.decode
  encodeClaim := WfClaim.encode
  decode_encode := WfClaim.decode_encode

def challengeParamsChunk (t : Tier) : ChallengeParams where
  spec := challengeSpecChunk t
  profile := NearSpec.TransferV1.profileValidityClassical128
  verifyFuel := verifyFuelV3
  maxProofBytes := maxProofBytesV3
  maxReductionFuel := maxReductionFuelV3

/-- Language inclusion: a claim true at any tier is true for the challenge statement. -/
theorem inLang_mono (t : Tier) (cb : Bytes) :
    (challengeSpecChunk t).InLang cb → challengeSpecChunkTop.InLang cb := by
  rintro ⟨c, hc, w, hw⟩
  exact ⟨c, hc, w, rel_mono t c.1.encode w hw⟩

/-- **Soundness lifting**: a verifier deterministically sound for a tier's language is sound for
the challenge statement. -/
theorem sound_lift (t : Tier) (v : Verifier) (pub : Bytes)
    (h : DeterministicSound (challengeSpecChunk t).InLang v pub) :
    DeterministicSound challengeSpecChunkTop.InLang v pub :=
  fun cb pb hacc => inLang_mono t cb (h cb pb hacc)

end NearSpecV3
