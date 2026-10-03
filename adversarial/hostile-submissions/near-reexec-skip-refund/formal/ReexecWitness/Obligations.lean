import ArenaCore.Admission
import NearSpec.Challenge
import ReexecWitness.Model
import ReexecWitness.Size

/-!
# HOSTILE: obligations for a *weakened* challenge

The verifier (`Model.lean`) skips the refund outputs. Every obligation of the
real admission statement holds for it EXCEPT soundness w.r.t. `NearRelation`.
So the author restates the challenge with the weakened relation and proves the
admission statement for THAT — a genuine, axiom-clean proof of the wrong
theorem. The judge constructs the type itself, so this must fail with
THEOREM_TYPE_MISMATCH.
-/

namespace ReexecWitness

open ArenaCore NearSpec NearSpec.TransferV1

def honestProofBound : Nat := 3088869

/-- The attacker's restated challenge: same claims/codec/domain, weaker `Rel`. -/
def weakSpec : ChallengeSpec where
  Claim := WfClaim
  Witness := Witness
  Rel := fun c w => WeakRelation c.1 w
  Domain := WfClaim.ClaimDomain
  decodeClaim := WfClaim.decode
  encodeClaim := WfClaim.encode
  decode_encode := WfClaim.decode_encode

def weakParams (prof : SecurityProfile) (fuel mpb red : Nat) : ChallengeParams :=
  { spec := weakSpec, profile := prof, verifyFuel := fuel, maxProofBytes := mpb,
    maxReductionFuel := red }

def backend : Backend weakSpec where
  Aux := Witness
  B := fun c w => weakSpec.Rel c w

theorem deployed_eq (pub cb pb : ArenaCore.Bytes) :
    Model.verifier.deployed pub cb pb = check cb pb := rfl

theorem encodable_of_static {c : Claim} {w : Witness} (h : DomainStatic c w) : Encodable w := by
  obtain ⟨_, _, _, hlen, _, hmax, _, hslice, _, htwf, hsize⟩ := h
  refine ⟨?_, ?_, htwf, hsize⟩
  · rw [List.all_eq_true] at hslice ⊢
    intro r hr
    have := hslice r hr
    simp only [Receipt.inSlice, Bool.and_eq_true] at this
    exact this.1.1
  · rw [hlen]; simp [Params.maxBatch] at hmax; omega

theorem honest_length {c : WfClaim} {w : Witness} (h : WeakRelation c.1 w) :
    (encodeProof w).length ≤ honestProofBound := by
  have he := encodable_of_static h.1
  have hl := encodeProof_length_le w he.receipts_wf he.trie_wf
  obtain ⟨⟨_, _, _, hlen, _, hmax, _⟩, _⟩ := h
  have := he.trie_size
  simp only [Params.maxBatch] at hmax
  unfold honestProofBound; omega

theorem check_complete {c : WfClaim} {w : Witness} (h : WeakRelation c.1 w) :
    check (WfClaim.encode c) (encodeProof w) = true := by
  unfold check
  rw [WfClaim.decode_encode, decodeProof_encodeProof w (encodable_of_static h.1)]
  exact decide_eq_true h

theorem check_sound {cb pb : ArenaCore.Bytes} (h : check cb pb = true) :
    ∃ c, WfClaim.decode cb = some c ∧ ∃ w, WeakRelation c.1 w := by
  unfold check at h
  split at h
  · cases h
  · rename_i c hc
    split at h
    · cases h
    · rename_i w _
      exact ⟨c, hc, w, of_decide_eq_true h⟩

theorem admission_weak (prof : SecurityProfile) (fuel mpb red : Nat) (hm : honestProofBound ≤ mpb)
    (pub : ArenaCore.Bytes) (pubDigest binDigest : Digest) (toolchain : String)
    (hpub : ArenaCore.sha256 pub = pubDigest) :
    AdmissionStatement (weakParams prof fuel mpb red)
      { publicDigest := pubDigest, impl := .nativeTrusted binDigest toolchain Model.verifier } := by
  refine ⟨pub, Model.verifier, hpub, rfl, backend,
    { semSound := fun _ w h => ⟨w, h⟩
      semComplete := fun _ w _ h => ⟨w, h⟩
      verifierComplete := ?_
      cryptoSound := Or.inl ?_ }⟩
  · intro c w _ h
    refine ⟨encodeProof w, Nat.le_trans (honest_length h) hm, ?_⟩
    rw [deployed_eq]
    exact check_complete h
  · intro cb pb hacc
    rw [deployed_eq] at hacc
    obtain ⟨c, hc, w, hw⟩ := check_sound hacc
    exact ⟨c, hc, w, hw⟩

end ReexecWitness
