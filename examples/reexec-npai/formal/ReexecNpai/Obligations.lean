import ArenaCore.Admission
import NearSpec.Challenge
import ReexecNpai.Main

/-!
# Admission obligations on the approved-interpreter route

The deployed verifier is `interpOracleVerifier code fuel`: the judge's NPAI
interpreter running the image `code = encode program` (route `.interp`,
edge status **checked**). By `interpVerify_eq_check` it computes exactly the
reference model `check`, so the obligations are discharged as for a model
verifier:

* backend `Aux := Witness`, `B := Rel`;
* verifier completeness: the honest proof `encodeProof w` decodes back to `w`
  and is at most `honestProofBound` bytes;
* cryptographic soundness: **deterministic** (no assumption): acceptance means
  `check` holds, i.e. the claim decodes and the decoded witness satisfies
  `NearRelation`.

Everything is stated for an arbitrary profile, reduction budget,
`maxProofBytes ≥ honestProofBound` and fuel `≥ FUEL + 1`.
-/

namespace ReexecNpai

open ArenaCore NearSpec NearSpec.TransferV1

def honestProofBound : Nat := 5000000

def backend : Backend challengeSpec where
  Aux := Witness
  B := fun c w => challengeSpec.Rel c w

theorem backend_sound : backend.SemSound := fun _ w h => ⟨w, h⟩
theorem backend_complete : backend.SemComplete := fun _ w _ h => ⟨w, h⟩

theorem check_sound {cb pb : NearSpec.Bytes} (h : check cb pb = true) :
    ∃ c, WfClaim.decode cb = some c ∧ ∃ w, decodeProof pb = some w ∧ NearRelation c.1 w := by
  unfold check at h
  split at h
  · cases h
  · rename_i c hc
    split at h
    · cases h
    · rename_i w hw
      exact ⟨c, hc, w, hw, of_decide_eq_true h⟩

theorem deployed_eq {fuel : Nat} (hf : FUEL + 1 ≤ fuel) {pub : NearSpec.Bytes} (hpub : pub.length < 4294967296)
    (cb pb : NearSpec.Bytes) : (interpOracleVerifier code fuel).deployed pub cb pb = check cb pb := by
  rw [interpOracleVerifier_deployed]
  exact interpVerify_eq_check hpub hf

theorem deterministicSound {fuel : Nat} (hf : FUEL + 1 ≤ fuel) {pub : NearSpec.Bytes} (hpub : pub.length < 4294967296) :
    DeterministicSound backend.InLang (interpOracleVerifier code fuel).deployed pub := by
  intro cb pb h
  rw [deployed_eq hf hpub] at h
  obtain ⟨c, hc, w, -, hr⟩ := check_sound h
  exact ⟨c, hc, w, hr⟩

theorem encodable_of_rel {c : WfClaim} {w : Witness} (h : WfClaim.Rel c w) : Encodable w := by
  obtain ⟨⟨_, _, _, hlen, _, hmax, _, hslice, _, htwf, hsize⟩, _, _, hrun⟩ := h
  refine ⟨?_, ?_, htwf, hsize, ?_⟩
  · rw [List.all_eq_true] at hslice ⊢
    intro r hr
    have := hslice r hr
    simp only [Receipt.inSlice, Bool.and_eq_true] at this
    exact this.1.1
  · rw [hlen]; simp [Params.maxBatch] at hmax; omega
  · -- a `.hash` root has no revealed value, so the (non-empty) batch fails
    cases ht : w.trie with
    | hash h =>
      exfalso
      obtain ⟨rs, t⟩ := w
      simp only at ht
      subst ht
      cases rs with
      | nil => simp at hlen; simp at *; omega
      | cons r rs =>
        simp [runBatch, applyAll, applyReceipt, PTrie.get] at hrun
    | _ => rfl

theorem honest_length {c : WfClaim} {w : Witness} (h : WfClaim.Rel c w) :
    (encodeProof w).length ≤ honestProofBound := by
  have he := encodable_of_rel h
  have hl := encodeProof_length_le w he
  have h3 := cntT_le w.trie he.trie_wf
  obtain ⟨⟨_, _, _, hlen, _, hmax, _⟩, _⟩ := h
  have := he.trie_size
  simp only [Params.maxBatch, Params.maxWitnessBytes] at hmax this
  unfold honestProofBound; omega

theorem check_complete {c : WfClaim} {w : Witness} (h : WfClaim.Rel c w) :
    check (WfClaim.encode c) (encodeProof w) = true := by
  unfold check
  rw [WfClaim.decode_encode, decodeProof_encodeProof w (encodable_of_rel h)]
  exact decide_eq_true h

theorem verifierComplete {fuel : Nat} (hf : FUEL + 1 ≤ fuel) {pub : NearSpec.Bytes} (hpub : pub.length < 4294967296)
    (mpb : Nat) (hm : honestProofBound ≤ mpb) :
    VerifierComplete challengeSpec (interpOracleVerifier code fuel).deployed pub mpb := by
  intro c w _ h
  refine ⟨encodeProof w, Nat.le_trans (honest_length h) hm, ?_⟩
  rw [deployed_eq hf hpub]
  exact check_complete h

/-- The full admission statement for the approved-interpreter route. -/
theorem admission (prof : SecurityProfile) (fuel mpb red : Nat) (hf : FUEL + 1 ≤ fuel)
    (hm : honestProofBound ≤ mpb) (pub : NearSpec.Bytes) (hpub : pub.length < 4294967296) (pubDigest codeDigest : Digest)
    (hpd : ArenaCore.sha256 pub = pubDigest) (hcd : ArenaCore.sha256 code = codeDigest) :
    AdmissionStatement (challengeParamsWith prof fuel mpb red)
      { publicDigest := pubDigest, impl := .interp codeDigest } :=
  ⟨pub, interpOracleVerifier code fuel, hpd, ⟨code, hcd, rfl⟩, backend,
    { semSound := backend_sound
      semComplete := backend_complete
      verifierComplete := verifierComplete hf hpub mpb hm
      cryptoSound := Or.inl (deterministicSound hf hpub) }⟩

end ReexecNpai
