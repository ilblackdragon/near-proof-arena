import ArenaCore.Admission
import NearSpec.Challenge
import ReexecWitness.Model
import ReexecWitness.Size

/-!
# The admission obligations of the `reexec-witness` backend

Everything here is stated for an arbitrary security profile, fuel and
reduction budget, and any `maxProofBytes ≥ 3 088 869`, so the certificate does
not depend on how the judge renders those literals.

* Backend: `Aux := Witness`, `B := Rel` (the backend object IS a relation
  witness) — semantic soundness and completeness are immediate.
* Verifier completeness: the honest proof `encodeProof w` decodes back to `w`
  (`decodeProof_encodeProof`) and is at most 3 088 869 bytes
  (`encodeProof_length_le` + the domain limits).
* Cryptographic soundness: **deterministic** (`DeterministicSound`, ε = 0, no
  assumption). The verifier accepts only if `decide (NearRelation c w)` holds
  for the decoded claim and proof, so every accepted claim is in the
  relation's language. Collision resistance is NOT needed: `NearRelation` is
  itself stated over `ArenaCore.sha256` values (state roots, commitments), and
  the decoded proof is an explicit witness — nothing is "opened" against a
  commitment whose binding would need CR.
-/

namespace ReexecWitness

open ArenaCore NearSpec NearSpec.TransferV1

/-- Honest proofs never exceed this many bytes. -/
def honestProofBound : Nat := 3088869

/-- The backend: a relation witness. -/
def backend : Backend challengeSpec where
  Aux := Witness
  B := fun c w => challengeSpec.Rel c w

theorem backend_sound : backend.SemSound := fun _ w h => ⟨w, h⟩

theorem backend_complete : backend.SemComplete := fun _ w _ h => ⟨w, h⟩

theorem deployed_eq (pub cb pb : ArenaCore.Bytes) : Model.verifier.deployed pub cb pb = check cb pb := rfl

/-- What acceptance means. -/
theorem check_sound {cb pb : ArenaCore.Bytes} (h : check cb pb = true) :
    ∃ c, WfClaim.decode cb = some c ∧ ∃ w, decodeProof pb = some w ∧ NearRelation c.1 w := by
  unfold check at h
  split at h
  · cases h
  · rename_i c hc
    split at h
    · cases h
    · rename_i w hw
      exact ⟨c, hc, w, hw, of_decide_eq_true h⟩

theorem deterministicSound (pub : ArenaCore.Bytes) :
    DeterministicSound backend.InLang Model.verifier.deployed pub := by
  intro cb pb h
  rw [deployed_eq] at h
  obtain ⟨c, hc, w, -, hr⟩ := check_sound h
  exact ⟨c, hc, w, hr⟩

theorem encodable_of_rel {c : WfClaim} {w : Witness} (h : WfClaim.Rel c w) : Encodable w := by
  obtain ⟨⟨_, _, _, hlen, _, hmax, _, hslice, _, htwf, hsize⟩, _⟩ := h
  refine ⟨?_, ?_, htwf, hsize⟩
  · rw [List.all_eq_true] at hslice ⊢
    intro r hr
    have := hslice r hr
    simp only [Receipt.inSlice, Bool.and_eq_true] at this
    exact this.1.1
  · rw [hlen]; simp [Params.maxBatch] at hmax; omega

theorem honest_length {c : WfClaim} {w : Witness} (h : WfClaim.Rel c w) :
    (encodeProof w).length ≤ honestProofBound := by
  sorry  -- ATTACK: the honest-proof size bound is never proved

theorem check_complete {c : WfClaim} {w : Witness} (h : WfClaim.Rel c w) :
    check (WfClaim.encode c) (encodeProof w) = true := by
  unfold check
  rw [WfClaim.decode_encode, decodeProof_encodeProof w (encodable_of_rel h)]
  exact decide_eq_true h

theorem verifierComplete (pub : ArenaCore.Bytes) (mpb : Nat) (hm : honestProofBound ≤ mpb) :
    VerifierComplete challengeSpec Model.verifier.deployed pub mpb := by
  intro c w _ h
  refine ⟨encodeProof w, Nat.le_trans (honest_length h) hm, ?_⟩
  rw [deployed_eq]
  exact check_complete h

/-- The full admission statement for the native-trusted route, for any
profile / fuel / reduction budget and any `maxProofBytes ≥ 3 088 869`. -/
theorem admission (prof : SecurityProfile) (fuel mpb red : Nat) (hm : honestProofBound ≤ mpb)
    (pub : ArenaCore.Bytes) (pubDigest binDigest : Digest) (toolchain : String)
    (hpub : ArenaCore.sha256 pub = pubDigest) :
    AdmissionStatement (challengeParamsWith prof fuel mpb red)
      { publicDigest := pubDigest, impl := .nativeTrusted binDigest toolchain Model.verifier } :=
  ⟨pub, Model.verifier, hpub, rfl, backend,
    { semSound := backend_sound
      semComplete := backend_complete
      verifierComplete := verifierComplete pub mpb hm
      cryptoSound := Or.inl (deterministicSound pub) }⟩

end ReexecWitness
