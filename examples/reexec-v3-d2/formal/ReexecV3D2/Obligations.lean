import ArenaCore.Admission
import NearSpecV3.ChallengeD2
import ReexecV3D2.Model
import ReexecV3D2.Size
import ReexecV3D2.NormalForm

/-!
# The admission obligations of the `reexec-v3-d2` backend

Stated for an arbitrary security profile, fuel and reduction budget, and any
`maxProofBytes ≥ 8 388 641`, so the certificate does not depend on how the
judge renders those literals.

* Backend: `Aux := Witness` (the witness bytes), `B := Rel` — semantic
  soundness and completeness are immediate.
* Verifier completeness: the honest proof is the **normal form** `w'` of the
  witness `w`, computed by the prover's normaliser `normSW` (`relD2_normal`,
  `NormalForm.lean`: ignored header fields and block hashes zeroed, receipt-proof
  entries deduplicated and sorted, every `base_state` cut to its read set; `RelD2`
  still holds by `checkD2_normal`, the normal form is a fixed point of `normSW` by
  `normSW_spec`, and `|w'| ≤ |w|`); the verifier decodes the canonical claim back
  (`WfClaim.decode_encode`, the proved codec round trip of `NearSpecV3.ChallengeV3`),
  checks `normalW (encode c) w'` and decides `RelD2 (encode c) w'`;
  `|w| ≤ 8 388 641` by `relD2_witness_length` (`Size.lean`).
* Accepted proofs are normal: `normalW_sound` / `normalW_fixed` (`NormalForm.lean`).
* Cryptographic soundness: **deterministic** (`DeterministicSound`, ε = 0, no
  assumption). The verifier accepts only if `decide (RelD2 (encode c) pb)`
  holds for the decoded claim `c`, so every accepted claim is in the
  relation's language with witness `pb`. Collision resistance is not needed:
  `RelD2` is itself stated over `ArenaCore.sha256` values (block hashes,
  chunk-header roots, state roots, receipt-proof paths), recomputed by the
  verifier from the explicit witness; nothing is opened against a commitment
  whose binding would need CR. CR is what makes `RelD2` *meaningful* about the
  real chain (spec §2.1, §4), not a gap between verifier and relation.
-/

namespace ReexecV3D2

open ArenaCore NearSpecV3

/-- Honest proofs (= witnesses of `RelD2`) never exceed this many bytes. -/
def honestProofBound : Nat := 8388641

/-- The backend: a relation witness. -/
def backend : Backend challengeSpecD2 where
  Aux := List UInt8
  B := fun c w => challengeSpecD2.Rel c w

theorem backend_sound : backend.SemSound := fun _ w h => ⟨w, h⟩

theorem backend_complete : backend.SemComplete := fun _ w _ h => ⟨w, h⟩

theorem deployed_eq (pub cb pb : ArenaCore.Bytes) :
    Model.verifier.deployed pub cb pb = check cb pb := rfl

/-- What acceptance means. -/
theorem check_sound {cb pb : ArenaCore.Bytes} (h : check cb pb = true) :
    ∃ c, WfClaim.decode cb = some c ∧ WfClaim.RelD2 c pb := by
  unfold check at h
  split at h
  · cases h
  · rename_i c hc
    have hr : RelD2 c.encode pb := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
    exact ⟨c, hc, hr⟩

theorem deterministicSound (pub : ArenaCore.Bytes) :
    DeterministicSound backend.InLang Model.verifier.deployed pub := by
  intro cb pb h
  rw [deployed_eq] at h
  obtain ⟨c, hc, hr⟩ := check_sound h
  exact ⟨c, hc, pb, hr⟩

theorem check_complete {c : WfClaim} {w : List UInt8} (h : WfClaim.RelD2 c w)
    (hc : normalW (WfClaim.encode c) w = true) : check (WfClaim.encode c) w = true := by
  unfold check
  rw [WfClaim.decode_encode]
  dsimp only
  rw [hc, Bool.true_and]
  exact decide_eq_true h

theorem honest_length {c : WfClaim} {w : List UInt8} (h : WfClaim.RelD2 c w) :
    w.length ≤ honestProofBound := relD2_witness_length h

theorem verifierComplete (pub : ArenaCore.Bytes) (mpb : Nat) (hm : honestProofBound ≤ mpb) :
    VerifierComplete challengeSpecD2 Model.verifier.deployed pub mpb := by
  intro c w _ h
  obtain ⟨w', h', hcan, hlen⟩ := relD2_normal (cb := c.1.encode) h
  refine ⟨w', Nat.le_trans hlen (Nat.le_trans (honest_length h) hm), ?_⟩
  have hc : check (WfClaim.encode c) w' = true := check_complete h' hcan
  exact (deployed_eq pub (challengeSpecD2.encodeClaim c) w').trans hc

/-- The challenge parameters of `near-chunk-validation-d2` as the judge renders them
(`spec/lean/judge/ExpectedV3D2.native-lean.lean.template`): the relation of
`NearSpecV3.challengeSpecD2` with the judge's profile and budgets. -/
def paramsD2With (prof : SecurityProfile) (fuel mpb red : Nat) : ChallengeParams where
  spec := challengeSpecD2
  profile := prof
  verifyFuel := fuel
  maxProofBytes := mpb
  maxReductionFuel := red

/-- The full admission statement for the native-trusted route, for any
profile / fuel / reduction budget and any `maxProofBytes ≥ 8 388 641`. -/
theorem admission (prof : SecurityProfile) (fuel mpb red : Nat) (hm : honestProofBound ≤ mpb)
    (pub : ArenaCore.Bytes) (pubDigest binDigest : Digest) (toolchain : String)
    (hpub : ArenaCore.sha256 pub = pubDigest) :
    AdmissionStatement (paramsD2With prof fuel mpb red)
      { publicDigest := pubDigest, impl := .nativeTrusted binDigest toolchain Model.verifier } :=
  ⟨pub, Model.verifier, hpub, rfl, backend,
    { semSound := backend_sound
      semComplete := backend_complete
      verifierComplete := verifierComplete pub mpb hm
      cryptoSound := Or.inl (deterministicSound pub) }⟩

end ReexecV3D2
