import ArenaCore.Admission
import NearSpecV3.ChallengeChunkV3
import ReexecV3D3.Model
import ReexecV3D3.NormalForm

/-!
# The admission obligations of the `reexec-v3-d3` backend

The candidate declares tier `D3a` of the coverage-tiered challenge `near-chunk-v3` (docs/CONTRACTS.md
§11) and is admitted under `NearSpecV3.challengeParamsChunkWith .d3a …`: soundness w.r.t.
`RelTier .d3a = D3.RelD3`, completeness on `DomainTier .d3a` (claims with a `RelD3` witness of at most
`maxWitnessChunk` = 64 MiB). Soundness lifts to the statement `RelChunkV3` by the trusted
`NearSpecV3.sound_lift`. Stated for an arbitrary security profile, fuel and reduction budget, and
any `maxProofBytes ≥ 64 MiB`, so the certificate does not depend on how the judge renders those
literals.

* Backend: `Aux := Witness` (the witness bytes), `B := Rel` — semantic soundness and completeness are
  immediate.
* **Verifier completeness.** `DomainTier .d3a c` gives a witness `w₀` with `RelD3` and
  `|w₀| ≤ 64 MiB`. The honest proof is its normal form `canonW (encode c) w₀` (what `prove` emits):
  a `RelD3` witness, in normal form, no longer (`NormalForm.relD3_normal`). No escape: the verifier
  accepts only normal-form bytes.
* **Accepted proofs are normal** (`check_normal`): acceptance ⇒ the proof is the encoding of its own
  pools, every value of them is necessary (dropping any one makes `checkD3` reject), and it is its
  own normal form (`canonW (encode c) pb = pb`).
* Cryptographic soundness: **deterministic** (`DeterministicSound`, ε = 0, no assumption): the
  verifier accepts only if `checkD3 (encode c) pb = .ok ()` for the decoded claim `c`. `RelD3` is
  stated over `ArenaCore.sha256` values that the verifier recomputes from the explicit witness, so
  collision resistance is not needed for soundness (it is what makes `RelD3` meaningful about the
  real chain, spec/near-chunk-validation-v0.md §2.1).
-/

namespace ReexecV3D3

open ArenaCore NearSpecV3

/-- The backend: a relation witness. -/
def backend : Backend (challengeSpecChunk .d3a) where
  Aux := List UInt8
  B := fun c w => (challengeSpecChunk .d3a).Rel c w

theorem backend_sound : backend.SemSound := fun _ w h => ⟨w, h⟩

theorem backend_complete : backend.SemComplete := fun _ w _ h => ⟨w, h⟩

theorem deployed_eq (pub cb pb : ArenaCore.Bytes) :
    Model.verifier.deployed pub cb pb = check cb pb := rfl

/-- What acceptance means: a well-formed claim, `RelD3`, and a normal-form witness. -/
theorem check_sound {cb pb : ArenaCore.Bytes} (h : check cb pb = true) :
    ∃ c, WfClaim.decode cb = some c ∧ WfClaim.RelTier .d3a c pb ∧ normalW c.encode pb = true := by
  unfold check at h
  split at h
  · cases h
  · rename_i c hc
    obtain ⟨hn, ha⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨c, hc, (acceptsD3_iff _ _).mp ha, hn⟩

/-- **Accepted proofs are in normal form**: the proof is the encoding of its own pools, every value
of them is necessary, and it is the normaliser's fixed point. -/
theorem check_normal {cb pb : ArenaCore.Bytes} (h : check cb pb = true) :
    ∃ c, WfClaim.decode cb = some c ∧
      ∃ sw codes s, decodeWitnessFile pb = .ok (sw, codes) ∧ decodeStateWitnessD2 sw = .ok s ∧
        encP c.encode sw (initPools s codes) = pb ∧
        (∀ it ∈ items (initPools s codes),
          ¬ D3.RelD3 c.encode (encP c.encode sw (removeItem (initPools s codes) it))) ∧
        canonW c.encode pb = pb := by
  obtain ⟨c, hc, _, hn⟩ := check_sound h
  exact ⟨c, hc, normalW_sound hn⟩

theorem deterministicSound (pub : ArenaCore.Bytes) :
    DeterministicSound backend.InLang Model.verifier.deployed pub := by
  intro cb pb h
  rw [deployed_eq] at h
  obtain ⟨c, hc, hr, _⟩ := check_sound h
  exact ⟨c, hc, pb, hr⟩

theorem check_complete {c : WfClaim} {w : List UInt8} (h : WfClaim.RelTier .d3a c w)
    (hn : normalW (WfClaim.encode c) w = true) : check (WfClaim.encode c) w = true := by
  unfold check
  rw [WfClaim.decode_encode]
  dsimp only
  rw [hn, Bool.true_and]
  exact (acceptsD3_iff _ _).mpr h

/-- **The prover is complete.** For every `RelD3` witness of a well-formed claim, the prover's
output `canonW` is accepted. -/
theorem check_canonW {c : WfClaim} {w : List UInt8} (h : WfClaim.RelTier .d3a c w) :
    check (WfClaim.encode c) (canonW (WfClaim.encode c) w) = true :=
  check_complete (canonW_rel h) (normalW_canonW h).1

theorem verifierComplete (pub : ArenaCore.Bytes) (mpb : Nat) (hm : maxWitnessChunk ≤ mpb) :
    VerifierComplete (challengeSpecChunk .d3a) Model.verifier.deployed pub mpb := by
  intro c _ hdom _
  obtain ⟨w0, h0, hlen0⟩ := hdom
  obtain ⟨w', h', hn, hlen⟩ := relD3_normal (cb := c.1.encode) h0
  refine ⟨w', Nat.le_trans hlen (Nat.le_trans hlen0 hm), ?_⟩
  have hc : check (WfClaim.encode c) w' = true := check_complete h' hn
  exact (deployed_eq pub ((challengeSpecChunk .d3a).encodeClaim c) w').trans hc

/-- The lifted soundness: every accepted claim is in the challenge statement's language
(`RelChunkV3`), by the trusted `sound_lift`. -/
theorem statementSound (pub : ArenaCore.Bytes) :
    DeterministicSound challengeSpecChunkTop.InLang Model.verifier.deployed pub :=
  sound_lift .d3a _ pub (deterministicSound pub)

/-- The full admission statement for the native-trusted route, for any profile / fuel / reduction
budget and any `maxProofBytes ≥ 64 MiB`. -/
theorem admission (prof : SecurityProfile) (fuel mpb red : Nat) (hm : maxWitnessChunk ≤ mpb)
    (pub : ArenaCore.Bytes) (pubDigest binDigest : Digest) (toolchain : String)
    (hpub : ArenaCore.sha256 pub = pubDigest) :
    AdmissionStatement (challengeParamsChunkWith .d3a prof fuel mpb red)
      { publicDigest := pubDigest, impl := .nativeTrusted binDigest toolchain Model.verifier } :=
  ⟨pub, Model.verifier, hpub, rfl, backend,
    { semSound := backend_sound
      semComplete := backend_complete
      verifierComplete := verifierComplete pub mpb hm
      cryptoSound := Or.inl (deterministicSound pub) }⟩

end ReexecV3D3
