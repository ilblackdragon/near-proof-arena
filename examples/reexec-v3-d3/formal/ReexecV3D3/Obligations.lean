import ArenaCore.Admission
import NearSpecV3.ChallengeChunkV3
import ReexecV3D3.Model
import ReexecV3D3.ReadComplete

/-!
Admission obligations for the D3α read-set reference. The prover emits
`Read.canonW`, whose acceptance and non-expansion are proved in `ReadComplete`.
The verifier accepts only literal read-set-normal bytes and establishes the
original frozen D3 relation; soundness lifts to the unified chunk statement.
This is deterministic witness re-execution, not a succinct proof system.
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

/-- Acceptance establishes the frozen relation and the read-set check. -/
theorem check_sound {cb pb : ArenaCore.Bytes} (h : check cb pb = true) :
    ∃ c, WfClaim.decode cb = some c ∧ WfClaim.RelTier .d3a c pb ∧ Read.check c.encode pb = true := by
  unfold check at h
  split at h
  · cases h
  · rename_i c hc
    exact ⟨c, hc, Read.check_sound h, h⟩

/-- Accepted bytes are literally their own read-set normal form. -/
theorem check_normal {cb pb : ArenaCore.Bytes} (h : check cb pb = true) :
    ∃ c, WfClaim.decode cb = some c ∧ Read.canonW c.encode pb = pb := by
  obtain ⟨c, hc, _, hn⟩ := check_sound h
  exact ⟨c, hc, Read.check_normal hn⟩

theorem deterministicSound (pub : ArenaCore.Bytes) :
    DeterministicSound backend.InLang Model.verifier.deployed pub := by
  intro cb pb h
  rw [deployed_eq] at h
  obtain ⟨c, hc, hr, _⟩ := check_sound h
  exact ⟨c, hc, pb, hr⟩

theorem check_complete {c : WfClaim} {w : List UInt8}
    (hn : Read.check (WfClaim.encode c) w = true) : check (WfClaim.encode c) w = true := by
  unfold check
  rw [WfClaim.decode_encode]
  exact hn

/-- The honest read-set proof is accepted for every valid relation witness. -/
theorem check_canonW {c : WfClaim} {w : List UInt8} (h : WfClaim.RelTier .d3a c w) :
    check (WfClaim.encode c) (Read.canonW (WfClaim.encode c) w) = true :=
  check_complete (Read.check_canonW h).1

theorem verifierComplete (pub : ArenaCore.Bytes) (mpb : Nat) (hm : maxWitnessChunk ≤ mpb) :
    VerifierComplete (challengeSpecChunk .d3a) Model.verifier.deployed pub mpb := by
  intro c _ hdom _
  obtain ⟨w0, h0, hlen0⟩ := hdom
  have hp := Read.check_canonW h0
  refine ⟨Read.canonW c.1.encode w0, Nat.le_trans hp.2 (Nat.le_trans hlen0 hm), ?_⟩
  exact (deployed_eq pub ((challengeSpecChunk .d3a).encodeClaim c)
    (Read.canonW c.1.encode w0)).trans (check_complete hp.1)

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
