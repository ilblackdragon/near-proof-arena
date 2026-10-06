import ArenaCore.Admission
import NearSpecV3.ChallengeChunkV3
import ReexecV3D3.Model

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
* **Verifier completeness.** `DomainTier .d3a c` gives a witness `w₀` with `RelD3` and `|w₀| ≤ 64 MiB`. The
  honest proof is its normal form `w₁ = canonW (encode c) w₀` when that is usable (`canonOkOf`: a
  `RelD3` witness, a fixed point of `canonW`, no longer than `w₀`), else `w₀` itself (then `normalW`
  holds by its escape). Either way `normalW` and `RelD3` hold and the size is ≤ 64 MiB; the verifier
  decodes the canonical claim back (`WfClaim.decode_encode`). No lock-step argument through the
  runtime is needed, and none is claimed: that the escape is never taken on a `RelD3` witness is
  tested, not proved (`Canon.lean`).
* **Accepted proofs are normal** (`check_normal`): acceptance ⇒ `canonW (encode c) pb = pb`, or the
  escape.
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

/-- Accepted proofs are the canonical form of themselves (or the escape of `normalW`). -/
theorem check_normal {cb pb : ArenaCore.Bytes} (h : check cb pb = true) :
    ∃ c, WfClaim.decode cb = some c ∧
      (canonW c.encode pb = pb ∨ canonOkOf c.encode pb (canonW c.encode pb) = false) := by
  obtain ⟨c, hc, _, hn⟩ := check_sound h
  refine ⟨c, hc, ?_⟩
  unfold normalW at hn
  rcases Bool.or_eq_true_iff.mp hn with h1 | h2
  · exact Or.inl (beq_iff_eq.mp h1)
  · exact Or.inr (by simpa using h2)

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

/-- **The prover is complete.** For every `RelD3` witness `w`, the prover's output `proveW cb w` is
a `RelD3` witness in normal form, no longer than `w`. -/
theorem proveW_normal {cb w : List UInt8} (h : D3.RelD3 cb w) :
    D3.RelD3 cb (proveW cb w) ∧ normalW cb (proveW cb w) = true ∧ (proveW cb w).length ≤ w.length := by
  unfold proveW
  simp only
  by_cases hok : canonOkOf cb w (canonW cb w) = true
  · rw [if_pos hok]
    have hok' := hok
    unfold canonOkOf at hok'
    obtain ⟨⟨ha, hfix⟩, hlen⟩ := Bool.and_eq_true_iff.mp hok' |>.imp_left Bool.and_eq_true_iff.mp
    refine ⟨(acceptsD3_iff _ _).mp ha, ?_, of_decide_eq_true hlen⟩
    unfold normalW
    simp only at hfix ⊢
    rw [hfix]
    simp
  · rw [if_neg hok]
    refine ⟨h, ?_, Nat.le_refl _⟩
    unfold normalW
    simp only
    have : canonOkOf cb w (canonW cb w) = false := by simpa using hok
    rw [this]
    simp

/-- Every `RelD3` witness has a normal-form witness that is accepted, no longer than it. -/
theorem relD3_normal {cb w : List UInt8} (h : D3.RelD3 cb w) :
    ∃ w', D3.RelD3 cb w' ∧ normalW cb w' = true ∧ w'.length ≤ w.length :=
  ⟨proveW cb w, proveW_normal h⟩

/-- The prover's output for any `RelD3` witness of a well-formed claim is accepted. -/
theorem check_proveW {c : WfClaim} {w : List UInt8} (h : WfClaim.RelTier .d3a c w) :
    check (WfClaim.encode c) (proveW (WfClaim.encode c) w) = true :=
  let ⟨hr, hn, _⟩ := proveW_normal h
  check_complete hr hn

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
