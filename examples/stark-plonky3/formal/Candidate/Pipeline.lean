import Candidate.Backend

/-!
# The STARK pipeline, with every open obligation as an explicit hypothesis

Nothing in `StarkModel` models real code: every field is an opaque
parameter. The file fixes, kernel-checked, *how* the open obligations compose
into soundness against the NEAR relation, so each can be discharged (or
refuted) separately. Chain for `verify` accepting `(pub, claim.bin, proof.bin)`:

1. **IMPL** — the native `out/verify` (our framing + strict claim decoding +
   Plonky3 `p3-batch-stark` 3acc8b70 `verify_batch`, KoalaBear⁸, SHA-256
   Merkle/transcript) computes `StarkModel.verify`. Open (no Lean model of the
   Rust verifier; Aeneas/hax extraction not attempted).
2. **AIR-ID** — `pub` names the AIR/config compiled into the verifier
   (`public.bin` digest = Schwartz–Zippel fingerprint of every constraint and
   bus interaction + FRI parameters). Tested (deterministic; recomputed by
   `verify`).
3. **STARK/FRI/FS** — if `verify` accepts then either nine traces exist that
   satisfy every constraint of the AIR named in `pub` with public values =
   the claim's fixed-width bytes and balance every LogUp bus, or a forgery
   event happened (DEEP-ALI + FRI round-by-round soundness, LogUp
   Schwartz–Zippel, Merkle binding, Fiat–Shamir in the ROM over SHA-256).
   `Pr[Forged] ≤ ε` is the open crypto obligation; Plonky3's unverified
   calculator gives ≈ 2^-103 (unique decoding) per proof at our parameters.
4. **AIR ⇒ RELATION** — satisfying traces for a claim imply the claim is in
   the relation's language (our hand-written AIR is semantically sound:
   SHA-256 compression and padding, nearcore borsh layouts, trie walk,
   u128 arithmetic, domain checks). Open as a proof; *tested*: byte-identical
   claims on all public fixtures, native self-check, witness-mutation probe.
-/

namespace Candidate.Pipeline

open ArenaCore

/-- Opaque parameters describing the STARK pipeline. -/
structure StarkModel where
  /-- The deployed verifier as a total function `pub → claim → proof → accept?`. -/
  verify : Verifier
  /-- The AIR/config identity recorded in the public artifact. -/
  airOf : Bytes → Option Bytes
  /-- The AIR/config identity of the constraint system compiled into `verify`. -/
  airId : Bytes
  /-- Traces satisfying every constraint and bus of AIR `a` with public values
  determined by the claim bytes `cb` exist. -/
  Satisfiable : Bytes → Bytes → Prop
  /-- The forgery event for an accepted `(pub, claim, proof)`. -/
  Forged : Bytes → Bytes → Bytes → Prop

variable (m : StarkModel) (pub : Bytes)

/-- (3) STARK soundness as a dichotomy; `Pr[Forged] ≤ ε` is separate. -/
def StarkSoundOrForged : Prop :=
  ∀ cb pb, m.verify pub cb pb = true →
    (∃ a, m.airOf pub = some a ∧ m.Satisfiable a cb) ∨ m.Forged pub cb pb

/-- (2) The public artifact names the compiled AIR. -/
def AirBinding : Prop := m.airOf pub = some m.airId

/-- (4) The hand-written AIR refines the NEAR relation. -/
def AirRefines : Prop := ∀ cb, m.Satisfiable m.airId cb → nearSpec.InLang cb

/-- Composition (kernel-checked): under (2)–(4) every accepted claim is in the
relation's language unless a forgery event occurred. -/
theorem sound_or_forged (h3 : StarkSoundOrForged m pub) (h2 : AirBinding m pub)
    (h4 : AirRefines m) :
    ∀ cb pb, m.verify pub cb pb = true → nearSpec.InLang cb ∨ m.Forged pub cb pb := by
  intro cb pb hacc
  rcases h3 cb pb hacc with ⟨a, ha, hsat⟩ | hf
  · left
    rw [h2] at ha
    cases ha
    exact h4 cb hsat
  · exact Or.inr hf

/-- With no forgery event the conclusion is `ArenaCore.DeterministicSound`. -/
theorem deterministic_of_no_forgery (hnf : ∀ cb pb, ¬ m.Forged pub cb pb)
    (h3 : StarkSoundOrForged m pub) (h2 : AirBinding m pub) (h4 : AirRefines m) :
    DeterministicSound nearSpec.InLang m.verify pub := by
  intro cb pb hacc
  rcases sound_or_forged m pub h3 h2 h4 cb pb hacc with h | h
  · exact h
  · exact absurd h (hnf cb pb)

end Candidate.Pipeline
