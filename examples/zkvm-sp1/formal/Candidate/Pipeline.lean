import Candidate.Backend

/-!
# The SP1 pipeline, with every open obligation as an explicit hypothesis

Nothing in `Sp1Model` is a model of real SP1 code: every field is an opaque
parameter. The point of this file is to fix, in kernel-checked form, *how*
the open obligations would compose into soundness against the NEAR relation,
so that each one can later be discharged (or shown false) separately.

Real chain for `verify` accepting `(pub, claim.bin, proof.bin)`:

1. **IMPL** — the native `out/verify` binary computes `Sp1Model.verify`
   (Rust: sp1-verifier 6.8.1 compressed verifier + our framing). Open; best
   possible today is the `.nativeTrusted` route (a *trusted* edge).
2. **STARK/FS + RECURSION** — if `verify` accepts, then either the
   recursion-compressed proof attests a satisfying SP1 RISC-V execution record
   for the program vkey in `pub` with public-values digest = H(claim.bin), or a
   *forgery event* happened (Fiat–Shamir over Poseidon2/KoalaBear, Jagged
   PCS / BaseFold / FRI-style proximity, LogUp-GKR, sumcheck, 124 queries at
   blowup 4 + 16-bit grinding, SP1 target 100 bits; recursion verifier
   circuits; vk Merkle root). Bounding `Pr[forgery]` is the open crypto
   obligation; it is NOT expressible with the arena's approved assumptions
   (`sha256_cr`, `sha256_rom`): SP1's transcript and commitments use Poseidon2.
3. **VKEY** — the vkey in `pub` is SP1 `setup` of the pinned guest ELF.
   Holds by construction of the judge-run `prepare` (tested, not proved).
4. **CONSTRAINTS** — a satisfying SP1 execution record for `setup elf` with
   public values `pv` implies the RISC-V ELF really runs to exit code 0 on
   some input and commits `pv` (SP1 AIR soundness incl. the SHA-256
   precompile chips, memory argument, syscalls, public-values commitment).
   Upstream: sp1-lean proves per-chip soundness for 25 RV64IM chips; the
   machine theorem has a `sorry`, and precompiles/syscalls/memory init are out
   of scope. Open.
5. **COMPILER** — running the ELF on any input that commits `pv` implies the
   Rust guest (`transfer-core::derive_claim`) returns `pv` on some
   (request, witness) bytes (succinct rustc 1.96.0-dev, sp1-zkvm entrypoint,
   patched sha2 = FIPS SHA-256). Open (no verified compiler / no Lean model
   of the guest).
6. **GUEST** — `derive_claim rq wt = some cb` implies `cb` is in the NEAR
   relation's language. Open as a proof; *tested*: byte-identical to the
   oracle on 1520 in-domain cases, 224 out-of-domain cases refused.
-/

namespace Candidate.Pipeline

open ArenaCore

/-- Opaque parameters describing the SP1 pipeline. -/
structure Sp1Model where
  /-- The deployed verifier as a total function `pub → claim → proof → accept?`. -/
  verify : Verifier
  /-- Program vkey recorded in the public artifacts. -/
  vkeyOf : Bytes → Option Bytes
  /-- SP1 `setup`: program vkey of an ELF. -/
  setup : Bytes → Bytes
  /-- An SP1 execution record satisfying all AIR / bus constraints exists for
  program vkey `vk` with public values `pv`. -/
  Satisfiable : Bytes → Bytes → Prop
  /-- The RISC-V `elf` halts with exit code 0 on `input` having committed `pv`. -/
  Runs : Bytes → Bytes → Bytes → Prop
  /-- Lean-side meaning of the guest: `transfer-core::derive_claim`. -/
  guest : Bytes → Bytes → Option Bytes
  /-- The pinned guest ELF. -/
  elf : Bytes
  /-- The STARK forgery event for an accepted `(pub, claim, proof)`. -/
  Forged : Bytes → Bytes → Bytes → Prop

variable (m : Sp1Model) (pub : Bytes)

/-- (2) STARK + FS + recursion, as a *dichotomy*: acceptance implies a
satisfying execution record for the recorded vkey, or a forgery event.
`Pr[Forged] ≤ ε` is the separate, open, probabilistic obligation. -/
def StarkSoundOrForged : Prop :=
  ∀ cb pb, m.verify pub cb pb = true →
    (∃ vk, m.vkeyOf pub = some vk ∧ m.Satisfiable vk cb) ∨ m.Forged pub cb pb

/-- (3) The vkey in the public artifacts is that of the pinned ELF. -/
def VkeyBinding : Prop := m.vkeyOf pub = some (m.setup m.elf)

/-- (4) SP1 constraint soundness for the pinned ELF. -/
def ConstraintSound : Prop :=
  ∀ pv, m.Satisfiable (m.setup m.elf) pv → ∃ input, m.Runs m.elf input pv

/-- (5) Compilation + zkVM ABI correctness of the guest. -/
def CompilerCorrect : Prop :=
  ∀ input pv, m.Runs m.elf input pv → ∃ rq wt, m.guest rq wt = some pv

/-- (6) The guest refines the NEAR relation (on its committed outputs). -/
def GuestRefines : Prop :=
  ∀ rq wt cb, m.guest rq wt = some cb → nearSpec.InLang cb

/-- Composition (kernel-checked): under (2)–(6), every accepted claim is in
the NEAR relation's language unless a STARK forgery event occurred. With
`Forged := False` this is exactly `ArenaCore.DeterministicSound`. -/
theorem sound_or_forged
    (h2 : StarkSoundOrForged m pub) (h3 : VkeyBinding m pub) (h4 : ConstraintSound m)
    (h5 : CompilerCorrect m) (h6 : GuestRefines m) :
    ∀ cb pb, m.verify pub cb pb = true → nearSpec.InLang cb ∨ m.Forged pub cb pb := by
  intro cb pb hacc
  rcases h2 cb pb hacc with ⟨vk, hvk, hsat⟩ | hf
  · left
    rw [h3] at hvk
    cases hvk
    obtain ⟨input, hrun⟩ := h4 cb hsat
    obtain ⟨rq, wt, hg⟩ := h5 input cb hrun
    exact h6 rq wt cb hg
  · exact Or.inr hf

/-- Sanity: with no forgery event the conclusion is the arena's
`DeterministicSound` (so the composition is not vacuous in shape). -/
theorem deterministic_of_no_forgery
    (hnf : ∀ cb pb, ¬ m.Forged pub cb pb)
    (h2 : StarkSoundOrForged m pub) (h3 : VkeyBinding m pub) (h4 : ConstraintSound m)
    (h5 : CompilerCorrect m) (h6 : GuestRefines m) :
    DeterministicSound nearSpec.InLang m.verify pub := by
  intro cb pb hacc
  rcases sound_or_forged m pub h2 h3 h4 h5 h6 cb pb hacc with h | h
  · exact h
  · exact absurd h (hnf cb pb)

end Candidate.Pipeline
