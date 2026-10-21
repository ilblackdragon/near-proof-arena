import ArenaCore.Security.ROMLemmas

/-!
# Endpoint — the *shape* of the recursive hash endpoint

This file contains no new cryptographic assumption and proves no security
theorem about the deployed recursion. It makes the one missing step of the
recursive composition a *named hypothesis* and machine-checks the surrounding
arithmetic, in the arena's own `PrLE` / `RomSound` vocabulary.

## The statement

`RomSound S L v P pub …` bounds the probability that the deployed verifier
accepts a claim outside `L`, in the lazy random-oracle game of
`ArenaCore.Security.ROM`. For the recursive tail there are two languages:

* `L_air` — membership in the **concrete NV AIR relation**. An accepted trace
  certifies that the concrete inner verifier `V_{i-1}` (with concrete SHA-384
  inside the AIR) accepts. This is what the outer QROM argument can establish.
* `L_rec` — **base truth** (the end-to-end relation the recursion tail claims).

The outer theorem gives `RomSound` at `L_air`. Recursive semantics needs
`RomSound` at `L_rec`. The two differ exactly on

  `romInnerBad` := *the verifier accepts a claim that is in `L_air` but not in `L_rec`*,

that is, on "the concrete inner proof system accepted a false inner statement".
`inner_computational_soundness` decomposes the bad event

  `¬L_rec`  ⊆  `¬L_air`  ∪  (`L_air ∧ ¬L_rec`)

and applies a union bound. Every premise is a named hypothesis:

* `hOuter` — the outer ROM bound at `L_air` (the family-QROM track's target);
* `hInner` — a probability bound for `romInnerBad` **in the same game**, i.e.
  for the same adversary, the same oracle tape and the same verifier run.

`hInner` is *not* implied by collision resistance of SHA-384, by a time cap, or
by literal A-IC. It is a substantive assumption about the concrete inner
system (endpoint (c) of `PROOF.md` §7.2 / paper §7.3). It is strictly weaker
than the pointwise `SemSound`-style inclusion `∀ cb, L_air cb → L_rec cb` that
`Obligations.endToEnd` consumes; the difference is the error term `numI`.

## The range mismatch, stated rather than hidden

`RomSound` fixes `roRange = 2^256` and `LazyRO.answer` returns **32 bytes**.
The PQ stack uses SHA-384 with **42-byte** Merkle digests and 384-bit
transcripts. `RomSoundR` re-parameterises the range explicitly, and
`roRange_mismatch` records the exact gaps (`2^80` for 42-byte digests,
`2^128` for 384-bit ones) plus the fact that the concrete answer function
cannot produce a 42-byte value at all. A bound proved in the `roRange` game is
therefore *not* a bound at the PQ parameters: transporting it is a modelling
decision (`RomSoundR (2^336)` / `RomSoundR (2^384)`), not a theorem.
-/

namespace ArenaCore.Bridge

open ArenaCore
open ArenaCore.Security

set_option exponentiation.threshold 400

/-! ## Union bound for `PrLE` -/

/-- Union bound: bounds on `E` and `F` over the same denominator add. -/
theorem PrLE.or {n R : Nat} {E F : List Nat → Prop} {numE numF den : Nat}
    (hE : PrLE n R E numE den) (hF : PrLE n R F numF den) :
    PrLE n R (fun t => E t ∨ F t) (numE + numF) den := by
  refine ⟨hE.1, ?_⟩
  have hc : count (allTapes n R) (fun t => E t ∨ F t) ≤
      count (allTapes n R) E + count (allTapes n R) F := count_or_le _ _ _
  have h1 : count (allTapes n R) E * den ≤ numE * R ^ n := hE.2
  have h2 : count (allTapes n R) F * den ≤ numF * R ^ n := hF.2
  calc count (allTapes n R) (fun t => E t ∨ F t) * den
      ≤ (count (allTapes n R) E + count (allTapes n R) F) * den :=
        Nat.mul_le_mul_right _ hc
    _ = count (allTapes n R) E * den + count (allTapes n R) F * den := Nat.add_mul _ _ _
    _ ≤ numE * R ^ n + numF * R ^ n := Nat.add_le_add h1 h2
    _ = (numE + numF) * R ^ n := (Nat.add_mul _ _ _).symm

/-- Monotone in the numerator, with the same denominator. -/
theorem PrLE.mono_num {n R : Nat} {E : List Nat → Prop} {num num' den : Nat}
    (h : PrLE n R E num den) (hn : num ≤ num') : PrLE n R E num' den :=
  ⟨h.1, Nat.le_trans h.2 (Nat.mul_le_mul_right _ hn)⟩

/-! ## Exposing the verifier's outcome in the ROM game -/

/-- The claim the adversary's run judges (the verifier's own input claim). -/
noncomputable def romClaim (S : ChallengeSpec) (P : OracleProver S) (pub : Bytes)
    (A : RomAdversary S) (tape : List Nat) : Bytes :=
  (OracleComp.simulate (romImpl S P pub) A (LazyRO.init tape)).1.1

/-- Whether the verifier accepted. -/
noncomputable def romAccepted (S : ChallengeSpec) (v : OracleVerifier) (P : OracleProver S)
    (pub : Bytes) (A : RomAdversary S) (tape : List Nat) : Bool :=
  let r1 := OracleComp.simulate (romImpl S P pub) A (LazyRO.init tape)
  (v.run LazyRO.query r1.2 pub r1.1.1 r1.1.2).1

/-- Whether the simulated oracle overflowed its tape. -/
noncomputable def romOverflow (S : ChallengeSpec) (v : OracleVerifier) (P : OracleProver S)
    (pub : Bytes) (A : RomAdversary S) (tape : List Nat) : Bool :=
  let r1 := OracleComp.simulate (romImpl S P pub) A (LazyRO.init tape)
  (v.run LazyRO.query r1.2 pub r1.1.1 r1.1.2).2.overflow

/-- `romWins` splits into "overflow" and "accepted a claim outside `L`". -/
theorem romWins_iff (S : ChallengeSpec) (L : Bytes → Prop) (v : OracleVerifier)
    (P : OracleProver S) (pub : Bytes) (A : RomAdversary S) (tape : List Nat) :
    romWins S L v P pub A tape ↔
      romOverflow S v P pub A tape = true ∨
        (romAccepted S v P pub A tape = true ∧ ¬ L (romClaim S P pub A tape)) := by
  unfold romWins romOverflow romAccepted romClaim
  rfl

/-- The endpoint's residual event: the concrete inner system accepts a claim
in `L_air` that is not in `L_rec`. -/
noncomputable def romInnerBad (S : ChallengeSpec) (L_air L_rec : Bytes → Prop)
    (v : OracleVerifier) (P : OracleProver S) (pub : Bytes) (A : RomAdversary S)
    (tape : List Nat) : Prop :=
  romAccepted S v P pub A tape = true ∧
    L_air (romClaim S P pub A tape) ∧ ¬ L_rec (romClaim S P pub A tape)

/-- The event inclusion underlying the whole endpoint. -/
theorem romWins_subset (S : ChallengeSpec) (L_air L_rec : Bytes → Prop)
    (v : OracleVerifier) (P : OracleProver S) (pub : Bytes) (A : RomAdversary S)
    (tape : List Nat) :
    romWins S L_rec v P pub A tape →
      romWins S L_air v P pub A tape ∨ romInnerBad S L_air L_rec v P pub A tape := by
  rw [romWins_iff]
  rintro (hov | ⟨hacc, hnrec⟩)
  · exact Or.inl (by rw [romWins_iff]; exact Or.inl hov)
  · by_cases hair : L_air (romClaim S P pub A tape)
    · exact Or.inr ⟨hacc, hair, hnrec⟩
    · exact Or.inl (by rw [romWins_iff]; exact Or.inr ⟨hacc, hair⟩)

/-! ## The conditional endpoint -/

/-- **The recursive endpoint, as a reduction shape.**

Given the outer ROM bound for the *concrete AIR* language and a bound on
`romInnerBad` in the same game, the deployed verifier accepts a claim outside
base truth with probability at most `numOuter + numInner` (over `den`).

Every premise is a hypothesis. In particular `hInner` is endpoint (c): a
computational-soundness statement about the concrete inner system, quantified
over exactly the outer adversary, oracle and verifier run. Nothing here proves
`hInner`, and no theorem elsewhere in this repository implies it. -/
theorem inner_computational_soundness {S : ChallengeSpec} {L_air L_rec : Bytes → Prop}
    {v : OracleVerifier} {P : OracleProver S} {pub : Bytes}
    {qH qP n den numOuter numInner : Nat}
    (hOuter : RomSound S L_air v P pub qH qP n numOuter den)
    (hInner : ∀ A : RomAdversary S,
      OracleComp.QueryBound hashWeight A qH →
      OracleComp.QueryBound proveWeight A qP →
      PrLE n roRange (romInnerBad S L_air L_rec v P pub A) numInner den) :
    RomSound S L_rec v P pub qH qP n (numOuter + numInner) den := by
  intro A hA hP
  refine PrLE.mono (fun t ht => ?_) (PrLE.or (hOuter A hA hP) (hInner A hA hP))
  exact romWins_subset S L_air L_rec v P pub A t ht

/-- If the inner system is *pointwise* sound — every claim in the concrete AIR
language is true — the residual event is empty, so `hInner` holds with
`numInner = 0`. This is the only way the endpoint becomes unconditional, and it
is exactly the `∀ cb, L_air cb → L_rec cb` inclusion that `SemSound` consumes.
It is not obtainable from collision resistance or a runtime cap. -/
theorem inner_bad_empty_of_pointwise {S : ChallengeSpec} {L_air L_rec : Bytes → Prop}
    {v : OracleVerifier} {P : OracleProver S} {pub : Bytes}
    (hpoint : ∀ cb, L_air cb → L_rec cb) {A : RomAdversary S} :
    ∀ t, ¬ romInnerBad S L_air L_rec v P pub A t := by
  rintro t ⟨-, hair, hnrec⟩
  exact hnrec (hpoint _ hair)

/-- The special case in which the inner system is **perfectly** sound on the
whole probability space: `numInner = 0` (the bad event is empty). This is the
`RomSound.mono`-shaped statement, recovered as a corollary so that the two
endpoints differ only in the error term. -/
theorem inner_perfect_soundness {S : ChallengeSpec} {L_air L_rec : Bytes → Prop}
    {v : OracleVerifier} {P : OracleProver S} {pub : Bytes}
    {qH qP n den numOuter : Nat}
    (hOuter : RomSound S L_air v P pub qH qP n numOuter den)
    (hInner : ∀ A : RomAdversary S,
      OracleComp.QueryBound hashWeight A qH →
      OracleComp.QueryBound proveWeight A qP →
      PrLE n roRange (romInnerBad S L_air L_rec v P pub A) 0 den) :
    RomSound S L_rec v P pub qH qP n numOuter den := by
  have h := inner_computational_soundness hOuter hInner
  rw [Nat.add_zero] at h
  exact h

/-! ## The `roRange` / PQ-parameter mismatch -/

/-- The random-oracle game with an explicit answer alphabet. -/
def RomSoundR (R : Nat) (S : ChallengeSpec) (L : Bytes → Prop) (v : OracleVerifier)
    (P : OracleProver S) (pub : Bytes) (qHash qProve tapeLen num den : Nat) : Prop :=
  ∀ A : RomAdversary S,
    OracleComp.QueryBound hashWeight A qHash →
    OracleComp.QueryBound proveWeight A qProve →
    PrLE tapeLen R (romWins S L v P pub A) num den

/-- `RomSound` is `RomSoundR` at the built-in `2^256` alphabet: the deployment
model answers with 256-bit values (32 bytes). -/
theorem romSound_iff_R (S : ChallengeSpec) (L : Bytes → Prop) (v : OracleVerifier)
    (P : OracleProver S) (pub : Bytes) (qH qP n num den : Nat) :
    RomSound S L v P pub qH qP n num den ↔
      RomSoundR roRange S L v P pub qH qP n num den :=
  Iff.rfl

/-- The core's oracle answer is exactly 32 bytes. -/
theorem lazyAnswer_length (t : Nat) : (LazyRO.answer t).length = 32 :=
  Bytes.beN_length 32 t

/-- Hence it can never produce a 42-byte Merkle digest. -/
theorem lazyAnswer_ne_of_length_42 (t : Nat) (y : Bytes) (hy : y.length = 42) :
    LazyRO.answer t ≠ y := by
  intro h
  rw [← h, lazyAnswer_length] at hy
  exact absurd hy (by decide)

/-- The three answer widths: the arena's SHA-256 game, the PQ narrow
(42-byte) digest, and the PQ 384-bit transcript. -/
theorem roRange_mismatch :
    roRange = 2 ^ 256 ∧ 2 ^ 256 < 2 ^ 336 ∧ 2 ^ 336 < 2 ^ 384 := by
  refine ⟨by decide, ?_, ?_⟩
  · exact Nat.pow_lt_pow_right (by decide) (by decide)
  · exact Nat.pow_lt_pow_right (by decide) (by decide)

/-- Quantified gaps: 80 bits to the 42-byte digest space, 128 bits to the
384-bit transcript space. -/
theorem roRange_gaps :
    roRange * 2 ^ 80 = 2 ^ 336 ∧ 2 ^ 336 * 2 ^ 48 = 2 ^ 384 := by
  constructor
  · rw [roRange, ← Nat.pow_add]
  · rw [← Nat.pow_add]

end ArenaCore.Bridge

namespace ArenaCore.Bridge

open ArenaCore
open ArenaCore.Security

/-! ## The multi-pair bridge: the pairs an accepting execution actually uses

`Qrom.OracleBridge` (research package, Mathlib) fixes **one** pair `(m, y)`
before the experiment starts. An accepting execution does not name its pairs in
advance, and the pairs it uses depend on earlier oracle answers. This section
proves the multi-pair version in the arena's own counting model, with the
adaptivity explicit.

Model. A tape is the list of answers to *distinct* fresh inputs. `Demands` reads
the answers consumed so far and either requires the next fresh answer to equal a
specific symbol (`some a`) or requires nothing (`none`). `allMet req t` is "the
sampled oracle agreed with the concrete function on every pair the execution
used".

Result. If the first `ℓ` steps each make a demand, at most `R^{-ℓ}` of the tapes
are consistent, with the demanded symbols allowed to depend on every earlier
answer (`consistency_probability_multi`). `failure_lower_bound_multi` converts
this into the lower bound on inconsistency; at `ℓ = 1`, `R = 2^384` that is
exactly the paper's `1 - δ - 2^-384`.

Two premises are **not** proved here and are not implied by anything in this
repository:

* `hsome` — that each of the first `ℓ` steps really makes a demand on a
  *fresh* coordinate of the oracle (the model: the tape is the answers to
  distinct fresh inputs, and a demand is a specified required symbol). A
  re-query of an already-consumed coordinate adds no new demand, so the bound
  is not weakened by repeats; but if the execution may instead demand whatever
  answer it was given, the consistent event is everything and no bound exists.
  Whether the extracted trace has this shape is a statement about the
  extraction, not about `PrLE`;
* `hacc` — that acceptance of the outer proof requires consistency.

The counting is unconditional; the identification of "what the execution
demanded" with "what the accepting execution requires" is the missing premise,
and it is a modelling decision about the extracted trace, not a theorem.
-/

/-- Readings of "the next fresh answer must be `a`", as a function of the
answers consumed so far. -/
abbrev Demands := List Nat → Option Nat

/-- Every demand made along the execution was met. -/
def allMet (req : Demands) : List Nat → Prop
  | [] => True
  | a :: rest => (req [] = none ∨ req [] = some a) ∧ allMet (fun l => req (a :: l)) rest

theorem allMet_cons (req : Demands) (a : Nat) (rest : List Nat) :
    allMet req (a :: rest) ↔
      (req [] = none ∨ req [] = some a) ∧ allMet (fun l => req (a :: l)) rest :=
  Iff.rfl

theorem sum_map_zero {α : Type} (l : List α) (f : α → Nat) (h : ∀ a ∈ l, f a = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : f a = 0 := h a (List.mem_cons_self)
    have hl : (l.map f).sum = 0 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    rw [List.map_cons, List.sum_cons, ha, hl, Nat.add_zero]

/-- Over a list without repetitions, a sum vanishes off `a₀`. -/
theorem sum_map_le_of_nodup {α : Type} {l : List α} (hl : l.Nodup) (f : α → Nat) (a₀ : α)
    (hz : ∀ a, a ≠ a₀ → f a = 0) : (l.map f).sum ≤ f a₀ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons]
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp hl
    by_cases ha : a = a₀
    · subst ha
      have hzero : ∀ b ∈ l, f b = 0 := fun b hb => hz b fun hb' => hnot (hb' ▸ hb)
      rw [sum_map_zero l f hzero, Nat.add_zero]
      exact Nat.le_refl _
    · rw [hz a ha, Nat.zero_add]
      exact ih hnd

/-- **Multi-pair consistency probability.** If the first `ℓ` steps each demand
a specific answer — adaptively, as a function of every earlier answer — then
`count · R^ℓ ≤ R^n`: at most `R^{-ℓ}` of the tapes are consistent.

At `R = 2^384` this is `2^{-384ℓ}`; at the arena's `roRange = 2^256` the same
statement reads `2^{-256ℓ}`. The alphabet is a parameter here; the mismatch
between those two instantiations is `Bridge.roRange_mismatch`. -/
theorem consistency_probability_multi (R : Nat) :
    ∀ (n ℓ : Nat), ℓ ≤ n → ∀ req : Demands,
      (∀ pre, pre.length < ℓ → (req pre).isSome) →
      count (allTapes n R) (allMet req) * R ^ ℓ ≤ R ^ n := by
  intro n
  induction n with
  | zero =>
    intro ℓ hℓ req _
    have hℓ0 : ℓ = 0 := by omega
    subst hℓ0
    rw [Nat.pow_zero, Nat.mul_one]
    exact Nat.le_trans (count_le_length _ _) (Nat.le_of_eq (allTapes_length 0 R).symm)
  | succ n ih =>
    intro ℓ hℓ req hsome
    rcases Nat.eq_zero_or_pos ℓ with hℓ0 | hℓpos
    · subst hℓ0
      rw [Nat.pow_zero, Nat.mul_one]
      exact Nat.le_trans (count_le_length _ _)
        (Nat.le_of_eq (allTapes_length (n + 1) R))
    · obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
      rw [count_allTapes_succ]
      obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp (hsome [] (Nat.succ_pos j))
      have hterm : ∀ a : Nat, a ≠ a₀ →
          count (allTapes n R) (fun t => allMet req (a :: t)) = 0 := by
        intro a ha
        have h1 : count (allTapes n R) (fun t => allMet req (a :: t)) ≤
            count (allTapes n R) (fun _ => False) :=
          count_mono _ fun t ht => by
            rcases (allMet_cons req a t).mp ht |>.1 with h | h
            · rw [ha₀] at h; exact absurd h.symm (by simp)
            · exact ha (Option.some.inj (h.symm.trans ha₀))
        rw [count_const] at h1
        simpa using h1
      have hshift : count (allTapes n R) (fun t => allMet req (a₀ :: t)) ≤
          count (allTapes n R) (allMet (fun l => req (a₀ :: l))) :=
        count_mono _ fun t ht => (allMet_cons req a₀ t).mp ht |>.2
      have hbound : count (allTapes n R) (fun t => allMet req (a₀ :: t)) * R ^ j ≤ R ^ n := by
        have hmain : count (allTapes n R) (allMet (fun l => req (a₀ :: l))) * R ^ j ≤ R ^ n := by
          refine ih j (by omega) (fun l => req (a₀ :: l)) ?_
          intro pre hlen
          exact hsome (a₀ :: pre) (by simp; omega)
        exact Nat.le_trans (Nat.mul_le_mul_right _ hshift) hmain
      have hsum : ((List.range R).map fun a =>
            count (allTapes n R) (fun t => allMet req (a :: t))).sum ≤
          count (allTapes n R) (fun t => allMet req (a₀ :: t)) :=
        sum_map_le_of_nodup List.nodup_range _ a₀ fun a ha => hterm a ha
      calc ((List.range R).map fun a =>
              count (allTapes n R) (fun t => allMet req (a :: t))).sum * R ^ (j + 1)
          ≤ count (allTapes n R) (fun t => allMet req (a₀ :: t)) * R ^ (j + 1) :=
            Nat.mul_le_mul_right _ hsum
        _ = count (allTapes n R) (fun t => allMet req (a₀ :: t)) * R ^ j * R := by
            rw [Nat.pow_succ, Nat.mul_assoc]
        _ ≤ R ^ n * R := Nat.mul_le_mul_right _ hbound
        _ = R ^ (n + 1) := by rw [Nat.pow_succ]

/-- Splitting an event by an inclusion. -/
theorem count_le_split {n R : Nat} {E C : List Nat → Prop} (_hsub : ∀ t, E t → C t) :
    count (allTapes n R) E ≤
      count (allTapes n R) (fun t => E t ∧ ¬ C t) + count (allTapes n R) C := by
  have h1 : count (allTapes n R) E ≤
      count (allTapes n R) (fun t => (E t ∧ ¬ C t) ∨ C t) :=
    count_mono _ fun t ht => by
      by_cases hc : C t
      · exact Or.inr hc
      · exact Or.inl ⟨ht, hc⟩
  exact Nat.le_trans h1 (count_or_le _ _ _)

/-- **The multi-pair failure bound.** If acceptance requires consistency on the
`ℓ` pairs the execution demands, and `B` tapes are accepting, then at least
`B - R^(n-ℓ)` tapes are inconsistent. Writing `B/R^n ≥ 1 - δ`, the
inconsistency probability is at least `1 - δ - R^{-ℓ}`.

With `ℓ = 1` and `R = 2^384` this is precisely the paper's fixed-pair statement
`1 - δ - 2^-384`; the hypothesis `hsome` is what makes the "pair" fixed by the
execution rather than by the analyst, and that hypothesis is the premise the
paper says is missing. -/
theorem failure_lower_bound_multi (n ℓ R B : Nat) (hR : 0 < R) (hℓ : ℓ ≤ n) (req : Demands)
    (hsome : ∀ pre, pre.length < ℓ → (req pre).isSome)
    (accepted : List Nat → Prop) (hacc : ∀ t, accepted t → allMet req t)
    (hB : B ≤ count (allTapes n R) accepted) :
    B - R ^ (n - ℓ) ≤
      count (allTapes n R) (fun t => accepted t ∧ ¬ allMet req t) := by
  have hsplit := count_le_split (n := n) (R := R) (E := accepted) (C := allMet req) hacc
  have hcons := consistency_probability_multi R n ℓ hℓ req hsome
  have hdec : count (allTapes n R) (allMet req) ≤ R ^ (n - ℓ) := by
    have hp : 0 < R ^ ℓ := Nat.pow_pos hR
    have hdiv : R ^ (n - ℓ) * R ^ ℓ = R ^ n := by
      rw [← Nat.pow_add, Nat.sub_add_cancel hℓ]
    rw [← hdiv] at hcons
    exact Nat.le_of_mul_le_mul_right hcons hp
  omega

/-- **One demanded pair, at `R = 2^384`.** The general bound specialised to the
paper's shape: if acceptance requires consistency on a single demanded pair and
`B` of the `R^n` tapes are accepting, at least `B - R^(n-1)` tapes are
inconsistent. -/
theorem failure_single_pair (n R B : Nat) (hR : 0 < R) (hn : 0 < n) (req : Demands)
    (hsome : ∀ pre, pre.length < 1 → (req pre).isSome)
    (accepted : List Nat → Prop) (hacc : ∀ t, accepted t → allMet req t)
    (hB : B ≤ count (allTapes n R) accepted) :
    B - R ^ (n - 1) ≤
      count (allTapes n R) (fun t => accepted t ∧ ¬ allMet req t) :=
  failure_lower_bound_multi n 1 R B hR hn req hsome accepted hacc hB

end ArenaCore.Bridge

/-! ## Axiom guards -/

#print axioms ArenaCore.Bridge.PrLE.or
#print axioms ArenaCore.Bridge.romWins_iff
#print axioms ArenaCore.Bridge.romWins_subset
#print axioms ArenaCore.Bridge.inner_computational_soundness
#print axioms ArenaCore.Bridge.inner_perfect_soundness
#print axioms ArenaCore.Bridge.romSound_iff_R
#print axioms ArenaCore.Bridge.lazyAnswer_length
#print axioms ArenaCore.Bridge.lazyAnswer_ne_of_length_42
#print axioms ArenaCore.Bridge.roRange_mismatch
#print axioms ArenaCore.Bridge.roRange_gaps
#print axioms ArenaCore.Bridge.consistency_probability_multi
#print axioms ArenaCore.Bridge.failure_lower_bound_multi
#print axioms ArenaCore.Bridge.failure_single_pair
#print axioms ArenaCore.Bridge.inner_bad_empty_of_pointwise
