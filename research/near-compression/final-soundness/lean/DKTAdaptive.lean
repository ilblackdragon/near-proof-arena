import Mathlib

/-!
# Adaptive composition of sequential fold-certificate budgets

The 13 measured `FINAL` transfers in `DKTG2FoldTransfer.lean` are *separate* scalar
statements, each of the shape

  `∀ word, ∃ exceptional, |exceptional| ≤ E ∧ ∀ gamma ∉ exceptional, Good word gamma`

They say nothing about what happens when the challenge of fold `s + 1` is sampled *after*
some earlier fold challenge and after the adversary has seen it. This file supplies that
missing composition step.

## Model

`n` sequential draws from one finite field `F` (the challenge field; for the deployed
verifier this is `Ext12`, `|Ext12| = 2013265921^12`). A *history* is the list of draws so far.
For a history `hist`, `bad hist : Finset F` is the set of values of the next draw deemed bad.
`bad` is **arbitrary** — a function of the whole history — so it may depend on every earlier
draw and on every message absorbed so far. Hence an adversary that chooses the next committed
word after seeing earlier challenges is covered: fix its deterministic strategy before the
run, and read off the certificate's exceptional set for the word it commits to after `hist`.
Because a certificate bounds the exceptional set by the same `E` for *every* word, no
assumption about the adversary is needed beyond `hE`.

## Not modelled

This is a classical finite-sampling lemma. It does not model the Fiat–Shamir/QROM
compilation, does not show that the implemented challenge sampler has this distribution, and
does not assemble the other WHIR moves (OOD, shift queries, `gamma`). Those remain separate
obligations, and no security bound is asserted.

`Qrom.Adaptive.badRuns_probability` in `research/qrom` proves the same shape over `ℕ`
budgets; it is reusable in principle but lives in another track's tree, so this file is
self-contained to avoid editing `research/qrom/**`.
-/

namespace DKTAdaptive

open scoped BigOperators

variable {F : Type} [Fintype F] [DecidableEq F]

/-- `x` prefixed to a length-`n` challenge vector. -/
def prepend {n : ℕ} (x : F) (rest : Fin n → F) : Fin (n + 1) → F := Fin.cons x rest

/-- Challenge vectors of length `n+1` that are bad somewhere along the run: either the first
draw is bad at `hist`, or the remaining `n` draws are bad at the history they actually see. -/
def badRuns (bad : List F → Finset F) (hist : List F) : (n : ℕ) → Finset (Fin n → F)
  | 0 => ∅
  | n + 1 =>
      (((bad hist) ×ˢ (Finset.univ : Finset (Fin n → F))).image
          (fun p => (prepend p.1 p.2 : Fin (n + 1) → F))) ∪
        Finset.univ.biUnion
          (fun x => (badRuns bad (hist ++ [x]) n).image (prepend x))

/-- Every draw is good at the history that precedes it. This is the complement of `badRuns`. -/
def allGood (bad : List F → Finset F) (hist : List F) : (n : ℕ) → (Fin n → F) → Prop
  | 0, _ => True
  | n + 1, x => x 0 ∉ bad hist ∧ allGood bad (hist ++ [x 0]) n (fun j => x j.succ)

/-- Membership in `badRuns` unfolds exactly along the sampling order. -/
theorem cons_mem_badRuns (bad : List F → Finset F) (hist : List F)
    (n : ℕ) (x : F) (rest : Fin n → F) :
    prepend x rest ∈ badRuns bad hist (n + 1) ↔
      x ∈ bad hist ∨ rest ∈ badRuns bad (hist ++ [x]) n := by
  simp [badRuns, prepend, Fin.cons_inj]

/-- `badRuns` is exactly the set of vectors that are not good everywhere. -/
theorem notMem_badRuns_iff_allGood (bad : List F → Finset F) (hist : List F) :
    ∀ (n : ℕ) (x : Fin n → F),
      x ∉ badRuns bad hist n ↔ allGood bad hist n x := by
  intro n
  induction n generalizing hist with
  | zero => intro x; simp [badRuns, allGood]
  | succ n ih =>
    intro x
    rw [show x = prepend (x 0) (fun j => x j.succ) from (Fin.cons_self_tail x).symm]
    rw [cons_mem_badRuns]
    simp only [not_or, allGood, prepend, Fin.cons_zero, Fin.cons_succ]
    rw [ih]

/-- Total budget of `n` consecutive draws starting at history length `start`. -/
def budgetSum (E : ℕ → ℚ) (start : ℕ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => E start + budgetSum E (start + 1) n

@[simp]
theorem budgetSum_zero (E : ℕ → ℚ) (start : ℕ) : budgetSum E start 0 = 0 := rfl

theorem budgetSum_succ (E : ℕ → ℚ) (start n : ℕ) :
    budgetSum E start (n + 1) = E start + budgetSum E (start + 1) n := rfl

/-- Normalized adaptive union bound. Over a uniform challenge vector of length `n`, the
probability that some draw is bad at its own history is at most `(Σ E)/|F|`. -/
theorem badRuns_probability [Nonempty F] (bad : List F → Finset F) (E : ℕ → ℚ)
    (hE : ∀ hist, ((bad hist).card : ℚ) ≤ E hist.length)
    (hist : List F) (n : ℕ) :
    ((badRuns bad hist n).card : ℚ) / (Fintype.card F : ℚ) ^ n ≤
      budgetSum E hist.length n / (Fintype.card F : ℚ) := by
  induction n generalizing hist with
  | zero => simp [badRuns, budgetSum]
  | succ n ih =>
    set N : ℚ := (Fintype.card F : ℚ) with hN
    have hNpos : (0 : ℚ) < N := by
      have : 0 < Fintype.card F := Fintype.card_pos
      rw [hN]; exact_mod_cast this
    -- head: the first draw is bad
    have hhead :
        ((((bad hist) ×ˢ (Finset.univ : Finset (Fin n → F))).image
          (fun p => (prepend p.1 p.2 : Fin (n + 1) → F))).card : ℚ) ≤
          E hist.length * N ^ n := by
      have himg : (((bad hist) ×ˢ (Finset.univ : Finset (Fin n → F))).image
            (fun p => (prepend p.1 p.2 : Fin (n + 1) → F))).card ≤
          ((bad hist) ×ˢ (Finset.univ : Finset (Fin n → F))).card :=
        Finset.card_image_le
      have hprod : (((bad hist) ×ˢ (Finset.univ : Finset (Fin n → F))).card : ℚ) =
          (bad hist).card * N ^ n := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hN]
        push_cast
        ring
      have himg' : ((((bad hist) ×ˢ (Finset.univ : Finset (Fin n → F))).image
            (fun p => (prepend p.1 p.2 : Fin (n + 1) → F))).card : ℚ) ≤
          ((bad hist) ×ˢ (Finset.univ : Finset (Fin n → F))).card := by
        exact_mod_cast himg
      calc _ ≤ (((bad hist) ×ˢ (Finset.univ : Finset (Fin n → F))).card : ℚ) := himg'
        _ = (bad hist).card * N ^ n := hprod
        _ ≤ E hist.length * N ^ n := by
          apply mul_le_mul_of_nonneg_right (hE hist) (by positivity)
    -- tail: charge every possible first value its own continuation budget
    have hterm : ∀ x : F,
        (((badRuns bad (hist ++ [x]) n).image (prepend x)).card : ℚ) ≤
          budgetSum E (hist.length + 1) n / N * N ^ n := by
      intro x
      have himg : (((badRuns bad (hist ++ [x]) n).image (prepend x)).card : ℚ) ≤
          ((badRuns bad (hist ++ [x]) n).card : ℚ) := by
        exact_mod_cast Finset.card_image_le
      refine himg.trans ?_
      have hlen : (hist ++ [x]).length = hist.length + 1 := by simp
      have h := ih (hist ++ [x])
      rw [hlen] at h
      calc ((badRuns bad (hist ++ [x]) n).card : ℚ)
          = ((badRuns bad (hist ++ [x]) n).card : ℚ) / N ^ n * N ^ n := by
            field_simp
        _ ≤ (budgetSum E (hist.length + 1) n / N) * N ^ n := by
            exact mul_le_mul_of_nonneg_right h (by positivity)
        _ = budgetSum E (hist.length + 1) n / N * N ^ n := rfl
    have htail :
        ((Finset.univ.biUnion
          (fun x => (badRuns bad (hist ++ [x]) n).image (prepend x))).card : ℚ) ≤
          budgetSum E (hist.length + 1) n * N ^ n := by
      have hb : ((Finset.univ.biUnion
            (fun x => (badRuns bad (hist ++ [x]) n).image (prepend x))).card : ℚ) ≤
          ∑ x : F, (((badRuns bad (hist ++ [x]) n).image (prepend x)).card : ℚ) := by
        exact_mod_cast Finset.card_biUnion_le
      refine hb.trans ?_
      calc ∑ x : F, (((badRuns bad (hist ++ [x]) n).image (prepend x)).card : ℚ)
          ≤ ∑ _x : F, budgetSum E (hist.length + 1) n / N * N ^ n :=
            Finset.sum_le_sum fun x _ => hterm x
        _ = N * (budgetSum E (hist.length + 1) n / N * N ^ n) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = budgetSum E (hist.length + 1) n * N ^ n := by
            field_simp
    have hunion : ((badRuns bad hist (n + 1)).card : ℚ) ≤
        E hist.length * N ^ n + budgetSum E (hist.length + 1) n * N ^ n := by
      have hc : (((badRuns bad hist (n + 1)).card : ℕ) : ℚ) ≤
          (((((bad hist) ×ˢ (Finset.univ : Finset (Fin n → F))).image
              (fun p => (prepend p.1 p.2 : Fin (n + 1) → F))).card : ℕ) : ℚ) +
            (((Finset.univ.biUnion
              (fun x => (badRuns bad (hist ++ [x]) n).image (prepend x))).card : ℕ) : ℚ) := by
        exact_mod_cast Finset.card_union_le _ _
      linarith
    rw [budgetSum_succ]
    have hden : (0 : ℚ) < N ^ (n + 1) := pow_pos hNpos _
    apply (div_le_div_iff₀ hden hNpos).mpr
    calc ((badRuns bad hist (n + 1)).card : ℚ) * N
        ≤ (E hist.length * N ^ n + budgetSum E (hist.length + 1) n * N ^ n) * N :=
          mul_le_mul_of_nonneg_right hunion hNpos.le
      _ = (E hist.length + budgetSum E (hist.length + 1) n) * N ^ (n + 1) := by
          rw [pow_succ]; ring

/-- Constant-budget form (`k` sequential draws, each exceptional set of size at most `E`). -/
theorem badRuns_probability_const [Nonempty F] (bad : List F → Finset F) (E : ℚ)
    (hE : ∀ hist, ((bad hist).card : ℚ) ≤ E)
    (hist : List F) (n : ℕ) :
    ((badRuns bad hist n).card : ℚ) / (Fintype.card F : ℚ) ^ n ≤
      (n : ℚ) * E / (Fintype.card F : ℚ) := by
  have hE' : ∀ hist : List F, ((bad hist).card : ℚ) ≤ (fun _ : ℕ => E) hist.length := hE
  have h := badRuns_probability bad (fun _ => E) hE' hist n
  have hsum : ∀ (start : ℕ) (n : ℕ), budgetSum (fun _ : ℕ => E) start n = (n : ℚ) * E := by
    intro start n
    induction n generalizing start with
    | zero => simp
    | succ m ih => rw [budgetSum_succ, ih]; push_cast; ring
  rw [hsum] at h
  exact h

/-- Complement form: with probability at least `1 - (Σ E)/|F|` every draw is good at its own
history. The good set is written as the complement of `badRuns`, so no decidability of
`allGood` is needed. This is the statement a WHIR per-round argument consumes. -/
theorem allGood_probability [Nonempty F] (bad : List F → Finset F) (E : ℕ → ℚ)
    (hE : ∀ hist, ((bad hist).card : ℚ) ≤ E hist.length)
    (hist : List F) (n : ℕ) :
    1 - budgetSum E hist.length n / (Fintype.card F : ℚ) ≤
      (((Finset.univ : Finset (Fin n → F)) \ badRuns bad hist n).card : ℚ) /
        (Fintype.card F : ℚ) ^ n := by
  classical
  set N : ℚ := (Fintype.card F : ℚ) with hN
  have hNpos : (0 : ℚ) < N := by
    have : 0 < Fintype.card F := Fintype.card_pos
    rw [hN]; exact_mod_cast this
  have hsub : badRuns bad hist n ⊆ (Finset.univ : Finset (Fin n → F)) :=
    fun x _ => Finset.mem_univ x
  have huniv : ((Fintype.card (Fin n → F) : ℕ) : ℚ) = N ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, hN]
    push_cast
    ring
  have hcard : (((Finset.univ : Finset (Fin n → F)) \ badRuns bad hist n).card : ℚ)
      = N ^ n - ((badRuns bad hist n).card : ℚ) := by
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ,
      Nat.cast_sub (Finset.card_le_univ (badRuns bad hist n)), huniv]
  rw [hcard]
  have hbound := badRuns_probability bad E hE hist n
  have hden : (0 : ℚ) < N ^ n := pow_pos hNpos n
  have hsplit : (N ^ n - ((badRuns bad hist n).card : ℚ)) / N ^ n =
      1 - ((badRuns bad hist n).card : ℚ) / N ^ n := by
    field_simp
  rw [hsplit]
  linarith

/-- The good set is exactly the set of vectors that are good everywhere. -/
theorem mem_sdiff_univ_badRuns_iff [Nonempty F] (bad : List F → Finset F) (hist : List F)
    (n : ℕ) (x : Fin n → F) :
    x ∈ ((Finset.univ : Finset (Fin n → F)) \ badRuns bad hist n) ↔ allGood bad hist n x := by
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact notMem_badRuns_iff_allGood bad hist n x

/-- **Discharging the per-step hypothesis from a certificate family.**

This one needs no finiteness: it is bookkeeping. Suppose at every history `hist` the adversary's
next word `word hist` comes with an exceptional set of size at most `E hist.length` outside which
a predicate `Good hist (word hist) ·` holds. This is exactly the shape of every
`DKTG2FoldTransfer.final_r{r}_s{s}` theorem, which quantifies over *all* words: the adversary's
choice `word hist` (an arbitrary function of the history) is one such word, and the exceptional
set it receives is the one used here.

The conclusion feeds `badRuns_probability`, so no independence or fixed-order assumption is
needed beyond the certificate family itself. -/
theorem badOfWord_bound {F : Type} {W : List F → Type} (word : ∀ hist, W hist)
    (Good : ∀ hist, W hist → F → Prop) (E : ℕ → ℚ)
    (hcert : ∀ hist, ∃ ex : Finset F, ((ex.card : ℚ) ≤ E hist.length) ∧
      ∀ γ ∉ ex, Good hist (word hist) γ) :
    ∃ bad : List F → Finset F, (∀ hist, ((bad hist).card : ℚ) ≤ E hist.length) ∧
      ∀ hist γ, γ ∉ bad hist → Good hist (word hist) γ := by
  classical
  refine ⟨fun hist => (hcert hist).choose, ?_, ?_⟩
  · intro hist; exact (hcert hist).choose_spec.1
  · intro hist γ hγ
    exact (hcert hist).choose_spec.2 γ hγ

end DKTAdaptive
#print axioms DKTAdaptive.notMem_badRuns_iff_allGood
#print axioms DKTAdaptive.badRuns_probability
#print axioms DKTAdaptive.badRuns_probability_const
#print axioms DKTAdaptive.allGood_probability
#print axioms DKTAdaptive.badOfWord_bound
