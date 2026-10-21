import DKTAdaptive
import DKTG2FoldCoverage
import DKTOrderedCoset

/-!
# Round-level adaptive composition for the measured FINAL verifier

`DKTG2FoldCoverage` transfers every O-2 sub-code of every measured FINAL round and of the
PARENT O-2 rounds, but each is a separate scalar statement. `DKTAdaptive` supplies the
adaptive union bound over a *sequence* of uniformly sampled challenges. This file joins the
two at the granularity the verifier actually uses.

## What a round does (pinned `stark-backend-unified`)

For round `i` the verifier runs `k_i` sumcheck folds. In order, for `s = 0 .. k_i - 1`
(`crates/stark-backend/src/verifier/whir.rs:134-152`):

1. absorb `ev1, ev2` (`whir.rs:139-140`);
2. check the folding PoW (`whir.rs:143`);
3. sample `alpha_{i,s}` (`whir.rs:146`);
4. `claim := interpolate_quadratic_at_012 [ev0, ev1, ev2] alpha_{i,s}`.

The fold is checked on sub-code `C^{i,s}` for the *same* `s`, so
`DKTG2FoldCoverage.{role}_r{i}_s{s}` is exactly the per-step contract. Its exceptional set
depends on `alpha_{i,0..s-1}` and on every message absorbed before `alpha_{i,s}`; both are
functions of the earlier challenges once the adversary's strategy is fixed. `DKTAdaptive`
allows exactly that.

`alpha_{i,s}` is `transcript.sample_ext` (`whir.rs:146`). `sample_ext` draws twelve independent
base-field samples (`transcript/traits.rs:29-31`), i.e. a uniform `Ext12` element, so the
per-step budgets divide by `|Ext12| = 2013265921^12`. Here `F` is that challenge field; the
only facts used are `Fintype F` and `Nonempty F`.

## Statement

`roundFold_probability`: `k` subfolds with per-step budgets `E 0 .. E (k-1)` give total bad
probability at most `(Σ_{s<k} E s)/|F|`, with the exceptional sets allowed to depend on the
whole preceding challenge history.

## Scope

A *fold-only* per-round composition in the classical finite-sampling model. It excludes the
OOD, shift-query, `gamma`, μ-batching and query-PoW terms, the FS/QROM compilation, and the
Johnson rounds (which need `DKTGlue`). It is not a security bound.
-/

namespace DKTRoundCompose

/-- The Ext12 challenge-field cardinality for the deployed verifier. -/
def extCard : ℚ := (2013265921 : ℚ) ^ 12

theorem extCard_pos : (0 : ℚ) < extCard := by unfold extCard; positivity

variable {F : Type} [Fintype F] [DecidableEq F]

/-- **Round-level adaptive union.** The round's `k` fold challenges are `k` sequential uniform
draws from `F` (`whir.rs:146`). If the certificate for step `s` bounds its exceptional set by
`E s` for every history, the chance that some step is bad is at most
`budgetSum E · k / |F|`. -/
theorem roundFold_probability [Nonempty F] (k : ℕ) (E : ℕ → ℚ)
    (badAt : ℕ → List F → Finset F)
    (hE : ∀ s hist, ((badAt s hist).card : ℚ) ≤ E s) (hist : List F) :
    ((DKTAdaptive.badRuns (fun h => badAt h.length h) hist k).card : ℚ) /
        (Fintype.card F : ℚ) ^ k ≤
      (DKTAdaptive.budgetSum E hist.length k) / (Fintype.card F : ℚ) :=
  DKTAdaptive.badRuns_probability (fun h => badAt h.length h) E
    (fun h => hE h.length h) hist k

/-- Starting the round at an empty history. -/
theorem roundFold_probability_empty [Nonempty F] (k : ℕ) (E : ℕ → ℚ)
    (badAt : ℕ → List F → Finset F)
    (hE : ∀ s hist, ((badAt s hist).card : ℚ) ≤ E s) :
    ((DKTAdaptive.badRuns (fun h => badAt h.length h) [] k).card : ℚ) /
        (Fintype.card F : ℚ) ^ k ≤
      (DKTAdaptive.budgetSum E 0 k) / (Fintype.card F : ℚ) :=
  roundFold_probability k E badAt hE []

/-- Uniform-budget corollary: `k` subfolds each with budget `E` cost at most `k*E/|F|`. -/
theorem roundFold_probability_uniform [Nonempty F] (k : ℕ) (E : ℚ)
    (badAt : ℕ → List F → Finset F)
    (hE : ∀ s hist, ((badAt s hist).card : ℚ) ≤ E) (hist : List F) :
    ((DKTAdaptive.badRuns (fun h => badAt h.length h) hist k).card : ℚ) /
        (Fintype.card F : ℚ) ^ k ≤ (k : ℚ) * E / (Fintype.card F : ℚ) :=
  DKTAdaptive.badRuns_probability_const (fun h => badAt h.length h) E
    (fun h => hE h.length h) hist k

/-- Complementary form, which is what a verifier soundness argument consumes: with probability
at least `1 - budgetSum E · k / |F|`, no subfold challenge is bad. -/
theorem roundGood_probability [Nonempty F] (k : ℕ) (E : ℕ → ℚ)
    (badAt : ℕ → List F → Finset F)
    (hE : ∀ s hist, ((badAt s hist).card : ℚ) ≤ E s) (hist : List F) :
    1 - (DKTAdaptive.budgetSum E hist.length k) / (Fintype.card F : ℚ) ≤
      (((Finset.univ : Finset (Fin k → F)) \
          DKTAdaptive.badRuns (fun h => badAt h.length h) hist k).card : ℚ) /
        (Fintype.card F : ℚ) ^ k :=
  DKTAdaptive.allGood_probability (fun h => badAt h.length h) E
    (fun h => hE h.length h) hist k

/-- **Discharging the step hypothesis** from a family of scalar fold certificates, which is
exactly the shape of `DKTG2FoldCoverage.{role}_r{i}_s{s}` (they quantify over every word). The
adversary's committed word is an arbitrary function of the challenge history. -/
theorem stepBudgets_of_certificates {W : List F → Type} (word : ∀ hist, W hist)
    (Good : ∀ hist, W hist → F → Prop) (E : ℕ → ℚ)
    (hcert : ∀ hist, ∃ ex : Finset F, ((ex.card : ℚ) ≤ E hist.length) ∧
      ∀ γ ∉ ex, Good hist (word hist) γ) :
    ∃ bad : List F → Finset F, (∀ hist, ((bad hist).card : ℚ) ≤ E hist.length) ∧
      ∀ hist γ, γ ∉ bad hist → Good hist (word hist) γ :=
  DKTAdaptive.badOfWord_bound word Good E hcert

end DKTRoundCompose
#print axioms DKTRoundCompose.roundFold_probability
#print axioms DKTRoundCompose.roundFold_probability_empty
#print axioms DKTRoundCompose.roundFold_probability_uniform
#print axioms DKTRoundCompose.roundGood_probability
#print axioms DKTRoundCompose.stepBudgets_of_certificates
