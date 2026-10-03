import ArenaCore

/-!
# ZkFormal.Potential — the lazy-random-oracle potential lemma

This is the core of the Fiat–Shamir / BCS argument in ArenaCore's ROM game
(`docs/zk-formal/DESIGN.md` §6, lane L2).

A *potential* is a function `Φ : Table → Nat` of the random-oracle query log
(`LazyRO.table`, most recent entry first).  The one-step condition
`StepBound Φ w C` says: answering a *fresh* query `x` with a uniformly random
32-byte value raises the potential, in expectation, by at most `C * w x`
(everything is scaled by `roRange = 2^256` so that it stays in `Nat`).
Repeated queries do not touch the table, so they do not change `Φ`.

`potential_simulate` then says that after running any query tree with
`w`-weighted query budget `q` against the lazy oracle on a uniformly random
tape, the expected final potential is at most `Φ(start) + C * q`.  With
Markov's inequality (`prLE_of_potential`) this bounds the probability of any
event that forces the final potential above a threshold `M`.

Everything game-specific (round-by-round "doomed" sets, Merkle extraction,
the multi-symbol query phase) is encoded in the choice of `Φ`; this file is
generic.  Tape exhaustion is harmless here: an exhausted tape answers with
zeros *without* recording anything in the table.
-/

namespace ZkFormal

open ArenaCore ArenaCore.Security

/-- A random-oracle query log (most recent first), as in `LazyRO.table`. -/
abbrev Table := List (Bytes × Bytes)

/-! ## Sums over all tapes -/

/-- `∑_{t ∈ [0,R)^n} f t`. -/
def tsum (n R : Nat) (f : List Nat → Nat) : Nat := ((allTapes n R).map f).sum

theorem sum_flatMap_cons (n R : Nat) (f : List Nat → Nat) (l : List Nat) :
    ((l.flatMap fun a => (allTapes n R).map (a :: ·)).map f).sum =
      (l.map fun a => tsum n R (fun t => f (a :: t))).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      ih, List.map_map]
    rfl

/-- Summing over tapes through the first symbol. -/
theorem tsum_succ (n R : Nat) (f : List Nat → Nat) :
    tsum (n + 1) R f = ((List.range R).map fun a => tsum n R (fun t => f (a :: t))).sum :=
  sum_flatMap_cons n R f (List.range R)

theorem tsum_zero (R : Nat) (f : List Nat → Nat) : tsum 0 R f = f [] := by
  simp [tsum, allTapes]

theorem sum_map_le {α : Type} (l : List α) (f g : α → Nat) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_mul_right {α : Type} (l : List α) (f : α → Nat) (c : Nat) :
    (l.map fun a => f a * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

theorem tsum_le_of_le (n R : Nat) (f g : List Nat → Nat) (h : ∀ t, f t ≤ g t) :
    tsum n R f ≤ tsum n R g :=
  sum_map_le _ f g fun t _ => h t

theorem tsum_const (n R c : Nat) : tsum n R (fun _ => c) = c * R ^ n := by
  unfold tsum
  rw [Security.sum_map_const, allTapes_length, Nat.mul_comm]

/-! ## The one-step condition and the main lemma -/

/-- Answering a fresh query `x` raises the expected potential by at most
`C * w x` (scaled by `roRange`). -/
def StepBound (Φ : Table → Nat) (w : Bytes → Nat) (C : Nat) : Prop :=
  ∀ (tbl : Table) (x : Bytes), tbl.lookup x = none →
    ((List.range roRange).map fun v => Φ ((x, LazyRO.answer v) :: tbl)).sum ≤
      roRange * (Φ tbl + C * w x)

/-- Potentials compose additively. -/
theorem StepBound.add {Φ₁ Φ₂ : Table → Nat} {w : Bytes → Nat} {C₁ C₂ : Nat}
    (h₁ : StepBound Φ₁ w C₁) (h₂ : StepBound Φ₂ w C₂) :
    StepBound (fun t => Φ₁ t + Φ₂ t) w (C₁ + C₂) := by
  intro tbl x hx
  rw [sum_map_add]
  have := Nat.add_le_add (h₁ tbl x hx) (h₂ tbl x hx)
  refine Nat.le_trans this (Nat.le_of_eq ?_)
  generalize roRange = R
  grind

/-- Potentials can be rescaled (to put several on a common threshold). -/
theorem StepBound.smul {Φ : Table → Nat} {w : Bytes → Nat} {C : Nat} (k : Nat)
    (h : StepBound Φ w C) : StepBound (fun t => k * Φ t) w (k * C) := by
  intro tbl x hx
  have hs := h tbl x hx
  generalize roRange = R at hs ⊢
  have e : ((List.range R).map fun v => k * Φ ((x, LazyRO.answer v) :: tbl)).sum =
      ((List.range R).map fun v => Φ ((x, LazyRO.answer v) :: tbl)).sum * k := by
    rw [← sum_map_mul_right]
    exact congrArg List.sum (List.map_congr_left fun v _ => Nat.mul_comm _ _)
  rw [e]
  have := Nat.mul_le_mul_right k hs
  refine Nat.le_trans this (Nat.le_of_eq ?_)
  grind

/-- The final query log of running `A` from a lazy-oracle state. -/
def finalTable {α : Type} (A : OracleComp hashSpec α) (s : LazyRO) : Table :=
  (OracleComp.simulate hashImpl A s).2.table

/-- **Potential lemma.**  For every query tree `A` with `w`-weighted budget
`q`, every starting log `tbl` and every tape length `n`:
`E_tape[Φ(final log)] ≤ Φ(tbl) + C·q`, in the scaled form
`∑_tapes Φ(final) ≤ (Φ(tbl) + C·q) · R^n`. -/
theorem potential_simulate {Φ : Table → Nat} {w : Bytes → Nat} {C : Nat}
    (hΦ : StepBound Φ w C) {α : Type} {A : OracleComp hashSpec α} {q : Nat}
    (hA : OracleComp.QueryBound w A q) :
    ∀ (n : Nat) (tbl : Table) (b : Bool),
      tsum n roRange (fun t => Φ (finalTable A ⟨t, tbl, b⟩)) ≤ (Φ tbl + C * q) * roRange ^ n := by
  induction hA with
  | pure a q =>
    intro n tbl b
    unfold finalTable
    simp only [OracleComp.simulate]
    rw [tsum_const]
    exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  | query x k q hwq _ ih =>
    intro n tbl b
    -- the budget only shrinks: Φ tbl + C (q - w x) + C w x = Φ tbl + C q
    have hq : C * (q - w x) + C * w x = C * q := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hwq]
    cases hl : tbl.lookup x with
    | some y =>
      -- repeated query: no tape consumed, log unchanged
      have e : ∀ t : List Nat, finalTable (.query x k) ⟨t, tbl, b⟩ = finalTable (k y) ⟨t, tbl, b⟩ := by
        intro t
        simp [finalTable, OracleComp.simulate, hashImpl, LazyRO.query, hl]
      calc tsum n roRange (fun t => Φ (finalTable (.query x k) ⟨t, tbl, b⟩))
          = tsum n roRange (fun t => Φ (finalTable (k y) ⟨t, tbl, b⟩)) := by simp only [e]
        _ ≤ (Φ tbl + C * (q - w x)) * roRange ^ n := ih y n tbl b
        _ ≤ (Φ tbl + C * q) * roRange ^ n := by
          apply Nat.mul_le_mul_right; omega
    | none =>
      cases n with
      | zero =>
        -- tape exhausted: zeros, overflow flag, log unchanged
        simp only [tsum_zero]
        have e : finalTable (.query x k) ⟨[], tbl, b⟩ =
            finalTable (k (List.replicate 32 0)) ⟨[], tbl, true⟩ := by
          simp [finalTable, OracleComp.simulate, hashImpl, LazyRO.query, hl]
        rw [e]
        have := ih (List.replicate 32 0) 0 tbl true
        rw [tsum_zero] at this
        refine Nat.le_trans this ?_
        apply Nat.mul_le_mul_right; omega
      | succ m =>
        rw [tsum_succ]
        have e : ∀ (a : Nat) (t : List Nat), finalTable (.query x k) ⟨a :: t, tbl, b⟩ =
            finalTable (k (LazyRO.answer a)) ⟨t, (x, LazyRO.answer a) :: tbl, b⟩ := by
          intro a t
          simp [finalTable, OracleComp.simulate, hashImpl, LazyRO.query, hl]
        simp only [e]
        -- per first symbol: induction hypothesis on the continuation
        have step : ∀ a ∈ List.range roRange,
            tsum m roRange (fun t => Φ (finalTable (k (LazyRO.answer a)) ⟨t, (x, LazyRO.answer a) :: tbl, b⟩))
              ≤ Φ ((x, LazyRO.answer a) :: tbl) * roRange ^ m + C * (q - w x) * roRange ^ m := by
          intro a _
          have := ih (LazyRO.answer a) m ((x, LazyRO.answer a) :: tbl) b
          rw [Nat.add_mul] at this
          exact this
        refine Nat.le_trans (sum_map_le _ _ _ step) ?_
        rw [sum_map_add, sum_map_mul_right, Security.sum_map_const, List.length_range]
        have hs := hΦ tbl x hl
        have h1 := Nat.mul_le_mul_right (roRange ^ m) hs
        -- assemble: R(Φ + C w) R^m + R C (q - w) R^m = (Φ + C q) R^(m+1)
        calc ((List.range roRange).map fun v => Φ ((x, LazyRO.answer v) :: tbl)).sum * roRange ^ m
              + roRange * (C * (q - w x) * roRange ^ m)
            ≤ roRange * (Φ tbl + C * w x) * roRange ^ m + roRange * (C * (q - w x) * roRange ^ m) :=
              Nat.add_le_add_right h1 _
          _ = (Φ tbl + C * q) * roRange ^ (m + 1) := by
              rw [Nat.pow_succ, ← hq]
              generalize roRange = R
              grind

/-! ## Markov's inequality on tapes -/

theorem count_mul_le_tsum (n R M : Nat) (E : List Nat → Prop) (f : List Nat → Nat)
    (hE : ∀ t ∈ allTapes n R, E t → M ≤ f t) :
    count (allTapes n R) E * M ≤ tsum n R f := by
  classical
  unfold tsum
  rw [← sum_map_ite]
  apply sum_map_le
  intro t ht
  by_cases h : E t
  · simp only [h, ite_true]; exact hE t ht h
  · simp [h]

/-- If an event forces the final potential to be at least `M > 0`, its
probability is at most `(Φ(start) + C·q) / M`. -/
theorem prLE_of_potential {Φ : Table → Nat} {w : Bytes → Nat} {C : Nat}
    (hΦ : StepBound Φ w C) {α : Type} {A : OracleComp hashSpec α} {q : Nat}
    (hA : OracleComp.QueryBound w A q) (n : Nat) (tbl : Table) (b : Bool)
    (E : List Nat → Prop) (M : Nat) (hM : 0 < M)
    (hE : ∀ t, t.length = n → E t → M ≤ Φ (finalTable A ⟨t, tbl, b⟩)) :
    PrLE n roRange E (Φ tbl + C * q) M := by
  refine ⟨hM, ?_⟩
  have h1 := count_mul_le_tsum n roRange M E (fun t => Φ (finalTable A ⟨t, tbl, b⟩))
    (fun t ht hEt => hE t (mem_allTapes_length ht) hEt)
  exact Nat.le_trans h1 (potential_simulate hΦ hA n tbl b)

end ZkFormal
