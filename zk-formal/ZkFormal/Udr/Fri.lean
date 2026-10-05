import ZkFormal.Udr.Statements

/-!
# ZkFormal.Udr.Fri — the FRI pass-set argument (`FriStmt`)

Unique-decoding FRI query-phase soundness with binary folds and roll-ins.
Going down from the final layer `r`, the pass set `P_i` of layer `i` is the
preimage of `Q_{i+1} = {j' ∈ P_{i+1} : f (i+1) j' = rollW i j'}` under
`j ↦ j % nn (i+1)`, so `|P_i| = 2 |Q_{i+1}|` and the count hypothesis
propagates upward (`e i ≤ 2 e (i+1)`).  At each layer the strong line lemma
for `γ` (roll-in) and then for `β` (fold) turns the codeword of layer `i+1`
into codewords `A0, A1` for the even and odd parts on `Q_{i+1}`, and
`A0(X²) + X·A1(X²)` (coefficients interleaved, `ilv`) matches `f i` on `P_i`.
-/

namespace ZkFormal.Udr

open ArenaCore.Security
open Lean.Grind

set_option linter.unusedSectionVars false

theorem count_congr_mem {α : Type} (l : List α) {E F : α → Prop} (h : ∀ x ∈ l, E x ↔ F x) :
    count l E = count l F :=
  Nat.le_antisymm (count_mono_mem l fun x hx => (h x hx).1)
    (count_mono_mem l fun x hx => (h x hx).2)

/-- The preimage of a set under `j ↦ j % m` on `[0, 2m)` has twice its size. -/
theorem count_range_mod (m : Nat) (A : Nat → Prop) :
    count (List.range (2 * m)) (fun j => A (j % m)) = 2 * count (List.range m) A := by
  rw [show 2 * m = m + m by omega, List.range_add, count_append, count_map]
  have h1 : count (List.range m) (fun j => A (j % m)) = count (List.range m) A :=
    count_congr_mem _ fun x hx => by rw [Nat.mod_eq_of_lt (List.mem_range.mp hx)]
  have h2 : count (List.range m) (fun j => A ((m + j) % m)) = count (List.range m) A :=
    count_congr_mem _ fun x hx => by
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (List.mem_range.mp hx)]
  omega

/-- Agreement on `A` bounds the distance by the size of the complement. -/
theorem dist_add_count_le {K : Type} [Field K] {ι : Type} {n : Nat} {u v : Word ι K}
    (A : Nat → Prop) (h : ∀ i, i < n → A i → u i = v i) :
    dist n u v + count (List.range n) A ≤ n := by
  have hc := count_add_count_not (List.range n) A
  rw [List.length_range] at hc
  have : dist n u v ≤ count (List.range n) (fun i => ¬ A i) :=
    count_mono_mem _ fun i hi hne hA => hne (h i (List.mem_range.mp hi) hA)
  omega

/-- Interleaved coefficients: `ilv a b (2k) = a k`, `ilv a b (2k+1) = b k`. -/
def ilv {K : Type} (a b : Nat → K) (n : Nat) : K := if n % 2 = 0 then a (n / 2) else b (n / 2)

theorem ilv_shift {K : Type} (a b : Nat → K) :
    (fun k => ilv a b (k + 1 + 1)) = ilv (fun k => a (k + 1)) (fun k => b (k + 1)) := by
  funext k
  simp only [ilv]
  rw [show k + 1 + 1 = k + 2 * 1 by omega, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by omega)]

/-- `ev (2m) (ilv a b) x = a(x²) + x·b(x²)`. -/
theorem ev_ilv {K : Type} [Field K] (m : Nat) (a b : Nat → K) (x : K) :
    ev (2 * m) (ilv a b) x = ev m a (x * x) + x * ev m b (x * x) := by
  induction m generalizing a b with
  | zero => simp only [Nat.mul_zero, ev_zero]; grind
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, ev_succ, ev_succ, ev_succ m a, ev_succ m b]
    have e := ilv_shift a b
    rw [e, ih]
    have h0 : ilv a b 0 = a 0 := rfl
    have h1 : ilv a b (0 + 1) = b 0 := rfl
    rw [h0, h1]
    grind

namespace Fri

variable {K : Type} [Field K]

theorem passK_succ (S : Setup K) (R : Run K) {k i : Nat} (hik : i + (k + 1) = S.r) (j : Nat) :
    passK S R (k + 1) j ↔ (R.f (i + 1) (j % S.nn (i + 1)) = rollW S R i (j % S.nn (i + 1)) ∧
      passK S R k (j % S.nn (i + 1))) := by
  have h1 : S.r - k = i + 1 := by omega
  have h0 : S.r - (k + 1) = i := by omega
  rw [passK, h1, h0]

/-- The roll-in word `G i` is `e (i+1)`-close to the layer-`(i+1)` RS code. -/
def RollClose (S : Setup K) (R : Run K) (e : Nat → Nat) (i : Nat) : Prop :=
  ∃ q : Nat → K,
    count (List.range (S.nn (i + 1))) (fun j => R.G i j () ≠ ev (S.DD (i + 1)) q (S.xs (i + 1) j))
      ≤ e (i + 1)

/-- The layer-by-layer pass-set argument, layer `i = r - k`; also every
roll-in word from layer `i` upward is close to its code. -/
theorem fri_layer (S : Setup K) (R : Run K) (e : Nat → Nat)
    (he : ∀ i, i < S.r → e i ≤ 2 * e (i + 1)) (hgood : GoodChallenges S R e) :
    ∀ k i, i + k = S.r → S.nn i - e i ≤ count (List.range (S.nn i)) (passK S R k) →
      (∃ p : Nat → K, ∀ j, j < S.nn i → passK S R k j →
        R.f i j () = ev (S.DD i) p (S.xs i j)) ∧
      ∀ i', i ≤ i' → i' < S.r → RollClose S R e i' := by
  intro k
  induction k with
  | zero =>
    intro i hi _
    rw [show i = S.r by omega]
    exact ⟨⟨R.pr, fun j _ hj => hj⟩, fun i' h1 h2 => absurd h2 (by omega)⟩
  | succ k ih =>
    intro i hik hcnt
    have hir : i < S.r := by omega
    have hnn := S.hnn i hir
    have hDD := S.hDD i hir
    let A : Nat → Prop := fun j' => R.f (i + 1) j' = rollW S R i j' ∧ passK S R k j'
    have hP : ∀ j, passK S R (k + 1) j ↔ A (j % S.nn (i + 1)) := passK_succ S R (by omega)
    have hcA : S.nn i - e i ≤ 2 * count (List.range (S.nn (i + 1))) A := by
      rw [← count_range_mod, ← hnn]
      exact Nat.le_trans hcnt (Nat.le_of_eq (count_congr_mem _ fun j _ => hP j))
    have hei := he i hir
    have hAle : S.nn (i + 1) - e (i + 1) ≤ count (List.range (S.nn (i + 1))) A := by omega
    obtain ⟨⟨q, hq⟩, hup⟩ := ih (i + 1) (by omega)
      (Nat.le_trans hAle (count_mono _ fun j h => h.2))
    let c : Word Unit K := fun j _ => ev (S.DD (i + 1)) q (S.xs (i + 1) j)
    have hc : (S.code (i + 1) hir).mem c := ⟨q, fun j _ => rfl⟩
    have hdA : ∀ u v : Word Unit K, (∀ j, j < S.nn (i + 1) → A j → u j = v j) →
        dist (S.nn (i + 1)) u v ≤ e (i + 1) := by
      intro u v h
      have := dist_add_count_le A h
      omega
    have hroll : ∀ j, j < S.nn (i + 1) → A j → rollW S R i j = c j := by
      intro j hj hA
      rw [← hA.1]
      funext u; cases u; exact hq j hj hA.2
    obtain ⟨v0, v1, hv0, hv1, hS1⟩ := (hgood i hir).2 c hc (hdA _ _ hroll)
    have hrollI : RollClose S R e i := by
      obtain ⟨Q1, hQ1⟩ := hv1
      refine ⟨Q1, Nat.le_trans (count_mono_mem _ (F := fun j => R.G i j ≠ v1 j) fun j hj hne heq => hne ?_)
        (hdA (R.G i) v1 fun j hj hA => (hS1 j hj (hroll j hj hA)).2)⟩
      rw [← hQ1 j (List.mem_range.mp hj), heq]
    refine ⟨?_, fun i' h1 h2 => ?_⟩
    rotate_left
    · by_cases hii : i' = i
      · exact hii ▸ hrollI
      · exact hup i' (by omega) h2
    have hfold : ∀ j, j < S.nn (i + 1) → A j → foldW S R i j = v0 j :=
      fun j hj hA => (hS1 j hj (hroll j hj hA)).1
    obtain ⟨a0, a1, ha0, ha1, hS2⟩ := (hgood i hir).1 v0 hv0 (hdA _ _ hfold)
    obtain ⟨P0, hP0⟩ := ha0
    obtain ⟨P1, hP1⟩ := ha1
    refine ⟨ilv P0 P1, fun j hj hpj => ?_⟩
    have hA := (hP j).1 hpj
    have hm : 0 < S.nn (i + 1) := by omega
    -- the even/odd identities at `j' = j % nn (i+1)`
    have key : ∀ j', j' < S.nn (i + 1) → A j' →
        R.f i j' () = ev (S.DD (i + 1)) P0 (S.xs i j' * S.xs i j') +
            S.xs i j' * ev (S.DD (i + 1)) P1 (S.xs i j' * S.xs i j') ∧
        R.f i (j' + S.nn (i + 1)) () = ev (S.DD (i + 1)) P0 (S.xs i j' * S.xs i j') -
            S.xs i j' * ev (S.DD (i + 1)) P1 (S.xs i j' * S.xs i j') := by
      intro j' hj' hA'
      have h2 := hS2 j' hj' (hfold j' hj' hA')
      have hE := congrFun h2.1 ()
      have hO := congrFun h2.2 ()
      rw [hP0 j' hj'] at hE
      rw [hP1 j' hj'] at hO
      simp only [evenW, oddW] at hE hO
      rw [S.hsq i j' hir hj'] at hE hO
      have hx := S.hnz i j' (Nat.le_of_lt hir) (by omega)
      have h2x : (2 : K) * S.xs i j' ≠ 0 := by
        intro h0
        have := Field.mul_inv_cancel S.htwo
        apply hx
        have : (2 : K)⁻¹ * (2 * S.xs i j') = 0 := by rw [h0]; grind
        grind
      have i1 := Field.mul_inv_cancel S.htwo
      have i2 := Field.mul_inv_cancel h2x
      constructor <;> grind
    by_cases hlt : j < S.nn (i + 1)
    · rw [Nat.mod_eq_of_lt hlt] at hA
      rw [hDD, ev_ilv, (key j hlt hA).1]
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + S.nn (i + 1) := ⟨j - S.nn (i + 1), by omega⟩
      have hj' : j' < S.nn (i + 1) := by omega
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hj'] at hA
      rw [hDD, ev_ilv, (key j' hj' hA).2, S.hneg i j' hir hj']
      have : -S.xs i j' * -S.xs i j' = S.xs i j' * S.xs i j' := by grind
      rw [this]
      grind

end Fri

/-- **FRI pass-set argument** (unique decoding, no weights). -/
theorem fri : FriStmt := by
  intro K _ S R e he hgood hcnt
  exact (Fri.fri_layer S R e he hgood S.r 0 (Nat.zero_add _) hcnt).1

/-- **FRI roll-in closeness**: every roll-in word `G i` (`i < r`) is
`e (i+1)`-close to the layer-`(i+1)` code. -/
theorem friRoll : FriRollStmt := by
  intro K _ S R e he hgood hcnt i hi
  exact (Fri.fri_layer S R e he hgood S.r 0 (Nat.zero_add _) hcnt).2 i (Nat.zero_le _) hi

end ZkFormal.Udr
