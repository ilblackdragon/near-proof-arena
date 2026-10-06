import ZkFormal.Udr.Main
import ZkFormal.Udr.GrandProduct

/-!
# R2 PoC: the new algebra of one native-accumulation step

`docs/research/recursion-r2-theorem.md` §3. One accumulation step of the unique-decoding-regime
scheme ("UDR-Arc") keeps the accumulator relation

  `RAcc a T y` : `a` is `e`-close to an `RS[xs, n, D]` codeword `p` with `p(xs i) = y i` for `i ∈ T`.

The decider checks low degree of the **degree-corrected quotient** of `a` by the claims. The quotient
is `(a − ans)/V_T` with prover-chosen fill values on `T`, and the shifts `x^c · Quot` for `c ≤ |T|`.
`acc_close` is the closeness transfer: if that word is `e`-close to the interleaved RS code, then
`a` satisfies `RAcc` at radius `e + |T|`, whatever the fill values are. `spot_doom` and
`spot_escape` are the two facts the per-step spot checks use.

Everything is kernel-checked against zk-formal's Udr layer (imported read-only), with no Mathlib
and no `sorry`. `#print axioms` on every theorem here: propext, Classical.choice, Quot.sound.
-/

namespace RecursionPoc
open ZkFormal.Udr ArenaCore.Security Lean.Grind

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

/-- Accumulator relation `R_acc` at radius `e`. -/
def RAcc (xs : Nat → K) (n D e : Nat) (a : Word Unit K) (T : List Nat) (y : Nat → K) : Prop :=
  ∃ p : Nat → K, dist n a (fun i _ => ev D p (xs i)) ≤ e ∧ ∀ i ∈ T, ev D p (xs i) = y i

/-- Quotient of `a` by the claims (interpolant `ans`, vanishing polynomial of `T`), with
prover-supplied fill values on the claimed positions. -/
def quotW (xs : Nat → K) (T : List Nat) (ans : K → K) (fill : Nat → K) (a : Word Unit K) :
    Word Unit K :=
  fun i _ => if i ∈ T then fill i else (a i () - ans (xs i)) * (gpP (T.map xs) (xs i))⁻¹

/-- Degree-correction word: column `c ≤ t` is `x^c · Q(x)`; the other columns are zero. -/
def shiftW (xs : Nat → K) (t : Nat) (Q : Word Unit K) : Word Nat K :=
  fun i c => if c ≤ t then xs i ^ c * Q i () else 0

/-! ## Small lemmas -/

/-- Coefficients of `x^t · p`. -/
def shiftC (t : Nat) (c : Nat → K) : Nat → K := fun k => if k < t then 0 else c (k - t)

theorem ev_shiftC (m : Nat) (c : Nat → K) (x : K) :
    ∀ t, ev (m + t) (shiftC t c) x = x ^ t * ev m c x
  | 0 => by
    have : shiftC 0 c = c := by funext k; simp [shiftC]
    rw [this, Nat.add_zero]; grind
  | t + 1 => by
    rw [show m + (t + 1) = (m + t) + 1 by omega, ev_succ]
    have h0 : shiftC (t + 1) c 0 = 0 := by simp [shiftC]
    have h1 : (fun k => shiftC (t + 1) c (k + 1)) = shiftC t c := by
      funext k
      simp only [shiftC]
      by_cases hk : k < t
      · simp [hk]
      · simp only [show ¬ k + 1 < t + 1 by omega, hk, ite_false]
        congr 1; omega
    rw [h0, h1, ev_shiftC m c x t]
    grind

/-- The positions in a duplicate-free `T`, counted over `[0, n)`, are at most `|T|`. -/
theorem count_mem_le (n : Nat) (T : List Nat) :
    count (List.range n) (fun i => i ∈ T) ≤ T.length := by
  have h1 : count (List.range n) (fun i => i ∈ T) ≤
      count (List.range n) (fun a => ∃ j ∈ T, a = j) :=
    count_mono _ fun a ha => ⟨a, ha, rfl⟩
  have h2 : count (List.range n) (fun a => ∃ j ∈ T, a = j) ≤
      (T.map fun j => count (List.range n) (fun a => a = j)).sum :=
    count_exists_mem_le (List.range n) T (fun j a => a = j)
  have h3 : (T.map fun j => count (List.range n) (fun a => a = j)).sum ≤ T.length * 1 :=
    sum_le_length_mul T (fun j => count (List.range n) (fun a => a = j)) 1
      (fun j _ => count_le_one_of_unique List.nodup_range _ fun a b ha hb => ha.trans hb.symm)
  omega

/-- A product of nonzero factors is nonzero. -/
theorem prod_ne_zero : ∀ (l : List K), (∀ y ∈ l, y ≠ 0) → l.prod ≠ 0
  | [], _ => by simp only [List.prod_nil]; exact fun h => Field.zero_ne_one h.symm
  | a :: l, h => by
    rw [List.prod_cons]
    intro hp
    rcases gp_mul_eq_zero hp with ha | hl
    · exact h a (List.mem_cons_self ..) ha
    · exact prod_ne_zero l (fun y hy => h y (List.mem_cons_of_mem _ hy)) hl

/-- The vanishing polynomial of `T` is nonzero off `T` (distinct points). -/
theorem gpP_ne_zero (xs : Nat → K) (n : Nat) (hxs : Distinct xs n) (T : List Nat)
    (hTn : ∀ i ∈ T, i < n) (i : Nat) (hi : i < n) (hiT : i ∉ T) : gpP (T.map xs) (xs i) ≠ 0 := by
  unfold gpP
  apply prod_ne_zero
  intro y hy
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
  intro h0
  have : xs i = xs j := by grind
  exact hiT (hxs i j hi (hTn j hj) this ▸ hj)

/-- The vanishing polynomial of `T` is zero on `T`. -/
theorem gpP_root (xs : Nat → K) (T : List Nat) (i : Nat) (hi : i ∈ T) : gpP (T.map xs) (xs i) = 0 := by
  induction T with
  | nil => exact absurd hi List.not_mem_nil
  | cons j T ih =>
    rw [List.map_cons, gpP_cons]
    rcases List.mem_cons.mp hi with rfl | h
    · grind
    · rw [ih h]; grind

/-! ## (i) Degree correction by shifts -/

theorem shift_close (xs : Nat → K) (n D t e : Nat) (hD : D ≤ n) (hxs : Distinct xs n)
    (htD : t ≤ D) (hn : e + D + t ≤ n) (Q : Word Unit K)
    (h : Good (rsInterleaved xs n D hD hxs Nat) e (shiftW xs t Q) (fun _ _ => 0) 0) :
    ∃ q : Nat → K, dist n Q (fun i _ => ev (D - t) q (xs i)) ≤ e := by
  classical
  obtain ⟨w, hw, hdist⟩ := h
  -- column polynomials of the interleaved codeword
  have hcol : ∀ c, ∃ p : Nat → K, ∀ i, i < n → w i c = ev D p (xs i) := fun c => by
    obtain ⟨p, hp⟩ := hw c
    exact ⟨p, fun i hi => hp i hi⟩
  obtain ⟨p0, hp0⟩ := hcol 0
  obtain ⟨pt, hpt⟩ := hcol t
  -- agreement set
  let A : Nat → Prop := fun i => line (shiftW xs t Q) (fun _ _ => 0) 0 i = w i
  have hcnt := count_add_count_not (List.range n) A
  rw [List.length_range] at hcnt
  have hdA : count (List.range n) (fun i => ¬ A i) ≤ e := hdist
  have hA0 : ∀ i, i < n → A i → Q i () = ev D p0 (xs i) := fun i hi hA => by
    have := congrFun hA 0
    simp only [line, shiftW, Nat.zero_le, ite_true] at this
    rw [← hp0 i hi, ← this]; grind
  have hAt : ∀ i, i < n → A i → xs i ^ t * Q i () = ev D pt (xs i) := fun i hi hA => by
    have := congrFun hA t
    simp only [line, shiftW, Nat.le_refl, ite_true] at this
    rw [← hpt i hi, ← this]; grind
  -- x^t · p0 = pt on ≥ D + t distinct points, hence as coefficient vectors of length D + t
  let ptc : Nat → K := fun k => if k < D then pt k else 0
  have hptc : ∀ x, ev (D + t) ptc x = ev D pt x := fun x => by
    rw [ev_pad (Nat.le_add_right D t) (fun k h1 _ => by simp [ptc, show ¬ k < D by omega])]
    exact ev_congr (fun k hk => by simp [ptc, hk]) x
  let dc : Nat → K := fun k => shiftC t p0 k - ptc k
  obtain ⟨l, hlen, hmem, hnd⟩ := filter_props (List.range n) A
  have hlt : ∀ i ∈ l, i < n := fun i hi => List.mem_range.mp (hmem i hi).1
  have hroots : ∀ k, k < D + t → dc k = 0 :=
    coeffs_zero_of_roots (D + t) dc (l.map xs) (hxs.map_nodup (hnd List.nodup_range) hlt)
      (by rw [List.length_map]; omega)
      (fun r hr => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
        show ev (D + t) (fun k => shiftC t p0 k - ptc k) (xs i) = 0
        rw [ev_sub, ev_shiftC, hptc, ← hA0 i (hlt i hi) (hmem i hi).2,
          ← hAt i (hlt i hi) (hmem i hi).2]
        grind)
  -- the top `t` coefficients of p0 vanish
  have htop : ∀ k, D - t ≤ k → k < D → p0 k = 0 := fun k h1 h2 => by
    have := hroots (k + t) (by omega)
    simp only [dc, shiftC, ptc, show ¬ k + t < t by omega, show ¬ k + t < D by omega,
      ite_false, Nat.add_sub_cancel] at this
    grind
  refine ⟨p0, Nat.le_trans (dist_mono fun i hi hne hA => hne ?_) hdA⟩
  funext u; cases u
  rw [hA0 i hi hA, ev_pad (Nat.sub_le D t) htop]

/-! ## (ii) Quotient with in-domain claims and arbitrary fill -/

theorem quot_close (xs : Nat → K) (n D e : Nat) (hxs : Distinct xs n) (T : List Nat)
    (hT : T.Nodup) (hTn : ∀ i ∈ T, i < n) (htD : T.length ≤ D)
    (ans : Nat → K) (y : Nat → K) (hans : ∀ i ∈ T, ev T.length ans (xs i) = y i)
    (fill : Nat → K) (a : Word Unit K) (q : Nat → K)
    (hq : dist n (quotW xs T (ev T.length ans) fill a) (fun i _ => ev (D - T.length) q (xs i)) ≤ e) :
    RAcc xs n D (e + T.length) a T y := by
  classical
  let t := T.length
  let V : K → K := gpP (T.map xs)
  -- p := ans + V · q has length D
  have hpoly : IsPoly D (fun x => ev t ans x + V x * ev (D - t) q x) := by
    have hans' : IsPoly D (ev t ans) := (IsPoly.of_ev t ans).mono htD
    by_cases hDt : D - t = 0
    · have : (fun x => ev t ans x + V x * ev (D - t) q x) = ev t ans := by
        funext x; rw [hDt, ev_zero]; grind
      rw [this]; exact hans'
    · obtain ⟨b, hb⟩ : ∃ b, D - t = b + 1 := ⟨D - t - 1, by omega⟩
      have hV : IsPoly (t + 1) V := by
        have := gpP_isPoly (T.map xs); rwa [List.length_map] at this
      have hqp : IsPoly (b + 1) (ev (D - t) q) := hb ▸ IsPoly.of_ev _ q
      have hm := IsPoly.mul hV hqp
      rw [show t + b + 1 = D by omega] at hm
      exact hans'.add hm
  obtain ⟨p, hp⟩ := hpoly
  refine ⟨p, ?_, fun i hi => ?_⟩
  · -- a ≠ p only on T or where the quotient disagrees with q
    have hle : dist n a (fun i _ => ev D p (xs i)) ≤
        count (List.range n) (fun i => quotW xs T (ev t ans) fill a i ≠
            (fun i (_ : Unit) => ev (D - t) q (xs i)) i ∨ i ∈ T) := by
      refine count_mono_mem _ fun i hi hne => ?_
      have hi' := List.mem_range.mp hi
      by_cases hiT : i ∈ T
      · exact Or.inr hiT
      · refine Or.inl fun heq => hne ?_
        have hq1 := congrFun heq ()
        simp only [quotW, hiT, ite_false] at hq1
        have hV0 : V (xs i) ≠ 0 := gpP_ne_zero xs n hxs T hTn i hi' hiT
        funext u; cases u
        show a i () = ev D p (xs i)
        rw [← hp (xs i)]
        have hinv : V (xs i) * (V (xs i))⁻¹ = 1 := Field.mul_inv_cancel hV0
        have : a i () - ev t ans (xs i) = V (xs i) * ev (D - t) q (xs i) := by
          rw [← hq1]
          calc a i () - ev t ans (xs i)
              = (a i () - ev t ans (xs i)) * (V (xs i) * (V (xs i))⁻¹) := by rw [hinv]; grind
            _ = V (xs i) * ((a i () - ev t ans (xs i)) * (V (xs i))⁻¹) := by grind
        grind
    have hor := count_or_le (List.range n)
      (fun i => quotW xs T (ev t ans) fill a i ≠ (fun i (_ : Unit) => ev (D - t) q (xs i)) i)
      (fun i => i ∈ T)
    have hmem := count_mem_le n T
    have hq' : count (List.range n)
        (fun i => quotW xs T (ev t ans) fill a i ≠ (fun i (_ : Unit) => ev (D - t) q (xs i)) i) ≤ e := hq
    omega
  · -- on T: V vanishes, so p = ans = y
    rw [← hp (xs i)]
    show ev t ans (xs i) + gpP (T.map xs) (xs i) * ev (D - t) q (xs i) = y i
    rw [gpP_root xs T i hi, hans i hi]; grind

/-! ## The PoC core lemma -/

/-- **Closeness transfer through one accumulation step.** If the degree-corrected quotient word
of `(a, T)` is `e`-close to the interleaved RS code, then `a` satisfies the accumulator relation at
radius `e + |T|`, for every choice of fill values. -/
theorem acc_close (xs : Nat → K) (n D e : Nat) (hD : D ≤ n) (hxs : Distinct xs n)
    (T : List Nat) (hT : T.Nodup) (hTn : ∀ i ∈ T, i < n) (htD : T.length ≤ D)
    (hn : e + D + T.length ≤ n)
    (ans : Nat → K) (y : Nat → K) (hans : ∀ i ∈ T, ev T.length ans (xs i) = y i)
    (fill : Nat → K) (a : Word Unit K)
    (hW : Good (rsInterleaved xs n D hD hxs Nat) e
      (shiftW xs T.length (quotW xs T (ev T.length ans) fill a)) (fun _ _ => 0) 0) :
    RAcc xs n D (e + T.length) a T y := by
  obtain ⟨q, hq⟩ := shift_close xs n D T.length e hD hxs htD hn _ hW
  exact quot_close xs n D e hxs T hT hTn htD ans y hans fill a q hq

/-! ## (iii) Spot checks -/

/-- If `a` decodes to `p` (unique decoding) and a claimed position disagrees with `p`, the new
accumulator relation is false. -/
theorem spot_doom (xs : Nat → K) (n D e : Nat) (hD : D ≤ n) (hxs : Distinct xs n)
    (he : 2 * e < n - D + 1) (h a : Word Unit K) (p : Nat → K)
    (hp : dist n a (fun i _ => ev D p (xs i)) ≤ e) (X : List Nat) (hX : ∀ i ∈ X, i < n)
    (hbad : ∃ i ∈ X, ev D p (xs i) ≠ h i ()) :
    ¬ RAcc xs n D e a X (fun i => h i ()) := by
  rintro ⟨p', hp', hcl⟩
  obtain ⟨i, hiX, hne⟩ := hbad
  have hu := LinCode.unique (rsCode xs n D hD hxs) he
    (w := fun i _ => ev D p (xs i)) (w' := fun i _ => ev D p' (xs i))
    ⟨p, fun _ _ => rfl⟩ ⟨p', fun _ _ => rfl⟩ hp hp' i (hX i hiX)
  exact hne ((congrFun hu ()).trans (hcl i hiX))

/-- A codeword agrees with an `e'`-far word on at most `n − e' − 1` positions: the escape count of
one spot-check position. -/
theorem spot_escape (xs : Nat → K) (n D e' : Nat) (h : Word Unit K)
    (hfar : ∀ p : Nat → K, e' < dist n h (fun i _ => ev D p (xs i))) (p : Nat → K) :
    count (List.range n) (fun i => ev D p (xs i) = h i ()) + e' + 1 ≤ n := by
  have hc := count_add_count_not (List.range n) (fun i => ev D p (xs i) = h i ())
  rw [List.length_range] at hc
  have hd : dist n h (fun i _ => ev D p (xs i)) ≤
      count (List.range n) (fun i => ¬ ev D p (xs i) = h i ()) :=
    count_mono_mem _ fun i _ hne heq => hne (funext fun u => by cases u; exact heq.symm)
  have := hfar p
  omega

/-- Farness form of zk-formal's RS line gap (`rsGap`, threshold `3n + 2e + 1`). -/
theorem line_far (xs : Nat → K) (n D e : Nat) (hD : D ≤ n) (hxs : Distinct xs n)
    (he : 2 * e + D ≤ n) (u v : Word Unit K)
    (hfar : ¬ ∃ w, (rsCode xs n D hD hxs).mem w ∧ dist n u w ≤ e)
    (Ks : List K) (hKs : Ks.Nodup) :
    count Ks (Good (rsCode xs n D hD hxs) e u v) ≤ 3 * n + 2 * e + 1 := by
  refine Nat.le_of_not_lt fun hlt => hfar ?_
  obtain ⟨v0, v1, hv0, _, hca⟩ := rsGap K xs n D e hD hxs he u v Ks hKs hlt
  exact ⟨v0, hv0, Nat.le_trans (count_mono _ fun i h => Or.inl h) hca⟩

end RecursionPoc
