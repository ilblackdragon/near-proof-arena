import ZkFormal.Udr.Np.Domain
import ZkFormal.Udr.Np.Early
import ZkFormal.Udr.Np.Bus
import ZkFormal.Algebra.Main

/-!
# ZkFormal.Prover.NpPoly — polynomial toolkit for the honest np prover (lane L7)

Coefficient-function polynomials (`Udr.ev`, `Udr.IsPoly`, L3) and L1's Lagrange
interpolation, plus what the completeness proof needs on top:

* `pick`: a coefficient function chosen by specification (the prover model is a
  mathematical definition, never executed);
* `ofBase_ev`: evaluation commutes with `F ⊆ K`;
* `ev_split`, `ev_chunks`: splitting a length-`n·T` polynomial into `n` chunks of
  length `T` (`Q = Σ_j X^{jT} Q_j`, read with `combine`);
* `exists_div_vanish`: a polynomial vanishing on the trace domain `⟨ω⟩` (`|ω| = T`)
  is `(X^T - 1)·q` with `q` of length `m - T`;
* `exists_interp`: interpolation through distinct points (from `Poly.lagrange_spec`);
* trace-domain selectors: `selSum T (ω^r) = [r = 0]`, and the closed forms of the
  verifier at a point off the domain.
-/

namespace ZkFormal.Prover.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

set_option linter.unusedSectionVars false

/-! ## Choice of coefficients -/

/-- A coefficient function satisfying `P` (zero if none exists). -/
noncomputable def pick {K : Type} [Zero K] (P : (Nat → K) → Prop) : Nat → K :=
  open Classical in if h : ∃ c, P c then Classical.choose h else fun _ => 0

theorem pick_spec {K : Type} [Zero K] {P : (Nat → K) → Prop} (h : ∃ c, P c) : P (pick P) := by
  unfold pick; split
  · exact Classical.choose_spec ‹_›
  · contradiction

/-! ## Generic `ev` facts -/

section
variable {K : Type} [Field K]

theorem ev_split (a : Nat) : ∀ (b : Nat) (c : Nat → K) (x : K),
    ev (a + b) c x = ev a c x + x ^ a * ev b (fun k => c (a + k)) x := by
  induction a with
  | zero => intro b c x; simp only [Nat.zero_add, ev_zero, Semiring.pow_zero]; grind
  | succ a ih =>
    intro b c x
    rw [show a + 1 + b = (a + b) + 1 by omega, ev_succ, ev_succ, ih b (fun k => c (k + 1)) x]
    rw [Semiring.pow_succ]
    have : (fun k => c (a + k + 1)) = (fun k => c (a + 1 + k)) := by funext k; rw [Nat.add_right_comm]
    rw [this]; grind

/-- `ev (n·T) q x = Σ_j (x^T)^j · ev T (q (jT + ·)) x`, read with `combine`. -/
theorem ev_chunks (T : Nat) : ∀ (n : Nat) (q : Nat → K) (x : K),
    ev (n * T) q x = combine (x ^ T) ((List.range n).map fun j => ev T (fun k => q (j * T + k)) x)
  | 0, q, x => by simp [combine, ev_zero]
  | n + 1, q, x => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show _ = ev T (fun k => q (0 * T + k)) x + x ^ T * combine (x ^ T) _
    rw [show (n + 1) * T = T + n * T by rw [Nat.succ_mul, Nat.add_comm], ev_split,
      ev_chunks T n (fun k => q (T + k)) x]
    have h1 : (fun k => q (0 * T + k)) = q := by funext k; rw [Nat.zero_mul, Nat.zero_add]
    have h2 : ((List.range n).map fun j => ev T (fun k => q (T + (j * T + k))) x) =
        (List.range n).map ((fun j => ev T (fun k => q (j * T + k)) x) ∘ Nat.succ) := by
      apply List.map_congr_left; intro j _
      simp only [Function.comp, Nat.succ_mul]
      congr 1; funext k; congr 1; omega
    rw [h1, h2]

theorem ev_mono_pad {m m' : Nat} (hm : m ≤ m') (c : Nat → K) :
    ∃ c' : Nat → K, ∀ x, ev m c x = ev m' c' x := by
  have := IsPoly.mono hm (IsPoly.of_ev m c)
  obtain ⟨c', hc'⟩ := this
  exact ⟨c', hc'⟩

/-- Division by `X^T - 1` with remainder of length `T`. -/
theorem exists_div_XT (T : Nat) (hT : 1 ≤ T) : ∀ (m : Nat) (c : Nat → K),
    ∃ q r : Nat → K, ∀ x, ev m c x = (x ^ T - 1) * ev (m - T) q x + ev T r x := by
  intro m
  induction m with
  | zero => intro c; exact ⟨fun _ => 0, fun _ => 0, fun x => by
      rw [ev_eq_zero (fun _ _ => rfl), ev_eq_zero (fun _ _ => rfl), ev_zero]; grind⟩
  | succ m ih =>
    intro c
    by_cases hm : m + 1 ≤ T
    · refine ⟨fun _ => 0, fun k => if k < m + 1 then c k else 0, fun x => ?_⟩
      rw [ev_eq_zero (fun _ _ => rfl), ev_pad hm (fun k h1 _ => by simp [show ¬ k < m + 1 by omega])]
      rw [ev_congr (c := fun k => if k < m + 1 then c k else 0) (c' := c) (fun k hk => by simp only [hk, ite_true])]
      grind
    · -- c_m x^m = c_m x^(m-T) (x^T - 1) + c_m x^(m-T)
      classical
      let c1 : Nat → K := fun k => if k = m - T then c k + c m else c k
      obtain ⟨q, r, h⟩ := ih c1
      refine ⟨fun k => if k < m - T then q k else if k = m - T then c m else 0, r, fun x => ?_⟩
      have e1 : ev (m + 1) c x = ev m c x + c m * x ^ m := ev_succ_last m c x
      have eI : ev m (fun k => if k = m - T then c m else 0) x = c m * x ^ (m - T) := by
        rw [ev_pad (m := m - T + 1) (by omega) (fun k h1 _ => by simp [show k ≠ m - T by omega]),
          ev_succ_last, ev_eq_zero (fun k hk => by simp [show k ≠ m - T by omega])]
        simp only [ite_true]; grind
      have e2 : ev m c1 x = ev m c x + c m * x ^ (m - T) := by
        have := ev_add m c (fun k => if k = m - T then c m else 0) x
        have h3 : (fun k => c k + (if k = m - T then c m else 0)) = c1 := by
          funext k; simp only [c1]; split <;> grind
        rw [h3, eI] at this; exact this
      have e3 : ev (m + 1 - T) (fun k => if k < m - T then q k else if k = m - T then c m else 0) x =
          ev (m - T) q x + c m * x ^ (m - T) := by
        rw [show m + 1 - T = (m - T) + 1 by omega, ev_succ_last]
        simp only [Nat.lt_irrefl, ite_false, ite_true]
        rw [ev_congr (c' := q) (fun k hk => by simp [hk])]
      have hx : x ^ m = x ^ T * x ^ (m - T) := by
        rw [← Semiring.pow_add]; congr 1; omega
      rw [e1, e3, hx]
      have := h x
      rw [e2] at this
      grind

/-- A polynomial vanishing on `T` distinct `T`-th roots of unity is divisible by `X^T - 1`. -/
theorem exists_div_vanish {T m : Nat} (hT : 1 ≤ T) (pts : Nat → K) (hd : Distinct pts T)
    (hpow : ∀ j, j < T → pts j ^ T = 1) (c : Nat → K) (hz : ∀ j, j < T → ev m c (pts j) = 0) :
    ∃ q : Nat → K, ∀ x, ev m c x = (x ^ T - 1) * ev (m - T) q x := by
  obtain ⟨q, r, h⟩ := exists_div_XT T hT m c
  refine ⟨q, fun x => ?_⟩
  have hr : ∀ x, ev T r x = 0 := by
    refine (IsPoly.of_ev T r).eq_zero_of_roots ((List.range T).map pts)
      (hd.map_nodup List.nodup_range (fun i hi => List.mem_range.mp hi)) (by simp) ?_
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
    have hj' := List.mem_range.mp hj
    have := h (pts j)
    rw [hz j hj', hpow j hj'] at this
    grind
  rw [h x, hr x]; grind

/-- Horner evaluation of a coefficient list. -/
theorem evalL_eq_ev (x : K) : ∀ l : List K, Poly.evalL x l = ev l.length (fun k => l.getD k 0) x
  | [] => rfl
  | a :: l => by
    rw [Poly.evalL_cons, List.length_cons, ev_succ, evalL_eq_ev x l]
    rfl

/-- Interpolation through `n` distinct points. -/
theorem exists_interp [DecidableEq K] {pts : Nat → K} {n : Nat} (hd : Distinct pts n)
    (vals : Nat → K) : ∃ c : Nat → K, ∀ r, r < n → ev n c (pts r) = vals r := by
  let xs := (List.range n).map pts
  let v : K → K := fun x => match (List.range n).find? (fun j => decide (pts j = x)) with
    | some j => vals j
    | none => 0
  obtain ⟨hdeg, hval⟩ := Poly.lagrange_spec K xs v
  have hnd : xs.Nodup := hd.map_nodup List.nodup_range (fun i hi => List.mem_range.mp hi)
  refine ⟨fun k => (Poly.lagrange xs v).coeffs.getD k 0, fun r hr => ?_⟩
  have hxs : xs.length = n := by simp [xs]
  have hmem : pts r ∈ xs := List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩
  have h1 := hval hnd (pts r) hmem
  rw [Poly.eval_def, evalL_eq_ev] at h1
  have hpad : ev n (fun k => (Poly.lagrange xs v).coeffs.getD k 0) (pts r) =
      ev (Poly.lagrange xs v).coeffs.length (fun k => (Poly.lagrange xs v).coeffs.getD k 0) (pts r) := by
    rcases Nat.le_total n (Poly.lagrange xs v).coeffs.length with hle | hle
    · exact (ev_pad hle (fun k h1 _ => hdeg k (by omega)) _).symm
    · exact ev_pad hle (fun k h1 _ => Poly.getD_ge_length _ k h1) _
  rw [hpad, h1]
  show (match (List.range n).find? (fun j => decide (pts j = pts r)) with
    | some j => vals j | none => 0) = vals r
  have hf : (List.range n).find? (fun j => decide (pts j = pts r)) = some r := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simp, r, by simpa using hr, by simp, fun j hj => ?_⟩
    simp only [List.getElem_range, Bool.not_eq_true', decide_eq_false_iff_not]
    intro he
    have := hd j r (by omega) hr he
    omega
  rw [hf]

end

/-! ## Base field to extension -/

theorem ofBase_pow' (a : Fp) : ∀ n : Nat, Fp8.ofBase (a ^ n) = Fp8.ofBase a ^ n := ofBase_pow a

/-- Evaluation commutes with `Fp ⊆ Fp8`. -/
theorem ofBase_ev : ∀ (m : Nat) (c : Nat → Fp) (y : Fp),
    Fp8.ofBase (ev m c y) = ev m (fun k => Fp8.ofBase (c k)) (Fp8.ofBase y)
  | 0, _, _ => rfl
  | m + 1, c, y => by
    rw [ev_succ, ev_succ, Fp8.ofBase_add, Fp8.ofBase_mul, ofBase_ev m]

theorem ofBase_natCast (n : Nat) : Fp8.ofBase (n : Fp) = (n : Fp8) := rfl

theorem ofBase_inv (a : Fp) : Fp8.ofBase a⁻¹ = (Fp8.ofBase a)⁻¹ := by
  by_cases ha : a = 0
  · subst ha
    have h1 : (0 : Fp)⁻¹ = 0 := Field.inv_zero
    have h2 : (0 : Fp8)⁻¹ = 0 := Field.inv_zero
    rw [h1]; exact h2.symm
  · have hb : Fp8.ofBase a ≠ 0 := fun h => ha (Fp8.ofBase_inj (h.trans rfl))
    have e : Fp8.ofBase a * Fp8.ofBase a⁻¹ = 1 := by
      rw [← Fp8.ofBase_mul, Field.mul_inv_cancel ha]; rfl
    have e2 := Field.mul_inv_cancel hb
    grind

/-! ## Trace-domain geometry -/

theorem npGeo {K : Type} [Field K] (y : K) : ∀ m : Nat, ev m (fun _ => 1) y * (y - 1) = y ^ m - 1
  | 0 => by rw [ev_zero, Semiring.pow_zero]; grind
  | m + 1 => by
    rw [ev_succ_last, Semiring.pow_succ]
    have := npGeo y m
    grind

theorem npEvOne : ∀ m : Nat, ev m (fun _ => (1 : Fp8)) 1 = ((m : Nat) : Fp8)
  | 0 => rfl
  | m + 1 => by
    rw [ev_succ_last, npEvOne m, Semiring.one_pow]
    show _ = @Nat.cast Fp8 Semiring.natCast (m + 1)
    rw [Semiring.natCast_succ]
    show @Nat.cast Fp8 Semiring.natCast m + 1 * 1 = _
    grind

theorem npNatCast_ne_zero {n : Nat} (h0 : 0 < n) (h : n < Algebra.P) : ((n : Nat) : Fp8) ≠ 0 := by
  intro he
  have : ((n : Nat) : Fp8) = ((0 : Nat) : Fp8) := he
  have := natCast_fp8_inj h (by decide) this
  omega

theorem npTwoPow_ne_zero {k : Nat} (hk : k ≤ 27) : ((2 ^ k : Nat) : Fp8) ≠ 0 :=
  npNatCast_ne_zero (Nat.two_pow_pos _)
    (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hk) (by decide))

theorem npOmg_pow_inj {log : Nat} (hlog : log ≤ 27) {i j : Nat} (hi : i < 2 ^ log) (hj : j < 2 ^ log)
    (h : omg log ^ i = omg log ^ j) : i = j := by
  unfold omg at h
  rw [← ofBase_pow, ← ofBase_pow] at h
  exact Fp.twoAdicGen_pow_inj hlog hi hj (Fp8.ofBase_inj h)

theorem npOmg_pow_mod {log : Nat} (hlog : log ≤ 27) (n : Nat) :
    omg log ^ n = omg log ^ (n % 2 ^ log) := by
  conv => lhs; rw [← Nat.div_add_mod n (2 ^ log)]
  rw [Semiring.pow_add, pow_mul_eq, omg_pow_T hlog, Semiring.one_pow, Semiring.one_mul]

theorem npDistinct_omg {log : Nat} (hlog : log ≤ 27) : Distinct (fun r => omg log ^ r) (2 ^ log) :=
  fun _ _ hi hj h => npOmg_pow_inj hlog hi hj h

theorem npOmg_ne_zero (log : Nat) (hlog : log ≤ 27) : omg log ≠ 0 := fun h =>
  Fp.twoAdicGen_ne_zero log hlog (Fp8.ofBase_inj (h.trans rfl))

theorem npSelSum_omg {log : Nat} (hlog : log ≤ 27) {r : Nat} (hr : r < 2 ^ log) :
    selSum (2 ^ log) (omg log ^ r) = if r = 0 then 1 else 0 := by
  unfold selSum
  have hT : ((2 ^ log : Nat) : Fp8) ≠ 0 := npTwoPow_ne_zero hlog
  split
  · next h0 =>
    subst h0
    rw [Semiring.pow_zero, npEvOne]
    exact Field.inv_mul_cancel hT
  · next h0 =>
    have hne : omg log ^ r - 1 ≠ 0 := by
      intro h
      have : omg log ^ r = omg log ^ 0 := by rw [Semiring.pow_zero]; grind
      exact h0 (npOmg_pow_inj hlog hr (Nat.two_pow_pos _) this)
    have hg := npGeo (omg log ^ r) (2 ^ log)
    rw [omg_pow_r_T hlog, show (1 : Fp8) - 1 = 0 by grind] at hg
    rcases ZkFormal.Udr.gp_mul_eq_zero hg with h | h
    · rw [h]; grind
    · exact absurd h hne

theorem npSelSum_omg_next {log : Nat} (hlog : log ≤ 27) {r : Nat} (hr : r < 2 ^ log) :
    selSum (2 ^ log) (omg log * omg log ^ r) = if r + 1 = 2 ^ log then 1 else 0 := by
  have e : omg log * omg log ^ r = omg log ^ ((r + 1) % 2 ^ log) := by
    rw [← npOmg_pow_mod hlog, Semiring.pow_succ]; grind
  rw [e, npSelSum_omg hlog (Nat.mod_lt _ (Nat.two_pow_pos _))]
  by_cases h : r + 1 = 2 ^ log
  · rw [if_pos (by rw [h, Nat.mod_self]), if_pos h]
  · rw [if_neg (by rw [Nat.mod_eq_of_lt (by omega)]; omega), if_neg h]

/-- The polynomial first-row selector equals the verifier's closed form off `x = 1`. -/
theorem npSelSum_closed {T : Nat} (hT : (T : Fp8) ≠ 0) {x : Fp8} (hx : x ≠ 1) :
    selSum T x = (x ^ T - 1) / ((T : Fp8) * (x - 1)) := by
  unfold selSum
  have h1 : x - 1 ≠ 0 := fun h => hx (by grind)
  have hg := npGeo x T
  have : ev T (fun _ => (1 : Fp8)) x = (x ^ T - 1) / (x - 1) := by
    rw [← hg]; grind
  rw [this]; grind

end ZkFormal.Prover.Np
