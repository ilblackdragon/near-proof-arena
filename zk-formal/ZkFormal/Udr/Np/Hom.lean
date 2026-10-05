import ZkFormal.Udr.Np.Chal7
import ZkFormal.Udr.Np.Domain

/-!
# ZkFormal.Udr.Np.Hom — base-field decoding and the evaluation homomorphism

* `colAt_base`: a decoded main column (an `Fp`-valued word decoded in `Fp8`)
  takes base-field values at base-field points: its coordinate polynomials
  `1..7` vanish on the agreement set (`≥ T + 1` distinct points).
* geometric sums over the trace domain: `selSum T (ω^r) = [r = 0]`.
* `evalWith_hom`: on the trace domain, the polynomial environment evaluates
  every expression to the base-field value on the decoded trace.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-! ## Coordinates -/

theorem coeff_add (a b : Fp8) (k : Nat) : Fp8.coeff (a + b) k = Fp8.coeff a k + Fp8.coeff b k := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
  | _ + 8 => show (0 : Fp) = 0 + 0; grind

theorem coeff_ofBase_mul (y : Fp) (a : Fp8) (k : Nat) :
    Fp8.coeff (Fp8.ofBase y * a) k = y * Fp8.coeff a k := by
  rw [← Fp8.smulBase_eq]
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
  | _ + 8 => show (0 : Fp) = y * 0; grind

theorem coeff_zero (k : Nat) : Fp8.coeff 0 k = 0 := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
  | _ + 8 => rfl

theorem ev_coeff (k : Nat) : ∀ (m : Nat) (P : Nat → Fp8) (y : Fp),
    Fp8.coeff (ev m P (Fp8.ofBase y)) k = ev m (fun j => Fp8.coeff (P j) k) y
  | 0, _, _ => coeff_zero k
  | m + 1, Q, y => by
    rw [ev_succ, ev_succ, coeff_add, coeff_ofBase_mul, ev_coeff k m]

theorem isBase_of_coeff {a : Fp8} (h : ∀ k, 1 ≤ k → k < 8 → Fp8.coeff a k = 0) : a.IsBase :=
  ⟨h 1 (by omega) (by omega), h 2 (by omega) (by omega), h 3 (by omega) (by omega),
    h 4 (by omega) (by omega), h 5 (by omega) (by omega), h 6 (by omega) (by omega),
    h 7 (by omega) (by omega)⟩

theorem coeff_ofBase {c : Fp} {k : Nat} (hk : 1 ≤ k) : Fp8.coeff (Fp8.ofBase c) k = 0 := by
  match k, hk with
  | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
  | _ + 8, _ => rfl

theorem ofBase_c0 {a : Fp8} (h : a.IsBase) : Fp8.ofBase a.c0 = a := by
  obtain ⟨c, rfl⟩ := (Fp8.isBase_iff a).mp h; rfl

/-! ## Base-field decoding -/

section
variable {A : Air} {prm : Params}

theorem agree_count {n e : Nat} {u v : Word Unit Fp8} (h : dist n u v ≤ e) :
    n - e ≤ count (List.range n) (fun p => u p = v p) := by
  have := count_add_count_not (List.range n) (fun p => u p = v p)
  rw [List.length_range] at this
  unfold dist at h
  simp only [ne_eq] at h
  omega

/-- A main column decodes to base-field values at base-field points. -/
theorem colAt_base (τ : PTn) (d : Col) (hd : d.kind = 0)
    (hlde : (tl A prm τ d.t).lde = (tl A prm τ d.t).log + prm.logBlowup)
    (hb : prm.logBlowup = 4) (hm : (tl A prm τ d.t).lde ≤ 27) (y : Fp) :
    (colAt A prm τ d (Fp8.ofBase y)).IsBase := by
  unfold colAt colP
  dsimp only
  split
  · next h =>
    generalize hP : Classical.choose h = P
    have hd' := Classical.choose_spec h
    rw [hP] at hd'
    refine isBase_of_coeff fun k hk1 hk8 => ?_
    rw [ev_coeff]
    generalize tl A prm τ d.t = L at *
    generalize n0Of A prm τ = n0 at *
    have hroots := agree_count hd'
    obtain ⟨l', hlen, hmem, hnd⟩ := filter_props (List.range (2 ^ L.lde))
      (fun p => (fun (_ : Unit) => colVal τ d p) = fun _ => ev (2 ^ L.log + 1) P (pt n0 L.lde p))
    have hpoly : IsPoly (2 ^ L.log + 1) (fun z => ev (2 ^ L.log + 1) (fun j => Fp8.coeff (P j) k) z) :=
      IsPoly.of_ev _ _
    refine hpoly.eq_zero_of_roots (l'.map fun p => domPoint (K := Fp8) n0 L.lde p) ?_ ?_ ?_ y
    · refine nodup_map_on (fun p hp q hq hpq => ?_) (hnd List.nodup_range)
      have h1 := List.mem_range.mp (hmem p hp).1
      have h2 := List.mem_range.mp (hmem q hq).1
      exact pt_inj hm h1 h2 (congrArg Fp8.ofBase hpq)
    · rw [List.length_map, hlen]
      have e1 : 2 ^ L.lde = 2 ^ L.log * 16 := by
        rw [hlde, hb, Nat.pow_add]
      have e2 : 2 ^ (L.lde - prm.logBlowup) = 2 ^ L.log := by
        rw [hlde, Nat.add_sub_cancel]
      have he : eRad prm L.lde = (2 ^ L.log * 16 - 2 ^ L.log) / 2 - 1 := by
        unfold eRad; rw [e2, e1]
      rw [he] at hroots
      have := Nat.two_pow_pos L.log
      omega
    · intro r hr
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      have hag := congrFun (hmem p hp).2 ()
      have hcv : colVal τ d p = Fp8.ofBase ((matOf (oracleOf τ d.kind) d.t).row p |>.getD d.c 0) := by
        unfold colVal; rw [if_pos hd]
      rw [hcv] at hag
      have := congrArg (fun a => Fp8.coeff a k) hag
      rw [coeff_ofBase hk1] at this
      have e3 : pt n0 L.lde p = Fp8.ofBase (domPoint (K := Fp8) n0 L.lde p) := rfl
      rw [e3, ev_coeff] at this
      exact this.symm
  · rw [ev_eq_zero (fun _ _ => rfl)]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end

/-! ## Geometric sums on the trace domain -/

theorem geo (y : Fp8) : ∀ m : Nat, ev m (fun _ => 1) y * (y - 1) = y ^ m - 1
  | 0 => by rw [ev_zero, Semiring.pow_zero]; grind
  | m + 1 => by
    rw [ev_succ_last, Semiring.pow_succ]
    have := geo y m
    grind

theorem ev_one_one : ∀ m : Nat, ev m (fun _ => (1 : Fp8)) 1 = ((m : Nat) : Fp8)
  | 0 => rfl
  | m + 1 => by
    rw [ev_succ_last, ev_one_one m, Semiring.one_pow]
    show _ = @Nat.cast Fp8 Semiring.natCast (m + 1)
    rw [Semiring.natCast_succ]
    show @Nat.cast Fp8 Semiring.natCast m + 1 * 1 = _
    grind

theorem natCast_ne_zero {n : Nat} (h0 : 0 < n) (h : n < Algebra.P) : ((n : Nat) : Fp8) ≠ 0 := by
  intro he
  have : ((n : Nat) : Fp8) = ((0 : Nat) : Fp8) := he
  have := natCast_fp8_inj h (by decide) this
  omega

theorem omg_pow_inj {log : Nat} (hlog : log ≤ 27) {i j : Nat} (hi : i < 2 ^ log) (hj : j < 2 ^ log)
    (h : omg log ^ i = omg log ^ j) : i = j := by
  unfold omg at h
  rw [← ofBase_pow, ← ofBase_pow] at h
  exact Fp.twoAdicGen_pow_inj hlog hi hj (Fp8.ofBase_inj h)

theorem omg_pow_mod {log : Nat} (hlog : log ≤ 27) (n : Nat) :
    omg log ^ n = omg log ^ (n % 2 ^ log) := by
  conv => lhs; rw [← Nat.div_add_mod n (2 ^ log)]
  rw [Semiring.pow_add, pow_mul_eq, omg_pow_T hlog, Semiring.one_pow, Semiring.one_mul]

theorem selSum_omg {log : Nat} (hlog : log ≤ 27) {r : Nat} (hr : r < 2 ^ log) :
    selSum (2 ^ log) (omg log ^ r) = if r = 0 then 1 else 0 := by
  unfold selSum
  have hT : ((2 ^ log : Nat) : Fp8) ≠ 0 := natCast_ne_zero (Nat.two_pow_pos _)
    (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hlog) (by decide))
  split
  · next h0 =>
    subst h0
    rw [Semiring.pow_zero, ev_one_one]
    exact Field.inv_mul_cancel hT
  · next h0 =>
    have hne : omg log ^ r - 1 ≠ 0 := by
      intro h
      have : omg log ^ r = omg log ^ 0 := by rw [Semiring.pow_zero]; grind
      exact h0 (omg_pow_inj hlog hr (Nat.two_pow_pos _) this)
    have hg := geo (omg log ^ r) (2 ^ log)
    rw [omg_pow_r_T hlog, show (1 : Fp8) - 1 = 0 by grind] at hg
    rcases ZkFormal.Udr.gp_mul_eq_zero hg with h | h
    · rw [h]; grind
    · exact absurd h hne

theorem selSum_omg_next {log : Nat} (hlog : log ≤ 27) {r : Nat} (hr : r < 2 ^ log) :
    selSum (2 ^ log) (omg log * omg log ^ r) = if r + 1 = 2 ^ log then 1 else 0 := by
  have e : omg log * omg log ^ r = omg log ^ ((r + 1) % 2 ^ log) := by
    rw [← omg_pow_mod hlog, Semiring.pow_succ]; grind
  rw [e, selSum_omg hlog (Nat.mod_lt _ (Nat.two_pow_pos _))]
  by_cases h : r + 1 = 2 ^ log
  · rw [if_pos (by rw [h, Nat.mod_self]), if_pos h]
  · rw [if_neg (by rw [Nat.mod_eq_of_lt (by omega)]; omega), if_neg h]

end ZkFormal.Udr.Np
