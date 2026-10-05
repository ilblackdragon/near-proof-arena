import ZkFormal.Udr.BWKey
import ZkFormal.Udr.Statements

/-!
# ZkFormal.Udr.BW — the RS line proximity gap at the unique-decoding radius

`rsGap : RsGapStmt`.  Elementary Berlekamp–Welch argument for a line
`u0 + Z·u1` (no Polishchuk–Spielman):

1. `bw_key`: nonzero `E(X, Z)` (bidegree `≤ (e, e)`) and `N(X, Z)` with
   `N(xᵢ, z) = (u0ᵢ + z·u1ᵢ)·E(xᵢ, z)` at every position, for every `z`.
2. For a good `z` with `E(·, z) ≢ 0` (all but `≤ e` good `z`), with
   `e`-close codeword `p_z`: `N(·, z) - p_z·E(·, z)` has length `≤ n - e`
   and `≥ n - e` roots, so `p_z(xᵢ) = u0ᵢ + z·u1ᵢ` wherever `E(xᵢ, z) ≠ 0`.
3. Double counting over the positions `T` where `E(xᵢ, ·) ≢ 0` and
   Markov: more than `e + 1` "small" challenges (few zeros of `E(·, z)` in
   `T`); two of them interpolate `v0, v1`; every small `p_z` equals
   `v0 + z·v1`; each position of `T` is then pinned down by two small
   challenges, and `|Tᶜ| ≤ e`.
-/

namespace ZkFormal.Udr

open ArenaCore.Security
open Lean.Grind

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

theorem sum_map_mul_left' {α : Type} (l : List α) (c : Nat) (f : α → Nat) :
    (l.map fun a => c * f a).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem IsPoly.mul' {D e : Nat} {φ ψ : K → K} (h1 : IsPoly D φ) (h2 : IsPoly (e + 1) ψ) :
    IsPoly (D + e) (fun x => φ x * ψ x) := by
  cases D with
  | zero =>
    obtain ⟨c, hc⟩ := h1
    exact ⟨fun _ => 0, fun x => by
      show φ x * ψ x = _
      rw [hc x, ev_zero, ev_eq_zero (fun _ _ => rfl)]; grind⟩
  | succ d =>
    have := IsPoly.mul h1 h2
    rwa [show d + e + 1 = d + 1 + e by omega] at this

/-- **Agreement step.** If `N(xᵢ, z) = (u0ᵢ + z·u1ᵢ)·E(xᵢ, z)` everywhere and
the length-`D` polynomial `p` is `e`-close to the line point at `z`, then `p`
interpolates the line point wherever `E(xᵢ, z) ≠ 0`. -/
theorem bw_agree {xs : Nat → K} {n D e : Nat} (hxs : Distinct xs n) (hn : 2 * e + D ≤ n)
    (E N : Nat → Nat → K) (u0 u1 : Word Unit K) (z : K)
    (hpos : ∀ i, i < n → ev (n - e) (fun k => ev (e + 2) (N k) z) (xs i) =
      (u0 i () + z * u1 i ()) * ev (e + 1) (fun k => ev (e + 1) (E k) z) (xs i))
    (p : Nat → K) (w : Word Unit K) (hp : ∀ i, i < n → w i () = ev D p (xs i))
    (hd : dist n (line u0 u1 z) w ≤ e) :
    ∀ i, i < n → ev (e + 1) (fun k => ev (e + 1) (E k) z) (xs i) ≠ 0 →
      ev D p (xs i) = u0 i () + z * u1 i () := by
  let EX : K → K := fun x => ev (e + 1) (fun k => ev (e + 1) (E k) z) x
  let NX : K → K := fun x => ev (n - e) (fun k => ev (e + 2) (N k) z) x
  have hφ : IsPoly (n - e) (fun x => NX x - ev D p x * EX x) :=
    (IsPoly.of_ev _ _).sub ((IsPoly.mul' (IsPoly.of_ev D p) (IsPoly.of_ev (e + 1) _)).mono
      (by omega))
  obtain ⟨l, hlen, hmem, hnd⟩ := filter_props (List.range n) fun i => ¬ line u0 u1 z i ≠ w i
  have hc := count_add_count_not (List.range n) fun i => line u0 u1 z i ≠ w i
  rw [List.length_range] at hc
  have hd' : count (List.range n) (fun i => line u0 u1 z i ≠ w i) ≤ e := hd
  have hlt : ∀ i ∈ l, i < n := fun i hi => List.mem_range.mp (hmem i hi).1
  have hzero := hφ.eq_zero_of_roots (l.map xs) (hxs.map_nodup (hnd List.nodup_range) hlt)
    (by rw [List.length_map]; omega) (fun r hr => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
      have hag := congrFun (Classical.not_not.mp (hmem i hi).2) ()
      simp only [line] at hag
      show NX (xs i) - ev D p (xs i) * EX (xs i) = 0
      rw [show NX (xs i) = _ from hpos i (hlt i hi), hag, hp i (hlt i hi)]
      grind)
  intro i hi hE
  have h1 := hzero (xs i)
  have h2 : NX (xs i) = _ := hpos i hi
  have hinv := Field.mul_inv_cancel hE
  have : (ev D p (xs i) - (u0 i () + z * u1 i ())) * EX (xs i) = 0 := by
    grind
  have := congrArg (· * (EX (xs i))⁻¹) this
  grind

/-- **Berlekamp–Welch line gap** for Reed–Solomon codes at `2e + D ≤ n`,
threshold `3n + 2e + 1`. -/
theorem rsGap : RsGapStmt := by
  intro K _ xs n D e hD hxs hn u0 u1 Ks hKs hG
  classical
  obtain ⟨E, N, ⟨k0, j0, hk0, hj0, hE0⟩, hpos⟩ :=
    bw_key xs n e (by omega) hxs (fun i => u0 i ()) (fun i => u1 i ())
  let C := rsCode xs n D hD hxs
  let EX : K → K → K := fun z x => ev (e + 1) (fun k => ev (e + 1) (E k) z) x
  let col : Nat → K → K := fun j x => ev (e + 1) (fun k => E k j) x
  have hswap : ∀ z x, EX z x = ev (e + 1) (fun j => col j x) z := fun z x => ev_swap _ _ _ _ _
  have hpos' : ∀ z, ∀ i, i < n → ev (n - e) (fun k => ev (e + 2) (N k) z) (xs i) =
      (u0 i () + z * u1 i ()) * EX z (xs i) := fun z i hi => hpos i hi z
  -- good challenges with `E(·, z) ≢ 0`
  let G' : K → Prop := fun z => Good C e u0 u1 z ∧ ∃ k, k ≤ e ∧ ev (e + 1) (E k) z ≠ 0
  have hG' : count Ks (Good C e u0 u1) ≤ count Ks G' + e := by
    refine Nat.le_trans (count_le_and_add_not Ks (Good C e u0 u1)
      (fun z => ∃ k, k ≤ e ∧ ev (e + 1) (E k) z ≠ 0)) (Nat.add_le_add_left ?_ _)
    refine Nat.le_trans (count_mono _ (F := fun z => ev (e + 1) (E k0) z = 0) fun z hz =>
      Classical.byContradiction fun h => hz ⟨k0, hk0, h⟩) ?_
    have := count_roots_lt (m := e + 1) ⟨j0, by omega, hE0⟩ Ks hKs
    omega
  -- few zeros of `E(·, z)` among the points
  have hR : ∀ z, G' z → count (List.range n) (fun i => EX z (xs i) = 0) ≤ e := by
    intro z ⟨_, k, hk, hkz⟩
    have := count_roots_lt (m := e + 1) (c := fun k => ev (e + 1) (E k) z) ⟨k, by omega, hkz⟩
      ((List.range n).map xs) (hxs.map_nodup List.nodup_range fun i hi => List.mem_range.mp hi)
    rw [count_map] at this
    exact Nat.le_of_lt_succ this
  -- positions where `E(xᵢ, ·) ≢ 0`
  let T : Nat → Prop := fun i => ∃ j, j ≤ e ∧ col j (xs i) ≠ 0
  have hTroots : ∀ i, T i → count Ks (fun z => EX z (xs i) = 0) ≤ e := by
    intro i ⟨j, hj, hji⟩
    have := count_roots_lt (m := e + 1) (c := fun j => col j (xs i)) ⟨j, by omega, hji⟩ Ks hKs
    simp only [hswap]
    exact Nat.le_of_lt_succ this
  have hTc : ∀ i, ¬ T i → ∀ z, EX z (xs i) = 0 := by
    intro i hi z
    rw [hswap]
    exact ev_eq_zero (fun j hj => Classical.byContradiction fun h => hi ⟨j, by omega, h⟩) z
  -- double counting
  let f : K → Nat := fun z => count (List.range n) (fun i => G' z ∧ T i ∧ EX z (xs i) = 0)
  have hsum : (Ks.map f).sum ≤ n * e := by
    rw [sum_count_swap Ks (List.range n) (fun z i => G' z ∧ T i ∧ EX z (xs i) = 0)]
    have := sum_le_length_mul (List.range n)
      (fun i => count Ks (fun z => G' z ∧ T i ∧ EX z (xs i) = 0)) e (fun i _ => by
        by_cases hT : T i
        · exact Nat.le_trans (count_mono _ fun z h => h.2.2) (hTroots i hT)
        · refine Nat.le_trans (count_mono _ (F := fun _ => False) fun z h => hT h.2.1) ?_
          rw [count_const]; simp)
    rwa [List.length_range] at this
  -- Markov
  let Small : K → Prop := fun z => G' z ∧ 3 * f z ≤ e
  have hbig : count Ks (fun z => ¬ 3 * f z ≤ e) ≤ 3 * n := by
    have hm := count_ge_mul_le_sum Ks (fun z => 3 * f z) (e + 1)
    rw [sum_map_mul_left'] at hm
    have h1 : count Ks (fun z => ¬ 3 * f z ≤ e) ≤ count Ks (fun z => e + 1 ≤ 3 * f z) :=
      count_mono _ fun z h => by omega
    have h2 : count Ks (fun z => e + 1 ≤ 3 * f z) * (e + 1) ≤ 3 * n * (e + 1) := by
      rw [Nat.mul_assoc]
      exact Nat.le_trans hm (Nat.mul_le_mul_left 3 (Nat.le_trans hsum
        (Nat.mul_le_mul_left n (Nat.le_succ e))))
    exact Nat.le_trans h1 (Nat.le_of_mul_le_mul_right h2 (Nat.succ_pos e))
  have hsmall : e + 2 ≤ count Ks Small := by
    have := count_le_and_add_not Ks G' (fun z => 3 * f z ≤ e)
    have hG2 : 3 * n + 2 * e + 1 < count Ks (Good C e u0 u1) := hG
    have hS : count Ks Small = count Ks (fun a => G' a ∧ 3 * f a ≤ e) := rfl
    omega
  -- two small challenges interpolate `v0, v1`
  obtain ⟨z1, z2, hz12, hs1, hs2⟩ := two_of_count Small hKs (by omega)
  obtain ⟨⟨w1, ⟨p1, hp1⟩, hd1⟩, _⟩ := hs1.1
  obtain ⟨⟨w2, ⟨p2, hp2⟩, hd2⟩, _⟩ := hs2.1
  have hz : z1 - z2 ≠ 0 := fun h => hz12 (by grind)
  have hinv := Field.mul_inv_cancel hz
  let v1 : Nat → K := fun k => (z1 - z2)⁻¹ * p1 k + (-(z1 - z2)⁻¹) * p2 k
  let v0 : Nat → K := fun k => 1 * p1 k + (-z1) * v1 k
  have hv1 : ∀ x, ev D v1 x = (z1 - z2)⁻¹ * ev D p1 x + (-(z1 - z2)⁻¹) * ev D p2 x :=
    fun x => ev_lin _ _ _ _ _ _
  have hv0 : ∀ x, ev D v0 x = 1 * ev D p1 x + (-z1) * ev D v1 x := fun x => ev_lin _ _ _ _ _ _
  have hsolve : ∀ i, ev D p1 (xs i) = u0 i () + z1 * u1 i () →
      ev D p2 (xs i) = u0 i () + z2 * u1 i () →
      u0 i () = ev D v0 (xs i) ∧ u1 i () = ev D v1 (xs i) := by
    intro i h1 h2
    rw [hv0, hv1, h1, h2]
    constructor <;> grind
  have ag1 := bw_agree hxs hn E N u0 u1 z1 (hpos' z1) p1 w1 hp1 hd1
  have ag2 := bw_agree hxs hn E N u0 u1 z2 (hpos' z2) p2 w2 hp2 hd2
  have hTcnt : count (List.range n) (fun i => ¬ T i) ≤ e :=
    Nat.le_trans (count_mono _ fun i h => hTc i h z1) (hR z1 hs1.1)
  have hfle : ∀ z, Small z →
      count (List.range n) (fun i => T i ∧ EX z (xs i) = 0) ≤ f z := fun z hz =>
    count_mono _ fun i h => ⟨hz.1, h⟩
  -- every small challenge's codeword lies on the line `v0 + z·v1`
  have hline : ∀ z3, Small z3 → ∀ (p3 : Nat → K) (w3 : Word Unit K),
      (∀ i, i < n → w3 i () = ev D p3 (xs i)) → dist n (line u0 u1 z3) w3 ≤ e →
      ∀ x, ev D p3 x = ev D v0 x + z3 * ev D v1 x := by
    intro z3 hs3 p3 w3 hp3 hd3 x
    have ag3 := bw_agree hxs hn E N u0 u1 z3 (hpos' z3) p3 w3 hp3 hd3
    let A : Nat → Prop := fun i => T i ∧ EX z1 (xs i) ≠ 0 ∧ EX z2 (xs i) ≠ 0 ∧ EX z3 (xs i) ≠ 0
    have hnA : count (List.range n) (fun i => ¬ A i) ≤ 2 * e := by
      have hor : count (List.range n) (fun i => ¬ A i) ≤
          count (List.range n) (fun i => ¬ T i) +
          (count (List.range n) (fun i => T i ∧ EX z1 (xs i) = 0) +
          (count (List.range n) (fun i => T i ∧ EX z2 (xs i) = 0) +
          count (List.range n) (fun i => T i ∧ EX z3 (xs i) = 0))) := by
        refine Nat.le_trans (count_mono _ (F := fun i => ¬ T i ∨ ((T i ∧ EX z1 (xs i) = 0) ∨
          ((T i ∧ EX z2 (xs i) = 0) ∨ (T i ∧ EX z3 (xs i) = 0)))) fun i h => ?_)
          (Nat.le_trans (count_or_le _ _ _) (Nat.add_le_add_left (Nat.le_trans
            (count_or_le _ _ _) (Nat.add_le_add_left (count_or_le _ _ _) _)) _))
        by_cases hT : T i
        · by_cases h1 : EX z1 (xs i) = 0
          · exact Or.inr (Or.inl ⟨hT, h1⟩)
          by_cases h2 : EX z2 (xs i) = 0
          · exact Or.inr (Or.inr (Or.inl ⟨hT, h2⟩))
          by_cases h3 : EX z3 (xs i) = 0
          · exact Or.inr (Or.inr (Or.inr ⟨hT, h3⟩))
          exact absurd ⟨hT, h1, h2, h3⟩ h
        · exact Or.inl hT
      have := hfle z1 hs1; have := hfle z2 hs2; have := hfle z3 hs3
      have := hs1.2; have := hs2.2; have := hs3.2
      omega
    have hcA := count_add_count_not (List.range n) A
    rw [List.length_range] at hcA
    have := ev_eq_of_agree (D := D) hxs p3 (fun k => v0 k + z3 * v1 k) A (by omega)
      (fun i hi ⟨_, h1, h2, h3⟩ => by
        obtain ⟨e0, e1⟩ := hsolve i (ag1 i hi h1) (ag2 i hi h2)
        rw [ag3 i hi h3, ev_add_smul, e0, e1]) x
    rw [this, ev_add_smul]
  -- correlated agreement outside `Tᶜ`
  refine ⟨fun i _ => ev D v0 (xs i), fun i _ => ev D v1 (xs i), ⟨v0, fun _ _ => rfl⟩,
    ⟨v1, fun _ _ => rfl⟩, Nat.le_trans (count_mono_mem _ fun i hi h => ?_) hTcnt⟩
  have hi := List.mem_range.mp hi
  intro hT
  have hc2 : 2 ≤ count Ks (fun z => Small z ∧ EX z (xs i) ≠ 0) := by
    have := count_le_and_add_not Ks Small (fun z => EX z (xs i) ≠ 0)
    have := Nat.le_trans (count_mono Ks (E := fun z => ¬ EX z (xs i) ≠ 0) (F := fun z => EX z (xs i) = 0)
      fun z h => Classical.not_not.mp h) (hTroots i hT)
    omega
  obtain ⟨za, zb, hab, ⟨hsa, hEa⟩, ⟨hsb, hEb⟩⟩ := two_of_count _ hKs hc2
  obtain ⟨⟨wa, ⟨pa, hpa⟩, hda⟩, _⟩ := hsa.1
  obtain ⟨⟨wb, ⟨pb, hpb⟩, hdb⟩, _⟩ := hsb.1
  have ea := (bw_agree hxs hn E N u0 u1 za (hpos' za) pa wa hpa hda i hi hEa).symm.trans
    (hline za hsa pa wa hpa hda (xs i))
  have eb := (bw_agree hxs hn E N u0 u1 zb (hpos' zb) pb wb hpb hdb i hi hEb).symm.trans
    (hline zb hsb pb wb hpb hdb (xs i))
  have hzab : za - zb ≠ 0 := fun h => hab (by grind)
  have hinv' := Field.mul_inv_cancel hzab
  have e1 : u1 i () = ev D v1 (xs i) := by
    have : (u1 i () - ev D v1 (xs i)) * (za - zb) = 0 := by grind
    have := congrArg (· * (za - zb)⁻¹) this
    grind
  have e0 : u0 i () = ev D v0 (xs i) := by rw [e1] at ea; grind
  rcases h with h | h
  · exact h (by funext c; cases c; exact e0)
  · exact h (by funext c; cases c; exact e1)

end ZkFormal.Udr
