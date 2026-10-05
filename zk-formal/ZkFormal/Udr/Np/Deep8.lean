import ZkFormal.Udr.Np.Shape8
import ZkFormal.Udr.Np.Domain

/-!
# ZkFormal.Udr.Np.Deep8 — close DEEP words give close columns and right claims

If the DEEP word of class `m` is within `eRad m` of `RS[2^log]` and `z ∉ F`,
then (`deep_close`) the class's column word is within `eRad m` of
`RS[2^log + 1]`, and each claimed OOD value equals the decoded column
(`colAt`) at `z` / `ωz` (unique decoding: `2·eRad m + 2^log + 1 ≤ 2^m`).
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr

/-! ## Unique decoding of one column -/

theorem uniq_dec {xs : Nat → Fp8} {n D e : Nat} (hxs : Distinct xs n) (h2 : D + 2 * e ≤ n)
    (w : Word Unit Fp8) (P Q : Nat → Fp8) (hP : dist n w (fun p _ => ev D P (xs p)) ≤ e)
    (hQ : dist n w (fun p _ => ev D Q (xs p)) ≤ e) (x : Fp8) : ev D P x = ev D Q x := by
  have ht := dist_triangle n (fun p (_ : Unit) => ev D P (xs p)) w (fun p _ => ev D Q (xs p))
  rw [dist_comm n _ w] at ht
  have hc := agree_count (Nat.le_trans ht (Nat.add_le_add hP hQ))
  exact ev_eq_of_agree hxs P Q (fun p => (fun (_ : Unit) => ev D P (xs p)) = fun _ => ev D Q (xs p))
    (by omega) (fun i _ hi => congrFun hi ()) x

section
variable {A : Air} {prm : Params}

theorem colAt_of_close (τ : PTn) (d : Col)
    (hD : 2 ^ (tl A prm τ d.t).log + 1 + 2 * eRad prm (tl A prm τ d.t).lde ≤ 2 ^ (tl A prm τ d.t).lde)
    (hxs : Distinct (pt (n0Of A prm τ) (tl A prm τ d.t).lde) (2 ^ (tl A prm τ d.t).lde))
    (P : Nat → Fp8)
    (hP : dist (2 ^ (tl A prm τ d.t).lde) (fun p (_ : Unit) => colVal τ d p)
      (fun p _ => ev (2 ^ (tl A prm τ d.t).log + 1) P (pt (n0Of A prm τ) (tl A prm τ d.t).lde p)) ≤
      eRad prm (tl A prm τ d.t).lde) (x : Fp8) :
    colAt A prm τ d x = ev (2 ^ (tl A prm τ d.t).log + 1) P x := by
  unfold colAt colP
  dsimp only
  split
  · next h => exact uniq_dec hxs hD _ _ _ (Classical.choose_spec h) hP x
  · next h => exact absurd ⟨P, hP⟩ h

end

/-! ## Membership in the DEEP column list -/

theorem mem_deepCols {lay : List TLayout} {m : Nat} {d : Col} {s : Bool}
    (h : (d, s) ∈ deepCols lay m) : ∃ L, lay[d.t]? = some L ∧ L.lde = m := by
  unfold deepCols at h
  obtain ⟨⟨L, t⟩, hLt, hd⟩ := List.mem_flatMap.mp h
  obtain ⟨hz, hm⟩ := List.mem_filter.mp hLt
  have hz' := List.mem_zipIdx_iff_getElem?.mp hz
  have ht : d.t = t := by
    simp only [List.mem_append, List.mem_map, List.mem_range] at hd
    rcases hd with (((⟨c, _, he⟩ | ⟨c, _, he⟩) | ⟨c, _, he⟩) | ⟨c, _, he⟩) | ⟨c, _, he⟩ <;>
      (cases he; rfl)
  exact ⟨L, by rw [ht]; exact hz', by simpa using hm⟩

theorem deepCols_of_classCols {lay : List TLayout} {m : Nat} {d : Col}
    (h : d ∈ classCols lay m 3) : (d, false) ∈ deepCols lay m := by
  unfold classCols at h
  unfold deepCols
  obtain ⟨⟨L, t⟩, hLt, hd⟩ := List.mem_flatMap.mp h
  refine List.mem_flatMap.mpr ⟨(L, t), hLt, ?_⟩
  unfold tableCols at hd
  dsimp only at hd ⊢
  rw [if_pos (by decide), if_pos (by decide)] at hd
  simp only [List.mem_append, List.mem_map, List.mem_range] at hd ⊢
  rcases hd with (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩) | ⟨c, hc, rfl⟩
  · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨c, hc, rfl⟩)))
  · exact Or.inl (Or.inl (Or.inr ⟨c, hc, rfl⟩))
  · exact Or.inr ⟨c, hc, rfl⟩

/-! ## Base-field facts -/

theorem isBase_mul_left {a : Fp} (ha : a ≠ 0) {w : Fp8} (h : (Fp8.ofBase a * w).IsBase) : w.IsBase := by
  obtain ⟨c, hc⟩ := (Fp8.isBase_iff _).mp h
  refine (Fp8.isBase_iff _).mpr ⟨a⁻¹ * c, ?_⟩
  rw [Fp8.ofBase_mul, ← hc, ← Semiring.mul_assoc, ← Fp8.ofBase_mul, Field.inv_mul_cancel ha]
  show w = (1 : Fp8) * w
  grind

theorem omg_mul_not_base {log : Nat} (hlog : log ≤ 27) {z : Fp8} (hz : ¬ z.IsBase) :
    ¬ (omg log * z).IsBase := fun h => hz (isBase_mul_left (Fp.twoAdicGen_ne_zero log hlog) h)

theorem pt_ne_of_not_base {z : Fp8} (hz : ¬ z.IsBase) (n0 m p : Nat) : pt n0 m p ≠ z := by
  intro h; exact hz (h ▸ (Fp8.isBase_iff _).mpr ⟨_, rfl⟩)

/-! ## The DEEP word as a `deepW` -/

section
variable (A : Air) (prm : Params)

def deepF (τ : PTn) (m : Nat) : Word Nat Fp8 := fun p j =>
  match (deepCols (layOf A prm τ) m)[j]? with
  | some (d, _) => colVal τ d p
  | none => 0

def deepZ (τ : PTn) (m : Nat) : Nat → Fp8 := fun j =>
  match (deepCols (layOf A prm τ) m)[j]? with
  | some (d, s) => if s then omg (tl A prm τ d.t).log * zOf τ else zOf τ
  | none => 0

def deepV (τ : PTn) (m : Nat) : Nat → Fp8 := fun j =>
  match (deepCols (layOf A prm τ) m)[j]? with
  | some (d, s) => claimed A prm τ d s
  | none => 0

theorem deepWord_eq (τ : PTn) (m p j : Nat) :
    deepWord A prm τ m p j = deepW (pt (n0Of A prm τ) m) (deepF A prm τ m) (deepZ A prm τ m)
      (deepV A prm τ m) p j := by
  unfold deepWord deepW deepF deepZ deepV
  split
  · next d s h => simp only [h]
  · next h => simp only [h]; grind

end

/-- Facts of the layout of a header-carrying transcript (`prm = default`). -/
structure LayOk (A : Air) (τ : PTn) : Prop where
  lde : ∀ L ∈ layOf A Params.default τ, L.lde = L.log + 4 ∧ L.lde ≤ 26

theorem eRad_facts (log : Nat) :
    2 ^ log + 1 + 2 * eRad Params.default (log + 4) ≤ 2 ^ (log + 4) ∧ 2 ^ log + 1 ≤ 2 ^ (log + 4) := by
  unfold eRad
  have e1 : 2 ^ (log + 4) = 2 ^ log * 16 := by rw [Nat.pow_add]
  have e2 : log + 4 - Params.default.logBlowup = log := rfl
  rw [e2, e1]
  have := Nat.two_pow_pos log
  omega

theorem deep_ok (A : Air) (τ : PTn) (hL : LayOk A τ) (L0 : TLayout) (hL0 : L0 ∈ layOf A Params.default τ)
    (hz : ¬ (zOf τ).IsBase)
    (hc : CloseRS (pt (n0Of A Params.default τ) L0.lde) (2 ^ L0.lde) (2 ^ L0.log) (eRad Params.default L0.lde)
      (deepWord A Params.default τ L0.lde)) :
    CloseRS (pt (n0Of A Params.default τ) L0.lde) (2 ^ L0.lde) (2 ^ L0.log + 1) (eRad Params.default L0.lde)
      (classWord A Params.default τ L0.lde 3) ∧
    ∀ d s, (d, s) ∈ deepCols (layOf A Params.default τ) L0.lde →
      colAt A Params.default τ d (if s then omg L0.log * zOf τ else zOf τ) = claimed A Params.default τ d s := by
  let prm := Params.default
  let m := L0.lde
  let log := L0.log
  let n0 := n0Of A prm τ
  let xs := pt n0 m
  have hm : m = log + 4 := (hL.lde L0 hL0).1
  have hm27 : m ≤ 27 := by have := (hL.lde L0 hL0).2; omega
  have hxs : Distinct xs (2 ^ m) := fun i j hi hj h => pt_inj hm27 hi hj h
  have hEf := eRad_facts log
  rw [← hm] at hEf
  have hD : 2 ^ log ≤ 2 ^ m := by omega
  have hD1 : 2 ^ log + 1 ≤ 2 ^ m := hEf.2
  -- the member tables of class m
  have hmem : ∀ d s, (d, s) ∈ deepCols (layOf A prm τ) m → tl A prm τ d.t = tl A prm τ d.t ∧
      (tl A prm τ d.t).lde = m ∧ (tl A prm τ d.t).log = log := fun d s h => by
    obtain ⟨L, hLd, hLm⟩ := mem_deepCols h
    have htl : tl A prm τ d.t = L := by
      unfold tl; rw [List.getD_eq_getElem?_getD, hLd]; rfl
    have := (hL.lde L (List.mem_of_getElem? hLd)).1
    rw [htl]; exact ⟨rfl, hLm, by omega⟩
  have hzpt : ∀ j i, i < 2 ^ m → xs i ≠ deepZ A prm τ m j := fun j i _ => by
    unfold deepZ
    split
    · next d s h =>
      have := hmem d s (List.mem_of_getElem? h)
      split
      · rw [this.2.2]; exact pt_ne_of_not_base (omg_mul_not_base (by omega) hz) _ _ _
      · exact pt_ne_of_not_base hz _ _ _
    · exact pt_ne_zero hm27 i
  obtain ⟨P, hP⟩ := hc
  have hq : Good (rsInterleaved xs (2 ^ m) (2 ^ log) hD hxs Nat) (eRad prm m)
      (deepW xs (deepF A prm τ m) (deepZ A prm τ m) (deepV A prm τ m)) (fun _ _ => 0) 0 := by
    refine ⟨fun p j => ev (2 ^ log) (P j) (xs p), fun j => ⟨P j, fun i _ => rfl⟩,
      Nat.le_trans (dist_mono fun i _ hne he => hne ?_) hP⟩
    funext j
    have := congrFun he j
    show deepW xs (deepF A prm τ m) (deepZ A prm τ m) (deepV A prm τ m) i j + 0 * 0 = _
    rw [← deepWord_eq, this]; grind
  obtain ⟨P', hPz, hPd⟩ := deep_close hD hD1 hxs _ _ _ hzpt hq
  -- single columns
  have hcol : ∀ j d s, (deepCols (layOf A prm τ) m)[j]? = some (d, s) →
      ∀ x, colAt A prm τ d x = ev (2 ^ log + 1) (P' j) x := fun j d s h x => by
    obtain ⟨_, h1, h2⟩ := hmem d s (List.mem_of_getElem? h)
    have hD' : 2 ^ (tl A prm τ d.t).log + 1 + 2 * eRad prm (tl A prm τ d.t).lde ≤
        2 ^ (tl A prm τ d.t).lde := by rw [h1, h2]; exact hEf.1
    have hxs' : Distinct (pt (n0Of A prm τ) (tl A prm τ d.t).lde) (2 ^ (tl A prm τ d.t).lde) := by
      rw [h1]; exact hxs
    rw [colAt_of_close τ d hD' hxs' (P' j) ?_ x, h2]
    rw [h1, h2]
    refine Nat.le_trans (dist_mono fun i _ hne he => hne ?_) hPd
    have := congrFun he j
    funext u
    simp only [deepF, h] at this
    exact this
  refine ⟨?_, fun d s hds => ?_⟩
  · refine closeRS_sub (fun j => ?_) ⟨P', hPd⟩
    unfold classWord
    cases hj : (classCols (layOf A prm τ) m 3)[j]? with
    | none => exact Or.inr fun _ => rfl
    | some d =>
      left
      obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.mp (deepCols_of_classCols (List.mem_of_getElem? hj))
      exact ⟨j', fun p => by simp only [deepF, hj']⟩
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hds
    have h1 := hcol j d s hj
    have h2 := hPz j
    have hj' : (deepCols (layOf A prm τ) m)[j]? = some (d, s) := hj
    simp only [deepZ, deepV, hj'] at h2
    rw [h1, ← h2, (hmem d s hds).2.2]

end ZkFormal.Udr.Np
