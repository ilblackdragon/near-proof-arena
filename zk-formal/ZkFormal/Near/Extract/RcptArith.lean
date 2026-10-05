import ZkFormal.Near.Extract.RcptDep

/-!
# ZkFormal.Near.Extract.RcptArith — the arithmetic facts of a receipt (`RcptV.Wf'.arith`)
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

theorem leN'_rows (f : Nat → Nat) (h : ∀ k, k < 16 → f k < 256) :
    leN' ((List.range 16).map f) = sumL f 16 := by
  rw [leN', le256_eq_leNat _ (fun y hy => by
    simp only [List.mem_map, List.mem_range] at hy; obtain ⟨k, hk, rfl⟩ := hy; exact h k hk), le256_map_range]

theorem bytes_rows (f : Nat → Nat) (h : Bytes8 ((List.range 16).map f)) : ∀ k, k < 16 → f k < 256 :=
  fun k hk => h _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)

theorem two128 : NearSpec.Params.two128 = 256 ^ 16 := by decide

theorem sumL16_lt (f : Nat → Nat) (h : ∀ k, k < 16 → f k < 256) : sumL f 16 < NearSpec.Params.two128 := by
  rw [two128]; exact sumL_lt f 16 h

theorem sumL_max (f : Nat → Nat) : ∀ L, (∀ j, j < L → f j ≤ 255) → sumL f L + 1 ≤ 256 ^ L := by
  intro L
  induction L with
  | zero => intro _; simp [sumL]
  | succ L ih =>
    intro hf
    have i1 := ih (fun j hj => hf j (by omega))
    have m1 : 256 ^ L * f L ≤ 256 ^ L * 255 := Nat.mul_le_mul_left _ (hf L (by omega))
    simp only [sumL, Nat.pow_succ]; omega

theorem sumL_max2 (f : Nat → Nat) : ∀ L, (∀ j, j < L → f j ≤ 255) → ∀ k, k < L → f k ≤ 254 →
    sumL f L + 2 ≤ 256 ^ L := by
  intro L
  induction L with
  | zero => intro _ k hk; omega
  | succ L ih =>
    intro hf k hk hfk
    have p1 : 0 < 256 ^ L := Nat.pow_pos (by omega)
    simp only [sumL, Nat.pow_succ]
    rcases Nat.lt_or_ge k L with h1 | h1
    · have i1 := ih (fun j hj => hf j (by omega)) k h1 hfk
      have m1 : 256 ^ L * f L ≤ 256 ^ L * 255 := Nat.mul_le_mul_left _ (hf L (by omega))
      omega
    · have : k = L := by omega
      subst this
      have i1 := sumL_max f k (fun j hj => hf j (by omega))
      have m1 : 256 ^ k * f k ≤ 256 ^ k * 254 := Nat.mul_le_mul_left _ hfk
      omega

theorem sumL16_notmax (f : Nat → Nat) (h : ∀ k, k < 16 → f k < 256) (k : Nat) (hk : k < 16) (hne : f k ≠ 255) :
    sumL f 16 < NearSpec.Params.u128Max := by
  have := sumL_max2 f 16 (fun j hj => Nat.le_of_lt_succ (h j hj)) k hk (by have := h k hk; omega)
  have e : NearSpec.Params.u128Max + 1 = 256 ^ 16 := by decide
  omega

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

/-- **The arithmetic of one receipt.** -/
theorem arith_of {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt)
    (hold : ∀ j, j < 16 → cv tr T_RCPT (gq s Lp Lv Ls kt 0) (tok j) < 256) :
    let x := rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩
    let bgpB := pubBytes pub PV_BGP 16
    let tok := sumL (fun j => cv tr T_RCPT (gq s Lp Lv Ls kt 0) (tok j)) 16
    let tok' := sumL (fun k => bvN tr (gq s Lp Lv Ls kt k) 31 8) 16
    Bytes8 bgpB → Bytes8 x.gp → Bytes8 x.dep → Bytes8 x.bef → Bytes8 x.lk → Bytes8 x.st →
    Bytes8 x.burnt → (x.hr = true → Bytes8 x.ramt) →
    leN' x.aft = leN' x.bef + leN' x.dep ∧ leN' x.aft < NearSpec.Params.u128Max ∧
    leN' x.aft + leN' x.lk < NearSpec.Params.two128 ∧
    ((NearSpec.Params.storageAmountPerByte * leN' x.st) % NearSpec.Params.two128 ≤ leN' x.aft + leN' x.lk ∨
      leN' x.st ≤ NearSpec.Params.zeroBalanceStorageLimit) ∧
    (x.ge = decide (leN' bgpB ≤ leN' x.gp)) ∧
    leN' x.burnt = NearSpec.Params.G * min (leN' x.gp) (leN' bgpB) ∧
    (x.hr = true ↔ NearSpec.Params.G * (leN' x.gp - min (leN' x.gp) (leN' bgpB)) ≠ 0) ∧
    (x.hr = true → leN' x.ramt = NearSpec.Params.G * (leN' x.gp - min (leN' x.gp) (leN' bgpB))) ∧
    tok' = tok + leN' x.burnt ∧ tok' < NearSpec.Params.two128 := by
  intro x bgpB tok tok' hbg hgp hdep hbef hlk hst hbu hra
  -- the view's lists are row lists
  have Xgp : x.gp = (List.range 16).map fun k => cv tr T_RCPT (gq s Lp Lv Ls kt k) b := rfl
  have Xdep : x.dep = (List.range 16).map fun k => cv tr T_RCPT (dq s Lp Lv Ls kt k) b := rfl
  have Xbef : x.bef = (List.range 16).map fun k => cv tr T_RCPT (dq s Lp Lv Ls kt k) bef := rfl
  have Xlk : x.lk = (List.range 16).map fun k => cv tr T_RCPT (dq s Lp Lv Ls kt k) lk := rfl
  have Xst : x.st = (List.range 16).map fun k => cv tr T_RCPT (dq s Lp Lv Ls kt k) st := rfl
  have Xaft : x.aft = (List.range 16).map fun k => bvN tr (dq s Lp Lv Ls kt k) 0 8 := rfl
  have Xbu : x.burnt = (List.range 16).map fun k => cv tr T_RCPT (gq s Lp Lv Ls kt k) burnt := rfl
  have Xra : x.ramt = (List.range 16).map fun k => cv tr T_RCPT (gq s Lp Lv Ls kt k) ramt := rfl
  have Xbg : bgpB = (List.range 16).map fun k => pubNat pub (PV_BGP + k) := rfl
  rw [Xgp] at hgp; rw [Xdep] at hdep; rw [Xbef] at hbef; rw [Xlk] at hlk; rw [Xst] at hst; rw [Xbu] at hbu
  rw [Xbg] at hbg
  have bgp := bytes_rows _ hgp; have bdep := bytes_rows _ hdep; have bbef := bytes_rows _ hbef
  have blk := bytes_rows _ hlk; have bst := bytes_rows _ hst; have bbu := bytes_rows _ hbu
  have bbg := bytes_rows _ hbg
  have baft : ∀ k, k < 16 → bvN tr (dq s Lp Lv Ls kt k) 0 8 < 256 := fun k hk =>
    (dep_bits hL lay k hk 0 8 (by omega)).2
  have btot : ∀ k, k < 16 → bvN tr (dq s Lp Lv Ls kt k) 9 8 < 256 := fun k hk =>
    (dep_bits hL lay k hk 9 8 (by omega)).2
  have bD : ∀ k, k < 16 → bvN tr (gq s Lp Lv Ls kt k) 0 8 < 256 := fun k hk =>
    (bitsX_eval hL (gp_row hL lay k hk).1 0 8 (by omega)).2
  have bnew : ∀ k, k < 16 → bvN tr (gq s Lp Lv Ls kt k) 31 8 < 256 := fun k hk =>
    (bitsX_eval hL (gp_row hL lay k hk).1 31 8 (by omega)).2
  rw [Xgp, Xdep, Xbef, Xlk, Xst, Xaft, Xbu, Xbg, leN'_rows _ bgp, leN'_rows _ bdep, leN'_rows _ bbef,
    leN'_rows _ blk, leN'_rows _ bst, leN'_rows _ baft, leN'_rows _ bbu, leN'_rows _ bbg]
  -- the facts
  have hA := dep_aft hL lay bbef bdep
  obtain ⟨k0, hk0, hne⟩ := dep_notmax hL lay
  have hT := dep_tot hL lay blk
  have hTlt := sumL16_lt _ btot
  have hB := gp_borrow hL lay bgp bbg
  have hDlt := sumL16_lt _ bD
  have hbu' := gp_burnt hL lay bgp bbg bbu
  have hhr := gp_hr hL lay
  have htk := gp_tok hL lay hold bbu
  have hnew := sumL16_lt _ bnew
  rw [two128] at hDlt hTlt
  -- ge
  have hs : s < tr.height T_RCPT := by have := lay.fin; have := total_pos h Lp Lv Ls kt; omega
  have hgeX : x.ge = decide (tr.cell T_RCPT s ge = 1) := rfl
  have hPN : sumL (PN tr pub s Lp Lv Ls kt) 16 = min (sumL (fun k => cv tr T_RCPT (gq s Lp Lv Ls kt k) b) 16) (sumL (fun k => pubNat pub (PV_BGP + k)) 16) := by
    rcases ge_cases hL lay with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e2] at hB
      rw [sumL_congr _ (fun k => cv tr T_RCPT (gq s Lp Lv Ls kt k) b) 16 (fun k hk => by simp [PN, e2])]
      rw [two128] at *; omega
    · rw [e2] at hB
      rw [sumL_congr _ (fun k => pubNat pub (PV_BGP + k)) 16 (fun k hk => by simp [PN, e2])]
      omega
  have hSN : sumL (SN tr s Lp Lv Ls kt) 16 = sumL (fun k => cv tr T_RCPT (gq s Lp Lv Ls kt k) b) 16 - min (sumL (fun k => cv tr T_RCPT (gq s Lp Lv Ls kt k) b) 16) (sumL (fun k => pubNat pub (PV_BGP + k)) 16) := by
    rcases ge_cases hL lay with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e2] at hB
      rw [sumL_congr _ (fun _ => 0) 16 (fun k hk => by simp [SN, e2]),
        (sumL_zero_iff (fun _ => 0) 16).mpr (fun _ _ => rfl)]
      omega
    · rw [e2] at hB
      rw [sumL_congr _ (fun k => bvN tr (gq s Lp Lv Ls kt k) 0 8) 16 (fun k hk => by simp [SN, e2])]
      omega
  have hGpos : 0 < NearSpec.Params.G := by decide
  refine ⟨hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sumL16_notmax _ baft k0 hk0 hne
  · rw [← hT]; rw [two128]; exact hTlt
  · rcases isBool hL hs (x := big) (by simp [boolCols]) with e | e
    · right; rw [NearSpec.Params.zeroBalanceStorageLimit]; exact dep_small hL lay e bst
    · left; rw [← dep_q hL lay bst, ← hT]; exact dep_cmp hL lay e
  · rw [hgeX]
    rcases ge_cases hL lay with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e2] at hB; rw [e1]; simp; omega
    · rw [e2] at hB; rw [e1]; simp; omega
  · rw [hbu', hPN]
  · show h = true ↔ _
    rw [← hSN, Nat.mul_ne_zero_iff]
    constructor
    · intro hh; refine ⟨Nat.pos_iff_ne_zero.mp hGpos, ?_⟩
      exact hhr.mp (by rw [lay.hr, hh]; rfl)
    · intro ⟨_, hne'⟩
      have := hhr.mpr hne'
      rw [lay.hr] at this; cases h <;> simp_all
  · intro hh
    have bra := bytes_rows _ (by rw [← Xra]; exact hra hh)
    rw [Xra, leN'_rows _ bra, gp_ramt hL lay bra, hSN]
  · exact htk
  · rw [two128]; exact hnew

end ZkFormal.Near.RcptProof
