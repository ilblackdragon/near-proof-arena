import ZkFormal.NearV3.Assembly.RcptCandidateReceiptBalance
import ZkFormal.NearV3.Assembly.RcptCandidateGasTokens
-- ReceiptArithmetic source SHA256: 245db57e4727e1b9f21427382855647de3b99e0697e76bf5ef95a0f18b149a3f.
-- Candidate arithmetic semantics; masked surplus used only after proving non-system.
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptBalance
import ZkFormal.NearV3.Rcpt.Extract.V.GasTokens
import ZkFormal.NearV3.Rcpt.Extract.V.ListInterior

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.RcptProof (sumL sumL_congr leN'_rows bytes_rows sumL16_lt sumL16_notmax two128)
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Full arithmetic clause for the concrete V3 receipt, including system gas semantics. -/
theorem arith_of {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
    (hold : ∀ j, j < 16 → cv tr tt (gq s Lp Lv Ls kt 0) (tok j) < 256) :
    let x := rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩
    let bgpB := pubBytes pub PH_GP 16
    let tok := sumL (fun j => cv tr tt (gq s Lp Lv Ls kt 0) (tok j)) 16
    let tok' := sumL (fun k => bvN tr tt (gq s Lp Lv Ls kt k) 31 8) 16
    Bytes8 bgpB → Bytes8 x.gp → Bytes8 x.dep → Bytes8 x.bef → Bytes8 x.lk → Bytes8 x.st →
    Bytes8 x.burnt → (x.hr = true → Bytes8 x.ramt) →
    leN' x.aft = leN' x.bef + leN' x.dep ∧ leN' x.aft < NearSpec.Params.u128Max ∧
    leN' x.aft + leN' x.lk < NearSpec.Params.two128 ∧
    ((NearSpec.Params.storageAmountPerByte * leN' x.st) % NearSpec.Params.two128 ≤ leN' x.aft + leN' x.lk ∨
      leN' x.st ≤ NearSpec.Params.zeroBalanceStorageLimit) ∧
    (x.ge = decide (leN' bgpB ≤ leN' x.gp)) ∧
    leN' x.burnt = (if x.sys then 0 else NearSpec.Params.G * min (leN' x.gp) (leN' bgpB)) ∧
    (x.hr = true ↔ x.sys = false ∧ NearSpec.Params.G * (leN' x.gp - min (leN' x.gp) (leN' bgpB)) ≠ 0) ∧
    (x.hr = true → leN' x.ramt = NearSpec.Params.G * (leN' x.gp - min (leN' x.gp) (leN' bgpB))) ∧
    tok' = tok + leN' x.burnt ∧ tok' < NearSpec.Params.two128 := by
  intro x bgpB tok tok' hbg hgp hdep hbef hlk hst hbu hra
  -- the view's lists are row lists
  have Xgp : x.gp = (List.range 16).map fun k => cv tr tt (gq s Lp Lv Ls kt k) b := rfl
  have Xdep : x.dep = (List.range 16).map fun k => cv tr tt (dq s Lp Lv Ls kt k) b := rfl
  have Xbef : x.bef = (List.range 16).map fun k => cv tr tt (dq s Lp Lv Ls kt k) bef := rfl
  have Xlk : x.lk = (List.range 16).map fun k => cv tr tt (dq s Lp Lv Ls kt k) lk := rfl
  have Xst : x.st = (List.range 16).map fun k => cv tr tt (dq s Lp Lv Ls kt k) st := rfl
  have Xaft : x.aft = (List.range 16).map fun k => bvN tr tt (dq s Lp Lv Ls kt k) 0 8 := rfl
  have Xbu : x.burnt = (List.range 16).map fun k => cv tr tt (gq s Lp Lv Ls kt k) burnt := rfl
  have Xra : x.ramt = (List.range 16).map fun k => cv tr tt (gq s Lp Lv Ls kt k) ramt := rfl
  have Xbg : bgpB = (List.range 16).map fun k => pubNat pub (PH_GP + k) := rfl
  rw [Xgp] at hgp; rw [Xdep] at hdep; rw [Xbef] at hbef; rw [Xlk] at hlk; rw [Xst] at hst; rw [Xbu] at hbu
  rw [Xbg] at hbg
  have bgp := bytes_rows _ hgp; have bdep := bytes_rows _ hdep; have bbef := bytes_rows _ hbef
  have blk := bytes_rows _ hlk; have bst := bytes_rows _ hst; have bbu := bytes_rows _ hbu
  have bbg := bytes_rows _ hbg
  have baft : ∀ k, k < 16 → bvN tr tt (dq s Lp Lv Ls kt k) 0 8 < 256 := fun k hk =>
    (dep_bits hL lay k hk 0 8 (by omega)).2
  have btot : ∀ k, k < 16 → bvN tr tt (dq s Lp Lv Ls kt k) 9 8 < 256 := fun k hk =>
    (dep_bits hL lay k hk 9 8 (by omega)).2
  have bD : ∀ k, k < 16 → bvN tr tt (gq s Lp Lv Ls kt k) 0 8 < 256 := fun k hk =>
    (bitsX_eval hL (gp_row hL lay k hk).1 0 8 (by omega)).2
  have bnew : ∀ k, k < 16 → bvN tr tt (gq s Lp Lv Ls kt k) 31 8 < 256 := fun k hk =>
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
  have htk := gp_tok hL lay hold bbu
  have hnew := sumL16_lt _ bnew
  rw [two128] at hDlt hTlt
  -- ge
  have hs : s < tr.height tt := by have := lay.fin; have := total_pos h Lp Lv Ls kt; omega
  have hgeX : x.ge = decide (tr.cell tt s ge = 1) := rfl
  have hPN : sumL (PN tr tt pub s Lp Lv Ls kt) 16 = (if cv tr tt s RcptV3.sys=1 then 0 else min (sumL (fun k => cv tr tt (gq s Lp Lv Ls kt k) b) 16) (sumL (fun k => pubNat pub (PH_GP + k)) 16)) := by
    by_cases hsN : cv tr tt s RcptV3.sys=1
    · rw [if_pos hsN]
      exact (sumL_zero_iff _ 16).mpr (fun k hk => by simp [PN,hsN])
    rw [if_neg hsN]
    rcases ge_cases hL lay with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e2] at hB
      rw [sumL_congr _ (fun k => cv tr tt (gq s Lp Lv Ls kt k) b) 16 (fun k hk => by simp [PN, hsN, e2])]
      rw [two128] at *; omega
    · rw [e2] at hB
      rw [sumL_congr _ (fun k => pubNat pub (PH_GP + k)) 16 (fun k hk => by simp [PN, hsN, e2])]
      omega
  have hSN (hsysNat : cv tr tt s RcptV3.sys≠1) : sumL (SN tr tt s Lp Lv Ls kt) 16 = sumL (fun k => cv tr tt (gq s Lp Lv Ls kt k) b) 16 - min (sumL (fun k => cv tr tt (gq s Lp Lv Ls kt k) b) 16) (sumL (fun k => pubNat pub (PH_GP + k)) 16) := by
    rcases ge_cases hL lay with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e2] at hB
      rw [sumL_congr _ (fun _ => 0) 16 (fun k hk => by simp [SN, hsysNat, e2]),
        (sumL_zero_iff (fun _ => 0) 16).mpr (fun _ _ => rfl)]
      omega
    · rw [e2] at hB
      rw [sumL_congr _ (fun k => bvN tr tt (gq s Lp Lv Ls kt k) 0 8) 16 (fun k hk => by simp [SN, hsysNat, e2])]
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
  · rw [hbu',hPN]
    rcases cvb (isBool hL hs (x:=RcptV3.sys) (by simp [boolCols])) with ⟨e,n⟩|⟨e,n⟩ <;>
      simp [x,rcptOf,e,n]
  · have hsdef : x.sys=decide (tr.cell tt s RcptV3.sys=1) := rfl
    have hhrdef : x.hr=h := rfl
    rw [hhrdef,hsdef]
    rcases isBool hL hs (x:=RcptV3.sys) (by simp [boolCols]) with es|es
    · have hhr := gp_hr hL lay es
      rw [es]
      simp only [show (0:Fp)≠1 by decide,decide_false,Bool.false_eq_true,not_false_eq_true,true_and]
      rw [←hSN (by simp [cv,es,Fp.toNat_zero]),Nat.mul_ne_zero_iff]
      constructor
      · intro hh
        exact ⟨Nat.pos_iff_ne_zero.mp hGpos,hhr.mp (by rw [lay.hr,hh]; rfl)⟩
      · intro ⟨_,hne'⟩
        have hh := hhr.mpr hne'
        rw [lay.hr] at hh
        cases h <;> simp_all
    · have hfirst : tr.cell tt s sPL=1 := by
        have ff := (lay.flds (sPL,0,4) (by simp [plan])).fld.st 0 (by decide)
        simpa using ff
      have hot := oneHot hL hs (by simp [states]) hfirst
      have hcl := hot.2 sCL (by simp [states]) (by decide)
      have cc := con hL hs (e:=mul3 rowE (c RcptV3.sys) (c RcptV3.hr)) (mem_sy (by simp [cSys]))
      simp only [rowE,eval_mul3,eval_sub,eval_c] at cc
      rw [hot.1,hcl,es,lay.hr] at cc
      have hh : h=false := by cases h <;> grind
      rw [hh,es]
      simp
  · intro hh
    have bra := bytes_rows _ (by rw [← Xra]; exact hra hh)
    have hhr : tr.cell tt s RcptV3.hr=1 := by rw [lay.hr];change (if h then (1:Fp) else 0)=1;change h=true at hh;rw [hh];rfl
    have hsysNat : cv tr tt s RcptV3.sys≠1 := by
      have hfirst : tr.cell tt s sPL=1 := by
        have ff := (lay.flds (sPL,0,4) (by simp [plan])).fld.st 0 (by decide)
        simpa using ff
      have hot := oneHot hL hs (by simp [states]) hfirst
      have hcl := hot.2 sCL (by simp [states]) (by decide)
      have cc := con hL hs (mem_sy (show mul3 rowE (c RcptV3.sys) (c RcptV3.hr)∈cSys by simp [cSys]))
      simp only [rowE,eval_mul3,eval_sub,eval_c,hot.1,hcl,hhr] at cc
      have hz : tr.cell tt s RcptV3.sys=0 := by grind
      simp [cv,hz,Fp.toNat_zero]
    rw [Xra, leN'_rows _ bra, gp_ramt hL lay bra, hSN hsysNat]
  · exact htk
  · rw [two128]; exact hnew


end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
