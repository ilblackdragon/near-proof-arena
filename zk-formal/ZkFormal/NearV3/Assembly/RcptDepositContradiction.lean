import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptPrevious

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RcptV3Proof

/-- The old version-distance equation cannot encode receipt index512 reading
an authenticated initial account version0. This is a local obstruction,
not an assertion of a full accepted transition fixture. -/
theorem old_deposit_initial_512_impossible {tr : Trace Fp} {pub : List Fp} {tt s : Nat}
    {h : Bool} {Lp Lv Ls kt : Nat} (hL : TableLocal RcptV3.table tr tt pub)
    (lay : Layout tr tt s h Lp Lv Ls kt)
    (hrN : tr.cell tt s RcptV3.r=(512:Fp)) (htprev : cv tr tt s tprev=0) : False := by
  have hm : (sDEP, 107 + Vt Lp Lv Ls kt, 16) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have hle := plan_le h Lp Lv Ls kt _ hm
  have hfin := lay.fin
  have F : RFld tr tt s (s + (107 + Vt Lp Lv Ls kt)) 16 sDEP := lay.flds _ hm
  have hq : s + (107 + Vt Lp Lv Ls kt) < tr.height tt := by simp at hle; omega
  have c := con hL hq (e := mul3 dp (c fs) (sub (sub (c RcptV3.r) (c tprev)) (bitsX 57 9))) (mem_dp (by simp [cDep]))
  have h1 : tr.cell tt (s + (107 + Vt Lp Lv Ls kt)) sDEP = 1 := by simpa using F.fld.st 0 (by omega)
  have hfs : tr.cell tt (s + (107 + Vt Lp Lv Ls kt)) fs = 1 := by simpa using F.fld.fs 0 (by omega)
  have hr0 := F.consts 0 (by omega) _ rC
  have ht0 := F.consts 0 (by omega) tprev (by simp [rconsts])
  simp only [Nat.add_zero] at hr0 ht0
  obtain ⟨be, bl⟩ := bitsX_eval hL hq 57 9 (by omega)
  simp only [dp, eval_mul3, eval_c, eval_sub] at c
  rw [h1, hfs, be, hr0, ht0, hrN, cell_eq_cast tr tt s tprev] at c
  rw [htprev] at c
  have e : ((512:Nat):Fp) = ((bitsVal (fun j=>cv tr tt (s+(107+Vt Lp Lv Ls kt)) (xb j)) 57 9:Nat):Fp) := by
    grind only
  have := ofNat_inj (by decide : 512<ZkFormal.Algebra.P) (by unfold ZkFormal.Algebra.P; omega) e
  omega

end ZkFormal.NearV3.Assembly.RcptSkeleton
