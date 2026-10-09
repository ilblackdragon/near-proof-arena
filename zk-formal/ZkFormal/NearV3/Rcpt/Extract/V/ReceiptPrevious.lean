import ZkFormal.NearV3.Rcpt.Extract.V.NameLengths

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Native predecessor-time ordering under the unchanged semantic no-wrap guard. -/
theorem tprev_le_of {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt) {rN : Nat}
    (hrN : tr.cell tt s RcptV3.r = (rN : Fp)) (hrP : rN < P) :
    (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).tprev < P - 512 → (rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩).tprev ≤ rN := by
  intro ht
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
  have e : ((rN : Nat) : Fp) = ((cv tr tt s tprev + bitsVal (fun j => cv tr tt (s + (107 + Vt Lp Lv Ls kt)) (xb j)) 57 9 : Nat) : Fp) := by
    rw [natCast_add]; grind
  have := ofNat_inj hrP (by simp [rcptOf] at ht; omega) e
  simp only [rcptOf]; omega


end ZkFormal.NearV3.RcptV3Proof
