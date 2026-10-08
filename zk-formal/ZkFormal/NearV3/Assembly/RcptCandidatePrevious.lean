import ZkFormal.NearV3.Assembly.RcptCandidateLayout
import ZkFormal.NearV3.Assembly.RcptCandidateBounds

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RcptSkeleton
open RcptV3Proof (Layout Vt plan plan_le rcptOf RFld)
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- Previous-version order for the concrete extracted receipt. The explicit
provider version bound must come from authenticated MEM ownership. -/
theorem previous_of_provider_bound (hL : TableLocal receiptArithmeticCandidate tr tt pub)
    {s : Nat} {h : Bool} {Lp Lv Ls kt rN : Nat}
    (lay : Layout tr tt s h Lp Lv Ls kt)
    (hrN : tr.cell tt s r=(rN:Fp)) (hrP : rN<P)
    (ht : (rcptOf tr tt ⟨s,h,Lp,Lv,Ls,kt⟩).tprev≤2^22) :
    (rcptOf tr tt ⟨s,h,Lp,Lv,Ls,kt⟩).tprev≤rN := by
  have hm : (sDEP,107+Vt Lp Lv Ls kt,16)∈plan h Lp Lv Ls kt := by simp [plan]
  have hle := plan_le h Lp Lv Ls kt _ hm
  have hf := lay.fin
  have F : RFld tr tt s (s+(107+Vt Lp Lv Ls kt)) 16 sDEP := lay.flds _ hm
  have hpos : s+(107+Vt Lp Lv Ls kt)<tr.height tt := by simp at hle;omega
  have hd : tr.cell tt (s+(107+Vt Lp Lv Ls kt)) sDEP=1 := by simpa using F.fld.st 0 (by decide)
  have hfs : tr.cell tt (s+(107+Vt Lp Lv Ls kt)) fs=1 := by simpa using F.fld.fs 0 (by decide)
  have hr0 := F.consts 0 (by decide) r (by simp [rconsts])
  have ht0 := F.consts 0 (by decide) tprev (by simp [rconsts])
  simp only [Nat.add_zero] at hr0 ht0
  have hpv : cv tr tt (s+(107+Vt Lp Lv Ls kt)) tprev≤2^22 := by
    simpa only [rcptOf,cv,ht0] using ht
  have horder := deposit_previous_provider_bound hL hpos hd hfs hpv
  simp only [cv,ht0,hr0,hrN,toNat_natCast,Nat.mod_eq_of_lt hrP] at horder
  exact horder

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
