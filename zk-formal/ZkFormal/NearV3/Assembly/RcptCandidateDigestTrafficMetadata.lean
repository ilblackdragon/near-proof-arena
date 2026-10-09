import ZkFormal.NearV3.Assembly.RcptCandidateDigestTrafficValues
-- Source DigestTrafficMetadata.lean SHA256: 4768394de18f7287639601e219f02248afe72dc0d11130f376c261db1b1a95ef.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.DigestTrafficValues

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

theorem Layout.refund_digest {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) (hy : y.h=true) :
    rowTraffic RcptV3.interactions tr tt (y.s+(127+Vt y.Lp y.Lv y.Ls y.kt)) pub B_DIGEST false=
      [Msg.toFp (digMsg (msgId K_RID rN) 48 (rcptOf tr tt y).rfid)] := by
  have hm : (sXRI,127+Vt y.Lp y.Lv y.Ls y.kt,32)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan,hy]
  have F := h.flds _ hm
  have hb := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  have hfin := h.fin
  simp only at hb
  have hq : y.s+(127+Vt y.Lp y.Lv y.Ls y.kt)+32≤tr.height tt := by omega
  have hs : tr.cell tt (y.s+(127+Vt y.Lp y.Lv y.Ls y.kt)) sXRI=1 := by simpa using F.fld.st 0 (by simp)
  have hf : tr.cell tt (y.s+(127+Vt y.Lp y.Lv y.Ls y.kt)) fs=1 := by simpa using F.fld.fs 0 (by simp)
  have hn : tr.cell tt (y.s+(127+Vt y.Lp y.Lv y.Ls y.kt)) RcptV3.r=(rN:Fp) := by
    simpa only [Nat.add_zero,hr] using F.consts 0 (by simp) RcptV3.r (by simp [rconsts])
  have ci := con hL (r:=y.s+(127+Vt y.Lp y.Lv y.Ls y.kt)) (by omega)
    (e:=mul3 (c fs) (c sXRI) (sub (c dI) (mid K_RID (c RcptV3.r)))) (mem_en (by simp [cEnd]))
  have cl := con hL (r:=y.s+(127+Vt y.Lp y.Lv y.Ls y.kt)) (by omega)
    (e:=mul3 (c fs) (c sXRI) (sub (c dL) (k 48))) (mem_en (by simp [cEnd]))
  simp only [eval_mul3,eval_sub,eval_c,eval_mid,eval_k,hs,hf,hn] at ci cl
  have hi : tr.cell tt (y.s+(127+Vt y.Lp y.Lv y.Ls y.kt)) dI=((msgId K_RID rN:Nat):Fp) := by
    simp only [msgId,natCast_add,natCast_mul]; grind
  have hl : tr.cell tt (y.s+(127+Vt y.Lp y.Lv y.Ls y.kt)) dL=(48:Nat) := by grind
  simpa only [rcptOf,hy,ite_true] using digest_field hL hq F.fld (Or.inl rfl) hi hl

theorem Layout.outcome_digest {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) :
    rowTraffic RcptV3.interactions tr tt (y.s+(144+32*hN y.h+Vt y.Lp y.Lv y.Ls y.kt)) pub B_DIGEST false=
      [Msg.toFp (digMsg (msgId K_PEO rN) (rcptOf tr tt y).peo.length (rcptOf tr tt y).peoh)] := by
  have hm : (sXLH,144+32*hN y.h+Vt y.Lp y.Lv y.Ls y.kt,32)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have F := h.flds _ hm
  have hb := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  have hfin := h.fin
  simp only at hb
  let q := y.s+(144+32*hN y.h+Vt y.Lp y.Lv y.Ls y.kt)
  have hq : q+32≤tr.height tt := by dsimp [q]; omega
  have hs : tr.cell tt q sXLH=1 := by simpa only [Nat.add_zero] using F.fld.st 0 (by simp)
  have hf : tr.cell tt q fs=1 := by simpa using F.fld.fs 0 (by simp)
  have hn : tr.cell tt q RcptV3.r=(rN:Fp) := by
    simpa only [Nat.add_zero,hr] using F.consts 0 (by simp) RcptV3.r (by simp [rconsts])
  have hh : tr.cell tt q RcptV3.hr=((hN y.h:Nat):Fp) := by
    have he := F.consts 0 (by simp) RcptV3.hr (by simp [rconsts])
    simp only [Nat.add_zero,h.hr] at he
    cases hy : y.h <;> simpa [q,hy,hN,natCast_eq,show Fp.ofNat 0=(0:Fp) from by decide,
      show Fp.ofNat 1=(1:Fp) from by decide] using he
  have hv : tr.cell tt q RcptV3.Lv=(y.Lv:Fp) := by
    simpa only [Nat.add_zero,h.cLv] using F.consts 0 (by simp) RcptV3.Lv LvC
  have ci := con hL (r:=q) (by omega)
    (e:=mul3 (c fs) (c sXLH) (sub (c dI) (mid K_PEO (c RcptV3.r)))) (mem_en (by simp [cEnd]))
  have cl := con hL (r:=q) (by omega)
    (e:=mul3 (c fs) (c sXLH) (sub (c dL) (sum [k 37,smul 32 (c RcptV3.hr),c RcptV3.Lv]))) (mem_en (by simp [cEnd]))
  simp only [eval_mul3,eval_sub,eval_c,eval_mid,eval_k,eval_sum_cons,eval_sum_nil,eval_smul,hs,hf,hn,hh,hv] at ci cl
  have hi : tr.cell tt q dI=((msgId K_PEO rN:Nat):Fp) := by
    simp only [msgId,natCast_add,natCast_mul]; grind
  have hl : tr.cell tt q dL=(((rcptOf tr tt y).peo.length:Nat):Fp) := by
    rw [rcptOf_peo_length]
    simp only [natCast_add,natCast_mul]
    grind
  exact digest_field hL hq F.fld (Or.inr rfl) hi hl

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
