import ZkFormal.NearV3.Assembly.RcptCandidateKeyAccountRows
-- Source KeyAccessRows.lean SHA256: 403c7cb1da63aa6d9a731e5efecded1611ff5537381ca792150852d5af2229e3.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.KeyAccountRows

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Access-key byte fields inherit exactly the refund gate and offset walk ID. -/
theorem key_access_byte_gates {q X : Nat} (hq : q<tr.height tt)
    (hx : X∈[sT0,sS,sKT,sPK]) (hs : tr.cell tt q X=1) :
    tr.cell tt q gKA=tr.cell tt q ee ∧ tr.cell tt q gKB=tr.cell tt q ee ∧
    wE.eval tr tt q pub=tr.cell tt q RcptV3.r+(W_AK:Nat) := by
  have hxs : X∈states := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> simp [states]
  have hne : sVL≠X := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> decide
  have hz := kz_zero hL hq ((oneHot hL hq hxs hs).2 sVL (by simp [states]) hne)
  obtain ⟨ha,hb,hw⟩ := key_state_gates hL hq hxs hs
  rw [hz] at ha
  have hg := (access_key_gates (tr.cell tt q fs) (tr.cell tt q ee) (tr.cell tt q RcptV3.r)).1 X hx
  exact ⟨ha.trans hg.1,hb.trans hg.2.1,hw.trans hg.2.2⟩

/-- No access byte symbols are emitted outside gas-refund receipts. -/
theorem key_access_byte_silent {q X : Nat} (hq : q<tr.height tt)
    (hx : X∈[sT0,sS,sKT,sPK]) (hs : tr.cell tt q X=1) (he : tr.cell tt q ee=0) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=[] := by
  obtain ⟨ha,hb,_⟩ := key_access_byte_gates hL hq hx hs
  rw [he] at ha hb
  rw [rowT_key]
  simp only [C]
  rw [gt_zero ha,gt_zero hb,List.nil_append]

/-- Exact two-slot access-key traffic on the type field. -/
theorem key_access_type_row {q : Nat} (hq : q<tr.height tt)
    (hs : tr.cell tt q sT0=1) (he : tr.cell tt q ee=1) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=
      [[tr.cell tt q RcptV3.r+(W_AK:Nat),0,0,0],
       [tr.cell tt q RcptV3.r+(W_AK:Nat),1,2,0]] := by
  obtain ⟨ha,hb,hw⟩ := key_access_byte_gates hL hq (by simp) hs
  rw [he] at ha hb
  obtain ⟨ht,hy,hl,htb,hyb⟩ := (akey_row hL hq he).1 hs
  rw [rowT_key]
  simp only [C]
  rw [gt_one ha,gt_one hb,hw,ht,hy,hl,htb,hyb]
  rfl

/-- Exact two-slot access-key traffic on the signer field. -/
theorem key_access_signer_row {q : Nat} (hq : q<tr.height tt)
    (hs : tr.cell tt q sS=1) (he : tr.cell tt q ee=1) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=
      [[tr.cell tt q RcptV3.r+(W_AK:Nat),2+2*tr.cell tt q idx,hiE.eval tr tt q pub,0],
       [tr.cell tt q RcptV3.r+(W_AK:Nat),3+2*tr.cell tt q idx,loE.eval tr tt q pub,0]] := by
  obtain ⟨ha,hb,hw⟩ := key_access_byte_gates hL hq (by simp) hs
  rw [he] at ha hb
  obtain ⟨ht,hy,hl,htb,hyb⟩ := (akey_row hL hq he).2.2.1 hs
  rw [rowT_key]
  simp only [C]
  rw [gt_one ha,gt_one hb,hw,ht,hy,hl,htb,hyb]
  rfl

/-- Exact two-slot access-key traffic on the kind field. -/
theorem key_access_kind_row {q : Nat} (hq : q<tr.height tt)
    (hs : tr.cell tt q sKT=1) (he : tr.cell tt q ee=1) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=
      [[tr.cell tt q RcptV3.r+(W_AK:Nat),4+2*tr.cell tt q RcptV3.Ls,0,0],
       [tr.cell tt q RcptV3.r+(W_AK:Nat),5+2*tr.cell tt q RcptV3.Ls,tr.cell tt q b,0]] := by
  obtain ⟨ha,hb,hw⟩ := key_access_byte_gates hL hq (by simp) hs
  rw [he] at ha hb
  obtain ⟨ht,hy,hl,htb,hyb⟩ := (akey_row hL hq he).2.2.2.1 hs
  rw [rowT_key]
  simp only [C]
  rw [gt_one ha,gt_one hb,hw,ht,hy,hl,htb,hyb]
  rfl

/-- Exact two-slot access-key traffic on the public key field. -/
theorem key_access_public_key_row {q : Nat} (hq : q<tr.height tt)
    (hs : tr.cell tt q sPK=1) (he : tr.cell tt q ee=1) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=
      [[tr.cell tt q RcptV3.r+(W_AK:Nat),6+2*tr.cell tt q RcptV3.Ls+2*tr.cell tt q idx,hiPK.eval tr tt q pub,0],
       [tr.cell tt q RcptV3.r+(W_AK:Nat),7+2*tr.cell tt q RcptV3.Ls+2*tr.cell tt q idx,loPK.eval tr tt q pub,0]] := by
  obtain ⟨ha,hb,hw⟩ := key_access_byte_gates hL hq (by simp) hs
  rw [he] at ha hb
  obtain ⟨ht,hy,hl,htb,hyb,_⟩ := (akey_row hL hq he).2.2.2.2.1 hs
  rw [rowT_key]
  simp only [C]
  rw [gt_one ha,gt_one hb,hw,ht,hy,hl,htb,hyb]
  rfl

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
