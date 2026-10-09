import ZkFormal.NearV3.Rcpt.Extract.V.KeyTrafficGates

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- The receiver field emits exactly its two constrained nibble slots. -/
theorem key_receiver_row {q : Nat} (hq : q<tr.height tt) (hs : tr.cell tt q sV=1) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=
    [[tr.cell tt q RcptV3.r,2+2*tr.cell tt q idx,hiE.eval tr tt q pub,0],
     [tr.cell tt q RcptV3.r,3+2*tr.cell tt q idx,loE.eval tr tt q pub,0]] := by
  have hz := kz_zero hL hq ((oneHot hL hq (by simp [states]) hs).2 sVL (by simp [states]) (by decide))
  obtain ⟨ha,hb,hw⟩ := key_state_gates hL hq (by simp [states]) hs
  rw [hz] at ha
  have hg := (account_key_gates (tr.cell tt q fs) 0 (tr.cell tt q ee) (tr.cell tt q RcptV3.r)).2.1
  rw [hg.1] at ha
  rw [hg.2.1] at hb
  rw [hg.2.2] at hw
  obtain ⟨ht,hy,hl⟩ := (key_row hL hq).2.1 hs
  obtain ⟨htb,hyb⟩ := keyB_V hL hq hs
  rw [rowT_key]
  simp only [C]
  rw [gt_one ha,gt_one hb,hw,ht,hy,hl,htb,hyb]
  rfl

/-- The length-prefix gate emits a zero symbol at the constrained byte index. -/
theorem key_receiver_prefix_row {q : Nat} (hq : q<tr.height tt)
    (hs : tr.cell tt q sVL=1) (hz : tr.cell tt q kz=1) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=
      [[tr.cell tt q RcptV3.r,tr.cell tt q idx,0,0]] := by
  obtain ⟨ha,hb,hw⟩ := key_state_gates hL hq (by simp [states]) hs
  have hg := (account_key_gates (tr.cell tt q fs) (tr.cell tt q kz) (tr.cell tt q ee) (tr.cell tt q RcptV3.r)).1
  rw [hg.1,hz] at ha
  rw [hg.2.1] at hb
  rw [hg.2.2] at hw
  obtain ⟨ht,hy,hl,_⟩ := (key_row hL hq).2.2.1 hz
  rw [rowT_key]
  simp only [C]
  rw [gt_one ha,gt_zero hb,hw,ht,hy,hl,List.append_nil]

/-- Remaining receiver-length rows emit no key symbols. -/
theorem key_receiver_prefix_silent {q : Nat} (hq : q<tr.height tt)
    (hs : tr.cell tt q sVL=1) (hz : tr.cell tt q kz=0) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=[] := by
  obtain ⟨ha,hb,_⟩ := key_state_gates hL hq (by simp [states]) hs
  have hg := (account_key_gates (tr.cell tt q fs) (tr.cell tt q kz) (tr.cell tt q ee) 0).1
  rw [hg.1,hz] at ha
  rw [hg.2.1] at hb
  rw [rowT_key]
  simp only [C]
  rw [gt_zero ha,gt_zero hb,List.nil_append]

/-- Only the first receipt-ID row emits the account-key terminal marker. -/
theorem key_receiver_end_row {q : Nat} (hq : q<tr.height tt)
    (hs : tr.cell tt q sRID=1) (hf : tr.cell tt q fs=1) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=
      [[tr.cell tt q RcptV3.r,2+2*tr.cell tt q RcptV3.Lv,(SYM_END:Nat),1]] := by
  have hz := kz_zero hL hq ((oneHot hL hq (by simp [states]) hs).2 sVL (by simp [states]) (by decide))
  obtain ⟨ha,hb,hw⟩ := key_state_gates hL hq (by simp [states]) hs
  rw [hz] at ha
  have hg := (account_key_gates (tr.cell tt q fs) 0 (tr.cell tt q ee) (tr.cell tt q RcptV3.r)).2.2
  rw [hg.1,hf] at ha
  rw [hg.2.1] at hb
  rw [hg.2.2] at hw
  obtain ⟨ht,hy,hl⟩ := (key_row hL hq).2.2.2.1 hs hf
  rw [rowT_key]
  simp only [C]
  rw [gt_one ha,gt_zero hb,hw,ht,hy,hl,List.append_nil]

/-- Later receipt-ID rows cannot emit account-key markers. -/
theorem key_receiver_end_silent {q : Nat} (hq : q<tr.height tt)
    (hs : tr.cell tt q sRID=1) (hf : tr.cell tt q fs=0) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=[] := by
  have hz := kz_zero hL hq ((oneHot hL hq (by simp [states]) hs).2 sVL (by simp [states]) (by decide))
  obtain ⟨ha,hb,_⟩ := key_state_gates hL hq (by simp [states]) hs
  rw [hz] at ha
  have hg := (account_key_gates (tr.cell tt q fs) 0 (tr.cell tt q ee) 0).2.2
  rw [hg.1,hf] at ha
  rw [hg.2.1] at hb
  rw [rowT_key]
  simp only [C]
  rw [gt_zero ha,gt_zero hb,List.nil_append]

end ZkFormal.NearV3.RcptV3Proof
