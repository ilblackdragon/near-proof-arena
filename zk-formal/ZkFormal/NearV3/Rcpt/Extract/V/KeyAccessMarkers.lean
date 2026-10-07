import ZkFormal.NearV3.Rcpt.Extract.V.KeyAccessRows

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Separator and terminal-marker gates retain the actual first-row flag. -/
theorem key_access_marker_gates {q : Nat} (hq : q<tr.height tt) :
    (tr.cell tt q sSL=1 → tr.cell tt q gKA=tr.cell tt q ee*tr.cell tt q fs ∧
      tr.cell tt q gKB=tr.cell tt q ee*tr.cell tt q fs ∧
      wE.eval tr tt q pub=tr.cell tt q RcptV3.r+(W_AK:Nat)) ∧
    (tr.cell tt q sGP=1 → tr.cell tt q gKA=tr.cell tt q ee*tr.cell tt q fs ∧
      tr.cell tt q gKB=0 ∧ wE.eval tr tt q pub=tr.cell tt q RcptV3.r+(W_AK:Nat)) := by
  constructor <;> intro hs
  · have hz := kz_zero hL hq ((oneHot hL hq (by simp [states]) hs).2 sVL (by simp [states]) (by decide))
    obtain ⟨ha,hb,hw⟩ := key_state_gates hL hq (by simp [states]) hs
    rw [hz] at ha
    have hg := (access_key_gates (tr.cell tt q fs) (tr.cell tt q ee) (tr.cell tt q RcptV3.r)).2.1
    exact ⟨ha.trans hg.1,hb.trans hg.2.1,hw.trans hg.2.2⟩
  · have hz := kz_zero hL hq ((oneHot hL hq (by simp [states]) hs).2 sVL (by simp [states]) (by decide))
    obtain ⟨ha,hb,hw⟩ := key_state_gates hL hq (by simp [states]) hs
    rw [hz] at ha
    have hg := (access_key_gates (tr.cell tt q fs) (tr.cell tt q ee) (tr.cell tt q RcptV3.r)).2.2
    exact ⟨ha.trans hg.1,hb.trans hg.2.1,hw.trans hg.2.2⟩

/-- Non-first marker rows and all markers outside refunds emit nothing. -/
theorem key_access_marker_silent {q X : Nat} (hq : q<tr.height tt)
    (hx : X=sSL ∨ X=sGP) (hs : tr.cell tt q X=1)
    (hz : tr.cell tt q ee=0 ∨ tr.cell tt q fs=0) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=[] := by
  have hm : tr.cell tt q ee*tr.cell tt q fs=0 := by rcases hz with hz|hz <;> rw [hz] <;> grind
  rcases hx with rfl|rfl
  · obtain ⟨ha,hb,_⟩ := (key_access_marker_gates hL hq).1 hs
    rw [hm] at ha hb
    rw [rowT_key]; simp only [C]
    rw [gt_zero ha,gt_zero hb,List.nil_append]
  · obtain ⟨ha,hb,_⟩ := (key_access_marker_gates hL hq).2 hs
    rw [hm] at ha
    rw [rowT_key]; simp only [C]
    rw [gt_zero ha,gt_zero hb,List.nil_append]

/-- The signer-length first row emits the two access-key separator symbols. -/
theorem key_access_separator_row {q : Nat} (hq : q<tr.height tt)
    (hs : tr.cell tt q sSL=1) (he : tr.cell tt q ee=1) (hf : tr.cell tt q fs=1) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=
      [[tr.cell tt q RcptV3.r+(W_AK:Nat),2+2*tr.cell tt q RcptV3.Ls,0,0],
       [tr.cell tt q RcptV3.r+(W_AK:Nat),3+2*tr.cell tt q RcptV3.Ls,2,0]] := by
  obtain ⟨ha,hb,hw⟩ := (key_access_marker_gates hL hq).1 hs
  have hm : tr.cell tt q ee*tr.cell tt q fs=1 := by rw [he,hf]; decide
  rw [hm] at ha hb
  obtain ⟨ht,hy,hl,htb,hyb⟩ := (akey_row hL hq he).2.1 hs hf
  rw [rowT_key]; simp only [C]
  rw [gt_one ha,gt_one hb,hw,ht,hy,hl,htb,hyb]
  rfl

/-- The gas-price first row emits the unique access-key terminal marker. -/
theorem key_access_end_row {q : Nat} (hq : q<tr.height tt)
    (hs : tr.cell tt q sGP=1) (he : tr.cell tt q ee=1) (hf : tr.cell tt q fs=1) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=
      [[tr.cell tt q RcptV3.r+(W_AK:Nat),70+2*tr.cell tt q RcptV3.Ls+64*tr.cell tt q RcptV3.kt,(SYM_END:Nat),1]] := by
  obtain ⟨ha,hb,hw⟩ := (key_access_marker_gates hL hq).2 hs
  have hm : tr.cell tt q ee*tr.cell tt q fs=1 := by rw [he,hf]; decide
  rw [hm] at ha
  obtain ⟨ht,hy,hl⟩ := (akey_row hL hq he).2.2.2.2.2 hs hf
  rw [rowT_key]; simp only [C]
  rw [gt_one ha,gt_zero hb,hw,ht,hy,hl,List.append_nil]

end ZkFormal.NearV3.RcptV3Proof
