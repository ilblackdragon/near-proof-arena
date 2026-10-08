import ZkFormal.NearV3.Assembly.RcptCandidateDigestTrafficSpan
-- Source DigestTrafficValues.lean SHA256: e1f8d2e7c823a7043658815907d2ed38c5a2c3137b68ddcb03277f0d91cac560.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.DigestTrafficSpan

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- The 32 loaded digest registers are exactly the 32 actual field bytes. -/
theorem digest_registers {q X : Nat} (hq : q+32≤tr.height tt) (F : Fld tr tt q 32 X)
    (hx : X∈regStates) (hn : X≠sCL) :
    regsAt tr tt q=(colAt tr tt q 32 b).map Fp.ofNat := by
  simp only [regsAt,colAt,List.map_map,Function.comp_def,cv,Fp.ofNat_toNat]
  apply List.map_congr_left
  intro k hk
  exact (fld_bytes hL hq F hx hn (by decide) k (List.mem_range.mp hk)).symm

/-- An actual digest-state field start emits exactly one digest lookup. -/
theorem digest_field {q X id len : Nat} (hq : q+32≤tr.height tt) (F : Fld tr tt q 32 X)
    (hx : X=sXRI ∨ X=sXLH) (hi : tr.cell tt q dI=(id:Fp)) (hl : tr.cell tt q dL=(len:Fp)) :
    rowTraffic RcptV3.interactions tr tt q pub B_DIGEST false=
      [Msg.toFp (digMsg id len (colAt tr tt q 32 b))] := by
  have hs : tr.cell tt q X=1 := by simpa using F.st 0 (by decide)
  have hf : tr.cell tt q fs=1 := by simpa using F.fs 0 (by decide)
  have hg := digest_gate hL (q:=q) (by omega)
  have hregs := digest_registers hL hq F (by rcases hx with rfl|rfl <;> simp [regStates])
    (by rcases hx with rfl|rfl <;> decide)
  have hxg : tr.cell tt q sXRI+tr.cell tt q sXLH=1 := by
    rcases hx with rfl|rfl
    · have ho := (oneHot hL (r:=q) (by omega) (by simp [states]) hs).2 sXLH (by simp [states]) (by decide)
      rw [hs,ho]; grind
    · have ho := (oneHot hL (r:=q) (by omega) (by simp [states]) hs).2 sXRI (by simp [states]) (by decide)
      rw [hs,ho]; grind
  have hg1 : tr.cell tt q gDg=1 := by rw [hf,hxg] at hg; grind
  rw [rowT_digest,gt_one hg1,hi,hl,hregs]
  simp [Msg.toFp,digMsg,natCast_eq]

omit hL in
/-- Partial-outcome digest input length includes its optional refund ID. -/
theorem rcptOf_peo_length (tr : Trace Fp) (tt : Nat) (y : RS) :
    (rcptOf tr tt y).peo.length=37+32*hN y.h+y.Lv := by
  simp [RcptV.peo,RcptV.borshN,rcptOf,colAt_len,u32r,G_LEn,hN]
  split <;> simp_all [colAt_len] <;> omega

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
