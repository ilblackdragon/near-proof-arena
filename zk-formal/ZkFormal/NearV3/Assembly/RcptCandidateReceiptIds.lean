import ZkFormal.NearV3.Assembly.RcptCandidateNameLengths
-- Source ReceiptIds.lean SHA256: 972b593e1a880d128291383c5ea615ccaa7796e8c04745fbdb72c3fa2ed9fba2.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.NameLengths

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 NearSpec
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- All three account IDs satisfy the native grammar and byte bounds. -/
theorem ids_of {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt) :
    let x := rcptOf tr tt ⟨s, h, Lp, Lv, Ls, kt⟩
    AccountId.valid (toBytes x.p) = true ∧ AccountId.valid (toBytes x.v) = true ∧
      AccountId.valid (toBytes x.s) = true ∧ Bytes8 x.p ∧ Bytes8 x.v ∧ Bytes8 x.s := by
  intro x
  have mP : (sP, 4, Lp) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have mV : (sV, 8 + Lp, Lv) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have mS : (sS, 45 + Lp + Lv, Ls) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have hfin := lay.fin
  have lP := plan_le h Lp Lv Ls kt _ mP; have lV := plan_le h Lp Lv Ls kt _ mV
  have lS := plan_le h Lp Lv Ls kt _ mS
  simp only at lP lV lS
  have FP : RFld tr tt s (s + 4) Lp sP := lay.flds _ mP
  have FV : RFld tr tt s (s + (8 + Lp)) Lv sV := lay.flds _ mV
  have FS : RFld tr tt s (s + (45 + Lp + Lv)) Ls sS := lay.flds _ mS
  have cP : ∀ k, k < Lp → tr.cell tt (s + 4 + k) RcptV3.Lp = ((Lp : Nat) : Fp) := fun k hk => by
    rw [FP.consts k hk _ LpC, lay.cLp]
  have cV : ∀ k, k < Lv → tr.cell tt (s + (8 + Lp) + k) RcptV3.Lv = ((Lv : Nat) : Fp) := fun k hk => by
    rw [FV.consts k hk _ LvC, lay.cLv]
  have cS : ∀ k, k < Ls → tr.cell tt (s + (45 + Lp + Lv) + k) RcptV3.Ls = ((Ls : Nat) : Fp) := fun k hk => by
    rw [FS.consts k hk _ LsC, lay.cLs]
  have nP := str_len hL FP (by omega) cP (mem_ch (by simp [cChars])) (mem_ch (by simp [cChars]))
  have nV := str_len hL FV (by omega) cV (mem_ch (by simp [cChars])) (mem_ch (by simp [cChars]))
  have nS := str_len hL FS (by omega) cS (mem_ch (by simp [cChars])) (mem_ch (by simp [cChars]))
  obtain ⟨vP, bP⟩ := str_valid hL (by simp) FP (by omega) nP
  obtain ⟨vV, bV⟩ := str_valid hL (by simp) FV (by omega) nV
  obtain ⟨vS, bS⟩ := str_valid hL (by simp) FS (by omega) nS
  exact ⟨vP,vV,vS,bP,bV,bS⟩

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
