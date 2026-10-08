import ZkFormal.NearV3.Assembly.RcptCandidateDeposit
import ZkFormal.NearV3.Assembly.RcptCandidateGasTokens
-- ReceiptBalance source SHA256: 936291fba22eccc1338e66aa872c790c8d658968a047e7cb740bc28ef10b8623.
-- Candidate arithmetic semantics; masked surplus used only after proving non-system.
import ZkFormal.NearV3.Rcpt.Extract.V.Deposit
import ZkFormal.Near.Extract.RcptArith

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.RcptProof (sumL leN'_rows bytes_rows sumL16_lt sumL16_notmax two128)
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- All balance and storage clauses of the exact V3 receipt arithmetic view. -/
theorem balance_of (hL : TableLocal receiptArithmeticCandidate tr tt pub) {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat}
    (lay : Layout tr tt s h Lp Lv Ls kt) :
    let x := rcptOf tr tt ⟨s,h,Lp,Lv,Ls,kt⟩
    Bytes8 x.dep → Bytes8 x.bef → Bytes8 x.lk → Bytes8 x.st →
    leN' x.aft=leN' x.bef+leN' x.dep ∧ leN' x.aft<NearSpec.Params.u128Max ∧
    leN' x.aft+leN' x.lk<NearSpec.Params.two128 ∧
    ((NearSpec.Params.storageAmountPerByte*leN' x.st)%NearSpec.Params.two128≤leN' x.aft+leN' x.lk ∨
      leN' x.st≤NearSpec.Params.zeroBalanceStorageLimit) := by
  intro x hdep hbef hlk hst
  have Xdep : x.dep=(List.range 16).map fun k => cv tr tt (dq s Lp Lv Ls kt k) b := rfl
  have Xbef : x.bef=(List.range 16).map fun k => cv tr tt (dq s Lp Lv Ls kt k) bef := rfl
  have Xlk : x.lk=(List.range 16).map fun k => cv tr tt (dq s Lp Lv Ls kt k) lk := rfl
  have Xst : x.st=(List.range 16).map fun k => cv tr tt (dq s Lp Lv Ls kt k) st := rfl
  have Xaft : x.aft=(List.range 16).map fun k => bvN tr tt (dq s Lp Lv Ls kt k) 0 8 := rfl
  rw [Xdep] at hdep
  rw [Xbef] at hbef
  rw [Xlk] at hlk
  rw [Xst] at hst
  have bd := bytes_rows _ hdep
  have bb := bytes_rows _ hbef
  have bl := bytes_rows _ hlk
  have bs := bytes_rows _ hst
  have ba : ∀ k,k<16 → bvN tr tt (dq s Lp Lv Ls kt k) 0 8<256 := fun k hk =>
    (dep_bits hL lay k hk 0 8 (by omega)).2
  have bt : ∀ k,k<16 → bvN tr tt (dq s Lp Lv Ls kt k) 9 8<256 := fun k hk =>
    (dep_bits hL lay k hk 9 8 (by omega)).2
  rw [Xdep,Xbef,Xlk,Xst,Xaft,leN'_rows _ bd,leN'_rows _ bb,leN'_rows _ bl,leN'_rows _ bs,leN'_rows _ ba]
  have hA := dep_aft hL lay bb bd
  obtain ⟨k,hk,hne⟩ := dep_notmax hL lay
  have hT := dep_tot hL lay bl
  have hTlt := sumL16_lt _ bt
  have hs : s<tr.height tt := by have := lay.fin; have := total_pos h Lp Lv Ls kt; omega
  refine ⟨hA,sumL16_notmax _ ba k hk hne,?_,?_⟩
  · rw [←hT]
    exact hTlt
  · rcases isBool hL hs (x:=big) (by simp [boolCols]) with e|e
    · right
      rw [NearSpec.Params.zeroBalanceStorageLimit]
      exact dep_small hL lay e bs
    · left
      rw [←dep_q hL lay bs,←hT]
      exact dep_cmp hL lay e

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
