import ZkFormal.NearV3.Assembly.RcptCandidateIndexedTraffic
-- Source MemoryWrites.lean SHA256: 2b863161adc107e99abf6ca89b3be1e97f12c5eeab307401ce738e11ed2730a7.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.IndexedTraffic

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def memoryWriteMsgs (r : Nat) (x : RcptE) : List Msg :=
  (List.range 16).map fun i => [x.kslot,r+1,i,x.aft.getD i 0,x.lk.getD i 0,x.st.getD i 0]

/-- Indexed memory writes agree with the unchanged semantic send API. -/
theorem memoryWriteMsgs_view (tr : Trace Fp) (tt : Nat) (pub : List Fp) (bs : List ListBlock) :
    indexedReceiptMsgs tr tt bs memoryWriteMsgs=rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_MEM := by
  rw [indexedReceiptMsgs_view]
  simp only [rcptSends3,show B_MEM≠B_BYTES by decide,show B_MEM≠B_RCL by decide,ite_false,List.nil_append]
  apply flatMap_congr'
  intro j _
  apply flatMap_congr'
  intro x _
  simp [rSends,memoryWriteMsgs,B_MEM,B_BYTES,B_KEYNIB,B_RIDS,B_MPOS]

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

omit hL in
/-- Both sides of the memory bus have the same active DEP-row gate. -/
theorem memory_write_silent {q : Nat}
    (hz : rowTraffic RcptV3.interactions tr tt q pub B_MEM false=[]) :
    rowTraffic RcptV3.interactions tr tt q pub B_MEM true=[] := by
  rw [rowT_memR] at hz
  rw [rowT_memS]
  simpa only [gt] using (show (if C tr tt q sDEP=1 then
    [[C tr tt q kslot,C tr tt q RcptV3.r+(1:Nat),C tr tt q idx,aftE.eval tr tt q pub,
      C tr tt q lk,C tr tt q st]] else [])=[] by
        split
        · simp_all [gt]
        · rfl)

/-- Whole account-memory sends exactly match every indexed extracted receipt. -/
theorem ListChain.memory_writes_view {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_MEM true)=
      (rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_MEM).map Msg.toFp := by
  rw [←memoryWriteMsgs_view]
  apply ListChain.indexed_traffic hL h
  · intro B hB
    have hh := ListBlockWf.header_memory_reads hL (h.blocks B hB)
    apply List.flatMap_eq_nil_iff.mpr
    intro q hq
    exact memory_write_silent ((List.flatMap_eq_nil_iff.mp hh) q hq)
  · intro q hq ha
    exact memory_write_silent (inactive_memory_reads hL hq ha)
  · intro j hj k hk
    have hw := (h.blocks bs[j] (List.getElem_mem hj)).layouts bs[j].receipts[k] (List.getElem_mem hk)
    exact rcpt_memS hL hw (ListChain.receipt_index hL h j hj k hk)

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
