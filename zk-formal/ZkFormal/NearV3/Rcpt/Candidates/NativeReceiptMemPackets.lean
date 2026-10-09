import ZkFormal.NearV3.Rcpt.Candidates.NativeReceiptMemMetadata
namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof Render

def depositMemPackets (vid time amount locked storage : Nat) : List ZkFormal.Near.Msg :=
  (List.range 16).map (fun lane=>[vid,time,lane,(leBytes 16 amount).getD lane 0,
    (leBytes 16 locked).getD lane 0,if lane<8 then (leBytes 8 storage).getD lane 0 else 0])

private theorem mem_packets_fields (pub : List Fp) (xs : List RcptE) (j r o : Nat)
    (x : RcptE) (vid previous amount deposit locked storage : Nat)
    (hk:x.kslot=vid) (ht:x.tprev=previous)
    (hf:∀i,i<16→x.bef.getD i 0=(leBytes 16 amount).getD i 0 ∧
      x.lk.getD i 0=(leBytes 16 locked).getD i 0 ∧
      x.st.getD i 0=(leBytes 8 storage).getD i 0 ∧
      x.aft.getD i 0=(leBytes 16 (amount+deposit)).getD i 0) :
    rSends pub xs j r o x B_MEM=depositMemPackets vid (r+1) (amount+deposit) locked storage ∧
    rRecvs r x B_MEM=depositMemPackets vid previous amount locked storage := by
  simp only [rSends,rRecvs,depositMemPackets,B_MEM,B_BYTES,B_KEYNIB,B_DIGEST,B_FINAL,
    Nat.reduceEqDiff,if_false,if_true]
  constructor <;> apply List.map_congr_left <;> intro i hi
  all_goals
    have hh:=hf i (List.mem_range.mp hi)
    rw [hk,hh.2.1,hh.2.2.1]
    first | rw [hh.2.2.2] | rw [ht,hh.1]
    by_cases h8:i<8
    · simp only [h8,if_true]
    · have hz:(leBytes 8 storage).getD i 0=0:=by rw [RcptP.leBytes_getD,if_neg h8]
      simp only [h8,if_false,hz]

/-- Exact MEM send/read packets for each physical repaired receipt block. -/
theorem native_receipt_mem_packets (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (pre post : List PlannedRow)
    (hb:plannedRows lists=pre++plannedReceiptRows p++post)
    (hid:accountId p<Algebra.P) (ht:previous p<Algebra.P) (xs : List RcptE) (j o : Nat) :
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log
      (completeReceiptConstants ctx k accountId (depositConstants accounts (depositAgeConstants previous constants))) pub digests
      (completeReceiptAux ctx k lists accountId accessId (depositFinalAux previous accounts fallback)) headerFallback) 0
    let x:=rcptOf tr 0 (inputShape pre.length p.input)
    rSends pub xs j p.receiptIndex o x B_MEM=
      depositMemPackets (accountId p) (p.receiptIndex+1) ((accounts p).amount+p.input.receipt.deposit)
        (accounts p).locked (accounts p).storageUsage ∧
    rRecvs p.receiptIndex x B_MEM=
      depositMemPackets (accountId p) (previous p) (accounts p).amount (accounts p).locked (accounts p).storageUsage := by
  have hm:=native_receipt_mem_metadata own ctx k lists log constants pub digests accountId accessId previous accounts fallback headerFallback p pre post hb hid ht
  apply mem_packets_fields pub xs j p.receiptIndex o _ _ _ _ _ _ _ hm.1 hm.2
  exact native_receipt_mem_view own ctx k lists log
    (completeReceiptConstants ctx k accountId (depositConstants accounts (depositAgeConstants previous constants)))
    pub digests accountId accessId previous accounts fallback headerFallback p pre post hb

end ZkFormal.NearV3.Assembly.RcptSkeleton
