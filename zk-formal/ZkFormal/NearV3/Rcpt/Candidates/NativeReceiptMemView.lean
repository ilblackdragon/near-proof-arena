import ZkFormal.NearV3.Rcpt.Candidates.NativeReceiptMemDecode
namespace ZkFormal.NearV3.Assembly.RcptSkeleton
set_option maxRecDepth 4096
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof
open ZkFormal.Near.Render RcptGen RcptP RoutingBoundedLayout

/-- The repaired receipt's extracted MEM payload uses the actual native
ledger account, not free auxiliary bytes. -/
theorem native_receipt_mem_view (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (pre post : List PlannedRow)
    (hb:plannedRows lists=pre++plannedReceiptRows p++post) (i : Nat) (hi:i<16) :
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log constants pub digests
      (completeReceiptAux ctx k lists accountId accessId (depositFinalAux previous accounts fallback)) headerFallback) 0
    let x:=rcptOf tr 0 (inputShape pre.length p.input)
    x.bef.getD i 0=(leBytes 16 (accounts p).amount).getD i 0 ∧
    x.lk.getD i 0=(leBytes 16 (accounts p).locked).getD i 0 ∧
    x.st.getD i 0=(leBytes 8 (accounts p).storageUsage).getD i 0 ∧
    x.aft.getD i 0=(leBytes 16 ((accounts p).amount+p.input.receipt.deposit)).getD i 0 := by
  have ha:=receipt_block_lookup lists p pre post hb _ _ (receipt_deposit_position p i hi)
  have hc:=native_deposit_mem_decode own ctx k lists log _ i constants pub digests accountId accessId previous accounts fallback headerFallback p ha
  dsimp only [rcptOf,inputShape]
  simp only [colAt_get _ _ _ _ _ i hi,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_range hi,Option.map_some,Option.getD_some]
  simpa only [Nat.add_assoc,List.getD_eq_getElem?_getD] using hc

end ZkFormal.NearV3.Assembly.RcptSkeleton
