import ZkFormal.NearV3.Rcpt.Candidates.NativeReceiptMemCells
namespace ZkFormal.NearV3.Assembly.RcptSkeleton
set_option maxRecDepth 4096
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof
open ZkFormal.Near.Render RcptGen RcptP RoutingBoundedLayout

private theorem decode_mem_byte (x : Nat) (hx:x<256) : (Fp.ofNat x).toNat=x := by
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt]
  unfold Algebra.P
  omega

/-- No-wrap decoding of the actual native deposit cells, including the
reconstructed post-amount byte from eight physical bits. -/
theorem native_deposit_mem_decode (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log pos i : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (ha:(plannedRows lists)[pos]?=some (.receipt p ⟨sDEP,i,16⟩)) :
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log constants pub digests
      (completeReceiptAux ctx k lists accountId accessId (depositFinalAux previous accounts fallback)) headerFallback) 0
    cv tr 0 pos bef=(leBytes 16 (accounts p).amount).getD i 0 ∧
    cv tr 0 pos lk=(leBytes 16 (accounts p).locked).getD i 0 ∧
    cv tr 0 pos st=(leBytes 8 (accounts p).storageUsage).getD i 0 ∧
    bitsVal (fun j=>cv tr 0 pos (xb j)) 0 8=(leBytes 16 ((accounts p).amount+p.input.receipt.deposit)).getD i 0 := by
  have hc:=native_deposit_mem_cells own ctx k lists log pos i constants pub digests accountId accessId previous accounts fallback headerFallback p ha
  have hb:=native_deposit_mem_bit own ctx k lists log pos i constants pub digests accountId accessId previous accounts fallback headerFallback p ha
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · unfold cv
    rw [hc.1]
    exact decode_mem_byte _ (leBytes_getD_lt 16 _ i)
  · unfold cv
    rw [hc.2.1]
    exact decode_mem_byte _ (leBytes_getD_lt 16 _ i)
  · unfold cv
    rw [hc.2.2]
    exact decode_mem_byte _ (leBytes_getD_lt 8 _ i)
  · rw [RcptP.bitsVal_congr 0 8 (fun j hj=>by
      simp only [Nat.zero_add,cv,hb j hj,frameBit]
      apply decode_mem_byte
      omega)]
    rw [frame_bitsVal]
    exact Nat.mod_eq_of_lt (leBytes_getD_lt 16 _ i)

end ZkFormal.NearV3.Assembly.RcptSkeleton
