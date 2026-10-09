import ZkFormal.NearV3.Candidates.NativeAccessKeyGateCells
namespace ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly Assembly.RcptSkeleton RcptV3

def receiptMessages (pre : PTrie) (rs : List Receipt) (p : ReceiptPlan) (sd : Bool) : List Msg :=
  (choice pre p.input.receipt).toList.map (fun i=>[i,uses pre (rs.take p.receiptIndex) i+(if sd then 1 else 0)])

theorem physical_row (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accountId : ReceiptPlan→Nat)
    (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (pre : PTrie) (rs : List Receipt) (p : ReceiptPlan)
    (ha:(plannedRows lists)[pos]?=some (.receipt p ⟨sT0,0,1⟩)) (sd : Bool) :
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log constants pub digests
      (completeReceiptAux ctx k lists accountId (NativeReceiptAccessIds.accessId pre)
        (depositFinalAux previous accounts (rankAux pre rs fallback))) headerFallback) 0
    rowTraffic RcptV3.interactions tr 0 pos pub B_AKC sd=(receiptMessages pre rs p sd).map Msg.toFp := by
  intro tr
  have hg:=physical_access_cells own ctx k lists log pos constants pub digests accountId
    (NativeReceiptAccessIds.accessId pre) (depositFinalAux previous accounts (rankAux pre rs fallback)) headerFallback p ha
  have hu:=physical_uak own ctx k lists log pos constants pub digests accountId
    (NativeReceiptAccessIds.accessId pre) previous accounts fallback headerFallback pre rs p ⟨sT0,0,1⟩ ha
  rw [ReceiptCandidateProof.rowT_akc,hg.1,hg.2,hu]
  unfold receiptMessages choice
  by_cases he:(p.input.receipt.predecessorId==AccountId.system && p.input.receipt.signerId==p.input.receipt.receiverId)=true
  · cases hi:valueIndex pre (keyAccessKey p.input.receipt.receiverId p.input.receipt.signerPk) with
    | none=>simp [NativeReceiptAccessIds.accessId,hi,he,systemEqual,bitCell,ReceiptCandidateProof.gt]
    | some i=>
      cases sd <;> simp [NativeReceiptAccessIds.accessId,hi,he,systemEqual,bitCell,ReceiptCandidateProof.gt,Msg.toFp]
      · change (uses pre (rs.take p.receiptIndex) i: Fp)+(0:Nat)=(uses pre (rs.take p.receiptIndex) i: Fp)
        rw [←natCast_add]
        rfl
      · change (uses pre (rs.take p.receiptIndex) i: Fp)+1=((uses pre (rs.take p.receiptIndex) i+1:Nat):Fp)
        rw [natCast_add]
        rfl
  · simp [he,systemEqual,bitCell,ReceiptCandidateProof.gt]
end ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
