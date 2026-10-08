import ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
import ZkFormal.NearV3.Assembly.RcptDepositGlobalCommute
namespace ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly Assembly.RcptSkeleton RcptV3

def rankAux (pre : PTrie) (rs : List Receipt) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if col=uak then Fp.ofNat (uses pre (rs.take p.receiptIndex)
    ((valueIndex pre (keyAccessKey p.input.receipt.receiverId p.input.receipt.signerPk)).getD 0))
  else fallback p row col

theorem rankAux_eq (pre : PTrie) (rs : List Receipt) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) :
    rankAux pre rs fallback p row uak=Fp.ofNat (uses pre (rs.take p.receiptIndex)
      ((valueIndex pre (keyAccessKey p.input.receipt.receiverId p.input.receipt.signerPk)).getD 0)) := by
  simp [rankAux]

theorem complete_uak (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) :
    completeReceiptAux ctx k lists accountId accessId fallback p row uak=fallback p row uak := by
  simp +decide [completeReceiptAux,digestMetadata,characterAux,characterLengthAux,predecessorAux,
    namedAux,systemAux,routingAux,keyAux,gasBorrowAux,gasEffectiveAux,candidateGasDelayAux,
    gasFlagAux,gasTokenAux,gasProductAux]

theorem deposit_uak (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) :
    depositFinalAux previous accounts fallback p row uak=fallback p row uak := by
  simp +decide [depositFinalAux,depositAgeAux,depositAux]

theorem physical_uak (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (pre : PTrie) (rs : List Receipt) (p : ReceiptPlan) (row : Coord)
    (ha:(plannedRows lists)[pos]?=some (.receipt p row)) :
    (RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log constants pub digests
      (completeReceiptAux ctx k lists accountId accessId
        (depositFinalAux previous accounts (rankAux pre rs fallback))) headerFallback) 0).cell 0 pos uak=
      Fp.ofNat (uses pre (rs.take p.receiptIndex)
        ((valueIndex pre (keyAccessKey p.input.receipt.receiverId p.input.receipt.signerPk)).getD 0)) := by
  rw [RoutingQCandidate.patch_other _ _ _ uak (by decide)]
  rw [booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests
    (completeReceiptAux ctx k lists accountId accessId
      (depositFinalAux previous accounts (rankAux pre rs fallback))) headerFallback _ ha uak (by decide)]
  simp +decide [plannedCell,receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,boolInput]
  change completeReceiptAux ctx k lists accountId accessId
    (depositFinalAux previous accounts (rankAux pre rs fallback)) p row uak=_
  rw [complete_uak,deposit_uak,rankAux_eq]
end ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
