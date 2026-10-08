import ZkFormal.NearV3.Candidates.NativeAccessKeyRankAux
import ZkFormal.NearV3.Assembly.RcptCandidateAccessTrafficRows
namespace ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly Assembly.RcptSkeleton RcptV3
set_option maxRecDepth 4096

private theorem complete_access_cells (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) :
    completeReceiptAux ctx k lists accountId accessId fallback p ⟨sT0,0,1⟩ gAK=
      bitCell (systemEqual p.input.receipt && !(accessId p).isNone) ∧
    completeReceiptAux ctx k lists accountId accessId fallback p ⟨sT0,0,1⟩ kF=
      Fp.ofNat ((accessId p).getD 0) := by
  simp +decide [completeReceiptAux,digestMetadata,characterAux,characterLengthAux,predecessorAux,
    namedAux,systemAux,routingAux,keyAux]

theorem physical_access_cells (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (ha:(plannedRows lists)[pos]?=some (.receipt p ⟨sT0,0,1⟩)) :
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log constants pub digests
      (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback) 0
    tr.cell 0 pos gAK=bitCell (systemEqual p.input.receipt && !(accessId p).isNone) ∧
    tr.cell 0 pos kF=Fp.ofNat ((accessId p).getD 0) := by
  have hg:=complete_access_cells ctx k lists accountId accessId fallback p
  have hh:=booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests
    (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback _ ha
  constructor
  · rw [RoutingQCandidate.patch_other _ _ _ gAK (by decide),hh gAK (by decide)]
    simp +decide [plannedCell,receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux]
    rw [hg.1]
    simpa using boolInput_preserves gAK _ (bitCell_boolean (systemEqual p.input.receipt && !(accessId p).isNone))
  · rw [RoutingQCandidate.patch_other _ _ _ kF (by decide),hh kF (by decide)]
    simp +decide [plannedCell,receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,boolInput]
    exact hg.2
end ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
