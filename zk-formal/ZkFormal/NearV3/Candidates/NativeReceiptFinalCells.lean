import ZkFormal.NearV3.Candidates.NativeReceiptQueryGate
import ZkFormal.NearV3.Candidates.NativeAccessKeyGateCells
import ZkFormal.NearV3.Candidates.NativeAccessKeyView
namespace ZkFormal.NearV3.Candidates.NativeReceiptQueryInventory
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly RcptSkeleton RcptV3 RcptV3Proof
set_option maxRecDepth 4096

theorem physical_access_final (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (pre post : List PlannedRow)
    (hb:plannedRows lists=pre++plannedReceiptRows p++post) (hi:(accessId p).getD 0<Algebra.P) :
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log constants pub digests
      (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback) 0
    let x:=rcptOf tr 0 (inputShape pre.length p.input)
    x.akf=(if (accessId p).isSome then FK_VAL else FK_ABS) ∧ x.akk=(accessId p).getD 0 := by
  have ha:=receipt_block_lookup lists p pre post hb _ _ (NativeAccessKeyRanks.receipt_t0_position p)
  have hc:=booleanReceiptTrace_planned_cell own ctx lists log _ constants pub digests
    (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback _ ha
  have hk:=NativeAccessKeyRanks.physical_access_cells own ctx k lists log _ constants pub digests accountId accessId fallback headerFallback p ha
  dsimp only [rcptOf,inputShape]
  constructor
  · unfold cv
    rw [RoutingQCandidate.patch_other _ _ _ fkF (by decide),hc fkF (by decide)]
    simp +decide [plannedCell,receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,
      completeReceiptAux,digestMetadata,characterAux,characterLengthAux,predecessorAux,
      namedAux,systemAux,routingAux,keyAux]
    cases accessId p <;> rfl
  · change ((RoutingQCandidate.patchTrace _ 0).cell 0 _ kF).toNat = _
    rw [hk.2,Fp.toNat_ofNat,Nat.mod_eq_of_lt hi]

theorem physical_account_final (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accountId : ReceiptPlan→Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (pre post : List PlannedRow)
    (hb:plannedRows lists=pre++plannedReceiptRows p++post) (hi:accountId p<Algebra.P) :
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log
      (completeReceiptConstants ctx k accountId constants) pub digests fallback headerFallback) 0
    (rcptOf tr 0 (inputShape pre.length p.input)).kslot=accountId p := by
  have ha:=receipt_block_lookup lists p pre post hb 0 _ (receipt_first_position p)
  simp only [Nat.add_zero] at ha
  have hc:=booleanReceiptTrace_planned_cell own ctx lists log pre.length
    (completeReceiptConstants ctx k accountId constants) pub digests fallback headerFallback _ ha
  dsimp only [rcptOf,inputShape]
  unfold cv
  rw [RoutingQCandidate.patch_other _ _ _ kslot (by decide),hc kslot (by decide)]
  change (Fp.ofNat (accountId p)).toNat=accountId p
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hi]
end ZkFormal.NearV3.Candidates.NativeReceiptQueryInventory
