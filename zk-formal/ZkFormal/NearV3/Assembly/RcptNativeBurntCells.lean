import ZkFormal.NearV3.Assembly.RcptNativePeoPositions
import ZkFormal.NearV3.Assembly.RcptDepositGlobalCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

theorem complete_burnt_cell (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i : Nat) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists)
        (booleanReceiptAux (completeReceiptAux ctx k lists accountId accessId fallback)))
      p ⟨sGP,i,16⟩ burnt=Fp.ofNat (gasByte (receiptPlanToken ctx lists p).burnt i) := rfl

theorem native_burnt_slice (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (pre post : List PlannedRow)
    (hb : plannedRows lists=pre++plannedReceiptRows p++post) :
    (rcptOf (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests
        (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback) 0) 0
      (inputShape pre.length p.input)).burnt=
        (u128 (nativeOutcome ctx p.input.receipt).tokensBurnt).map UInt8.toNat := by
  change colAt _ 0 (pre.length+(78+Vt p.input.receipt.predecessorId.length p.input.receipt.receiverId.length
      p.input.receipt.signerId.length p.input.receipt.signerPk.tag)) 16 burnt=_
  apply List.ext_getElem
  · simp [colAt,u128,leN]
  · intro i h1 h2
    have hi : i<16 := by simpa [colAt] using h1
    have ha := receipt_block_lookup lists p pre post hb _ _ (receipt_gas_position p i hi)
    have hc := booleanReceiptTrace_planned_cell own ctx lists log _ constants pub digests
      (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback _ ha burnt (by decide)
    simp only [plannedCell] at hc
    rw [complete_burnt_cell] at hc
    simp only [colAt,List.getElem_map,List.getElem_range,cv]
    rw [RoutingQCandidate.patch_other _ 0 _ burnt (by decide)]
    have ht : (receiptPlanToken ctx lists p).burnt=(nativeOutcome ctx p.input.receipt).tokensBurnt := rfl
    rw [ht,gasByte_native] at hc
    have hl : i<(u128 (nativeOutcome ctx p.input.receipt).tokensBurnt).length := by simp [u128,leN];exact hi
    simp only [Vt,Nat.add_assoc,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hl,Option.getD_some] at hc ⊢
    rw [hc,native_byte_decode]

end ZkFormal.NearV3.Assembly.RcptSkeleton
