import ZkFormal.NearV3.Candidates.NativeReceiptQueryInventory
import ZkFormal.NearV3.Rcpt.Candidates.NativeReceiptMemMetadata
namespace ZkFormal.NearV3.Candidates.NativeReceiptQueryInventory
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly RcptSkeleton RcptV3 RcptV3Proof

theorem physical_enabled (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accountId : ReceiptPlan→Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (pre post : List PlannedRow)
    (hb:plannedRows lists=pre++plannedReceiptRows p++post) :
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log
      (completeReceiptConstants ctx k accountId constants) pub digests fallback headerFallback) 0
    (rcptOf tr 0 (inputShape pre.length p.input)).ee=enabled p.input.receipt := by
  have ha:=receipt_block_lookup lists p pre post hb 0 _ (receipt_first_position p)
  simp only [Nat.add_zero] at ha
  have hc:=booleanReceiptTrace_planned_cell own ctx lists log pre.length
    (completeReceiptConstants ctx k accountId constants) pub digests fallback headerFallback _ ha
  dsimp only [rcptOf,inputShape]
  rw [RoutingQCandidate.patch_other _ _ _ ee (by decide),hc ee (by decide)]
  simp +decide only [plannedCell,receiptCell]
  change decide (boolInput ee (bitCell (systemEqual p.input.receipt))=1)=enabled p.input.receipt
  rw [boolInput_preserves _ _ (bitCell_boolean _)]
  change decide (bitCell (enabled p.input.receipt)=1)=enabled p.input.receipt
  cases enabled p.input.receipt <;> decide

theorem view_keys (pub : List Fp) (xs : List RcptE) (j i o : Nat)
    (x : RcptE) (r : Receipt)
    (ha:x.keySyms=accountKeyPath r.receiverId++[SYM_END])
    (he:x.ee=enabled r)
    (hk:enabled r=true→x.akSyms=keyAccessKey r.receiverId r.signerPk++[SYM_END]) :
    rSends pub xs j i o x B_KEYNIB=
      (receiptQueries r i).flatMap (fun q=>RcptE.keyMsgs q.wid (q.key++[SYM_END])) := by
  cases hh:enabled r <;> simp [rSends,B_KEYNIB,B_BYTES,ha,he,hh,receiptQueries,account,access,hk]

theorem physical_key_inventory (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accountId : ReceiptPlan→Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (pre post : List PlannedRow)
    (hb:plannedRows lists=pre++plannedReceiptRows p++post) (hw:p.input.receipt.wf=true)
    (xs : List RcptE) (j o : Nat) :
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log
      (completeReceiptConstants ctx k accountId constants) pub digests fallback headerFallback) 0
    rSends pub xs j p.receiptIndex o (rcptOf tr 0 (inputShape pre.length p.input)) B_KEYNIB=
      (receiptQueries p.input.receipt p.receiptIndex).flatMap
        (fun q=>RcptE.keyMsgs q.wid (q.key++[SYM_END])) := by
  apply view_keys
  · exact NativeReceiptKeySymbols.physical_account_symbols own ctx lists log _ pub digests fallback headerFallback p pre post hb
  · exact physical_enabled own ctx k lists log constants pub digests accountId fallback headerFallback p pre post hb
  · intro he
    have heq:p.input.receipt.signerId=p.input.receipt.receiverId := by
      simp only [enabled,Bool.and_eq_true,beq_iff_eq] at he
      exact he.2
    exact NativeReceiptKeySymbols.physical_access_symbols own ctx lists log _ pub digests fallback headerFallback p pre post hb hw heq

end ZkFormal.NearV3.Candidates.NativeReceiptQueryInventory
