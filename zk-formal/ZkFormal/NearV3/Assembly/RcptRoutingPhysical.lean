import ZkFormal.NearV3.Assembly.RcptRoutingPhysicalReceiver

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

theorem planned_header_state (lists : List (List Input)) (p : ListPlan) (row : Coord)
    (ha : PlannedRow.header p row∈plannedRows lists) : row.state=sCL := by
  rw [←plannedSegments_rows] at ha
  obtain ⟨seg,_,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨coord,hc,he⟩ := List.mem_map.mp ha
  have hs := (segment_member hc).1
  cases seg with
  | header lp => cases he; exact hs
  | receipt => cases he

theorem booleanReceiptTrace_route (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length≤2^log)
    (hv : ∀p,p.input∈lists.flatten→inInterval p.input.receipt.receiverId (interval p)=true)
    (hu : ∀p,p.input∈lists.flatten→∀v∈(interval p).2.getD [],0<v.toNat) :
    ∀e∈cRoute,e.eval (booleanReceiptTrace own ctx lists log constants pub digests
      (routingAux interval fallback) (routingHeaderAux headerFallback)) 0 pos pub=0 := by
  let tr := booleanReceiptTrace own ctx lists log constants pub digests
    (routingAux interval fallback) (routingHeaderAux headerFallback)
  change ∀e∈cRoute,e.eval tr 0 pos pub=0
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    have hh := booleanReceiptTrace_padding own ctx lists log pos constants pub digests
      (routingAux interval fallback) (routingHeaderAux headerFallback) ha
    apply routing_inactive tr 0 pos pub (hh sV) ?_ (hh gBd)
    rw [hh sRID];grind only
  | some a =>
    have hc := booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests
      (routingAux interval fallback) (routingHeaderAux headerFallback) a ha
    cases a with
    | header p row =>
      have hs := planned_header_state lists p row (List.mem_of_getElem? ha)
      have hsv : tr.cell 0 pos sV=0 := (hc sV (by decide)).trans (by
        change (if sV=row.state then (1:Fp) else 0)=0
        rw [hs];rfl)
      have hsr : tr.cell 0 pos sRID=0 := (hc sRID (by decide)).trans (by
        change (if sRID=row.state then (1:Fp) else 0)=0
        rw [hs];rfl)
      have hg : tr.cell 0 pos gBd=0 := (hc gBd (by decide)).trans (by
        change boolInput gBd 0=0
        exact boolInput_preserves _ _ (Or.inl rfl))
      apply routing_inactive tr 0 pos pub hsv ?_ hg
      rw [hsr];grind only
    | receipt p row =>
      have hm := planned_receipt_input_mem lists p row (List.mem_of_getElem? ha)
      by_cases hs : row.state=sV
      · have hl := planned_receipt_field_length lists p row (List.mem_of_getElem? ha)
        rw [hs] at hl
        change row.length=p.input.receipt.receiverId.length at hl
        cases row with
        | mk state i len =>
          dsimp only at hs hl
          subst state len
          exact booleanReceiptTrace_receiver_route own ctx lists hw log pos constants pub digests
            interval fallback headerFallback p i ha hcap (hv p hm) (hu p hm)
      · by_cases hr : row.state=sRID ∧ row.index=0
        · cases row with
          | mk state i len =>
            obtain ⟨hs',hi⟩ := hr
            dsimp only at hs' hi
            subst state i
            intro e he
            let pair := receiptPair (booleanConstants constants)
              (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (routingAux interval fallback)))
              p ⟨sRID,0,len⟩ ⟨sRID,0,len⟩
            have heq := routing_no_next tr pair 0 pos 0 0 pub
              (fun col hh=>hc col (routing_no_emission col hh)) ((hc sV (by decide)).trans rfl) e he
            exact heq.trans (routing_rid_local interval constants pub digests (receiptPlanToken ctx lists)
              fallback p len _ (hv p hm) (hu p hm) e he)
        · have hact : routingActive row=false := by
            simp only [routingActive,Bool.or_eq_false_iff,Bool.and_eq_false_iff,beq_eq_false_iff_ne]
            exact ⟨hs,by grind only⟩
          have hh := routing_inactive_cells interval constants pub digests (receiptPlanToken ctx lists) fallback p row hact
          apply routing_inactive tr 0 pos pub ((hc sV (by decide)).trans hh.1) ?_ ((hc gBd (by decide)).trans hh.2.2)
          rw [hc sRID (by decide),hc fs (by decide)]
          exact hh.2.1

end ZkFormal.NearV3.Assembly.RcptSkeleton
