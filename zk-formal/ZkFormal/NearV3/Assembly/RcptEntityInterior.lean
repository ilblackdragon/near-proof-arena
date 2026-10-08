import ZkFormal.NearV3.Assembly.RcptEntityRows

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 RcptV3

theorem fields_end_final (refund : Bool) : ∀s∈fields refund,
    (s==sXRZ || (s==sXLH && !refund))=true→s=(if refund then sXRZ else sXLH) := by
  cases refund <;> decide

theorem fields_next_not_final (refund : Bool) :
    ∀p∈(fields refund).zip ((fields refund).drop 1),p.1≠(if refund then sXRZ else sXLH) := by
  cases refund <;> decide

theorem receiptEnd_final (p : ReceiptPlan) (row : Coord)
    (hs : row.state∈fields p.input.refund) (he : receiptEnd p row=true) : row.state=finalState p.input := by
  have hh : (row.state==sXRZ || (row.state==sXLH && !p.input.refund))=true := by
    exact (Bool.and_eq_true_iff.mp he).2
  exact fields_end_final p.input.refund row.state hs hh

def EntityInside : EntityPlan→PlannedRow→Prop
  | .header p,a=>∃row,a=.header p row ∧ row.index+1<12
  | .receipt p,a=>∃row,a=.receipt p row ∧ receiptEnd p row=false

theorem EntityPlan.header_inside (p : ListPlan) (a b : PlannedRow)
    (hab : Neighbors (EntityPlan.header p).rows a b) : EntityInside (.header p) a := by
  obtain ⟨row,next,hh,hea,_⟩ := neighbors_map (PlannedRow.header p) headerRows a b hab
  obtain ⟨_,_,hi,_⟩ := segment_neighbors sCL 12 row next hh
  exact ⟨row,hea.symm,hi⟩

theorem EntityPlan.receipt_inside (p : ReceiptPlan) (hw : p.input.receipt.wf=true) (a b : PlannedRow)
    (hab : Neighbors (EntityPlan.receipt p).rows a b) : EntityInside (.receipt p) a := by
  have hn : ∀s∈receiptSegments p,(SegmentPlan.rows s)≠[] := by
    intro seg hseg
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hseg
    have hlen := fields_positive p.input hw s hs
    intro hz
    have he := congrArg List.length hz
    simp only [SegmentPlan.rows,List.length_map,segment_length,List.length_nil] at he
    exact (Nat.ne_of_gt hlen) he
  change Neighbors (plannedReceiptRows p) a b at hab
  rw [←receiptSegments_rows] at hab
  rcases neighbors_flatMap_nonempty SegmentPlan.rows (receiptSegments p) a b hn hab with
    ⟨seg,hseg,hh⟩|⟨seg,next,hseg,ha,_⟩
  · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hseg
    obtain ⟨row,_,hl,hi,hea,_⟩ := (SegmentPlan.receipt p s).neighbors a b hh
    refine ⟨row,hea,?_⟩
    have he : row.index+1≠row.length := by omega
    simp [receiptEnd,he]
  · obtain ⟨s,t,hst,hseg,hnext⟩ := neighbors_map (SegmentPlan.receipt p) (fields p.input.refund) seg next hseg
    subst seg next
    obtain ⟨row,hs,_,_,hea⟩ := (SegmentPlan.receipt p s).last a ha
    refine ⟨row,hea,?_⟩
    have hnot : row.state≠finalState p.input := by
      exact hs ▸ fields_next_not_final p.input.refund (s,t) hst
    have hm : row.state∈fields p.input.refund := by
      obtain ⟨i,hi,_⟩ := neighbors_get _ s t hst
      rw [hs]
      exact List.mem_of_getElem? hi
    cases he : receiptEnd p row with
    | false => rfl
    | true => exact False.elim (hnot (receiptEnd_final p row hm he))

end ZkFormal.NearV3.Assembly.RcptSkeleton
