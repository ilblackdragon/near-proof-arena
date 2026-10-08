import ZkFormal.NearV3.Assembly.RcptEntityBoundary

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 RcptV3

def EntityPlan.firstRow : EntityPlan→PlannedRow
  | .header p=>.header p ⟨sCL,0,12⟩
  | .receipt p=>.receipt p ⟨sPL,0,4⟩

theorem EntityPlan.rows_first (p : EntityPlan) : p.rows.head?=some p.firstRow := by
  cases p <;> rfl

theorem EntityPlan.rows_nonempty (p : EntityPlan) : p.rows≠[] := by
  intro h
  have hh := p.rows_first
  rw [h] at hh
  cases hh

theorem EntityPlan.head (p : EntityPlan) (a : PlannedRow) (ha : p.rows.head?=some a) : a=p.firstRow := by
  rw [p.rows_first] at ha
  exact (Option.some.inj ha).symm

theorem entityPlans_receipt_wf (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (p : ReceiptPlan)
    (hp : EntityPlan.receipt p∈entityPlans lists) : p.input.receipt.wf=true := by
  have hm : (EntityPlan.receipt p).firstRow∈plannedRows lists := by
    rw [←entityPlans_rows]
    exact List.mem_flatMap.mpr ⟨.receipt p,hp,List.mem_of_head? (EntityPlan.rows_first _)⟩
  exact planned_receipt_wf lists hw p ⟨sPL,0,4⟩ hm

theorem EntityPlan.header_last (p : ListPlan) (a : PlannedRow)
    (ha : (EntityPlan.header p).rows.getLast?=some a) : a=.header p ⟨sCL,11,12⟩ := by
  have h : (EntityPlan.header p).rows.getLast?=some (.header p ⟨sCL,11,12⟩) := rfl
  rw [h] at ha
  exact (Option.some.inj ha).symm

theorem EntityPlan.receipt_last (p : ReceiptPlan) (hw : p.input.receipt.wf=true) (a : PlannedRow)
    (ha : (EntityPlan.receipt p).rows.getLast?=some a) :
    ∃row,row.state=finalState p.input ∧ row.index+1=row.length ∧ a=.receipt p row := by
  change (plannedReceiptRows p).getLast?=some a at ha
  rw [←receiptSegments_rows] at ha
  have hn : ∀s∈receiptSegments p,(SegmentPlan.rows s)≠[] := by
    intro seg hseg
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hseg
    have hlen := fields_positive p.input hw s hs
    intro hz
    have he := congrArg List.length hz
    simp only [SegmentPlan.rows,List.length_map,segment_length,List.length_nil] at he
    exact (Nat.ne_of_gt hlen) he
  obtain ⟨seg,hseg,harow⟩ := flatMap_last_nonempty SegmentPlan.rows _ a hn ha
  rw [receiptSegments_last p seg hseg] at harow
  obtain ⟨row,hs,hl,hi,he⟩ := (SegmentPlan.receipt p (finalState p.input)).last a harow
  exact ⟨row,hs,by omega,he⟩

theorem entityPlans_final_flags (lists : List (List Input)) (a : EntityPlan)
    (ha : (entityPlans lists).getLast?=some a) :
    a.lastInList=true ∧ a.lastList=true ∧ a.withinList=a.listCount := by
  obtain ⟨lp,hl,hla⟩ := flatMap_last_nonempty listEntities (planLists 0 0 8 lists) a
    (fun p _=>by simp [listEntities]) ha
  obtain ⟨_,hn,_,hcj,_,hend,hll⟩ := listEntities_last_totals lp a hla
  have hlp := planLists_last_flag lists 0 0 8 lp hl
  exact ⟨hend,hll.trans hlp,hcj.trans hn.symm⟩

theorem planReceipts_lastInList_count (xs : List Input) (j nj r cj o o2 : Nat) (ll : Bool)
    (p : ReceiptPlan) (hp : p∈planReceipts j nj r cj o o2 ll xs) (hl : p.lastInList=true) :
    p.withinList+1=cj+xs.length := by
  induction xs generalizing r cj o o2 p with
  | nil => simp [planReceipts] at hp
  | cons x xs ih =>
    simp only [planReceipts,List.mem_cons] at hp
    rcases hp with rfl|hp
    · change xs.isEmpty=true at hl
      have hx : xs=[] := List.isEmpty_iff.mp hl
      rw [hx]
      rfl
    · have hh := ih (r+1) (cj+1) (o+rcLength x) (o2+refundLength x) p hp hl
      simp only [List.length_cons]
      omega

theorem entityPlans_listEnd_count (lists : List (List Input)) (a : EntityPlan)
    (ha : a∈entityPlans lists) (hl : a.lastInList=true) : a.withinList=a.listCount := by
  obtain ⟨lp,_,ha⟩ := List.mem_flatMap.mp ha
  simp only [listEntities,List.mem_cons] at ha
  rcases ha with rfl|ha
  · change lp.inputs.isEmpty=true at hl
    have hx := List.isEmpty_iff.mp hl
    change 0=lp.inputs.length
    rw [hx];rfl
  · obtain ⟨rp,hr,rfl⟩ := List.mem_map.mp ha
    have hc := planReceipts_lastInList_count lp.inputs _ _ _ _ _ _ _ rp hr hl
    have hn := (receipt_list_constants lp.inputs lp.listIndex lp.inputs.length lp.receiptIndex 1 12 lp.bodyOffset lp.lastList hr).2.1
    change rp.withinList=rp.listCount
    rw [hn]
    omega

end ZkFormal.NearV3.Assembly.RcptSkeleton
