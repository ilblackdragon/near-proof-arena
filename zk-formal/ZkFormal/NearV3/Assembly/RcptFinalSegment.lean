import ZkFormal.NearV3.Assembly.RcptLastPlans

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Near RcptV3

def FinalSegment : SegmentPlan→Prop
  | .header p=>p.inputs=[] ∧ p.lastList=true
  | .receipt p s=>p.lastInList=true ∧ p.lastList=true ∧ s=finalState p.input

theorem receiptSegments_nonempty (p : ReceiptPlan) : receiptSegments p≠[] := by
  cases h : p.input.refund <;> simp [receiptSegments,fields,h]

theorem receiptSegments_last (p : ReceiptPlan) (s : SegmentPlan)
    (h : (receiptSegments p).getLast?=some s) : s=.receipt p (finalState p.input) := by
  simp only [receiptSegments,List.getLast?_map,fields_last,Option.map_some,Option.some.injEq] at h
  exact h.symm

theorem listSegments_final (p : ListPlan) (hl : p.lastList=true) (s : SegmentPlan)
    (h : (listSegments p).getLast?=some s) : FinalSegment s := by
  by_cases hi : p.inputs=[]
  · simp only [listSegments,hi,planReceipts,List.flatMap_nil,List.getLast?_singleton,Option.some.injEq] at h
    subst s
    exact ⟨hi,hl⟩
  · have hprs : planReceipts p.listIndex p.inputs.length p.receiptIndex 1 12 p.bodyOffset p.lastList p.inputs≠[] := by
      intro he
      have hh := planReceipts_inputs p.inputs p.listIndex p.inputs.length p.receiptIndex 1 12 p.bodyOffset p.lastList
      rw [he] at hh
      exact hi hh.symm
    have hflat : ((planReceipts p.listIndex p.inputs.length p.receiptIndex 1 12 p.bodyOffset p.lastList p.inputs).flatMap receiptSegments)≠[] := by
      generalize he : planReceipts p.listIndex p.inputs.length p.receiptIndex 1 12 p.bodyOffset p.lastList p.inputs=ps at *
      cases ps with
      | nil => exact False.elim (hprs rfl)
      | cons rp rest =>
        intro hh
        exact receiptSegments_nonempty rp (List.eq_nil_of_append_eq_nil hh).1
    rw [listSegments,List.getLast?_cons_of_ne_nil hflat] at h
    obtain ⟨rp,hr,hs⟩ := flatMap_last_nonempty receiptSegments _ s (fun p _=>receiptSegments_nonempty p) h
    have hrflag := planReceipts_last_flag p.inputs _ _ _ _ _ _ _ rp hr
    have hll := (receipt_list_constants p.inputs p.listIndex p.inputs.length p.receiptIndex 1 12 p.bodyOffset
      p.lastList (List.mem_of_getLast? hr)).2.2
    rw [receiptSegments_last rp s hs]
    exact ⟨hrflag,hll.trans hl,rfl⟩

theorem plannedSegments_final (lists : List (List Input)) (p : SegmentPlan)
    (h : (plannedSegments lists).getLast?=some p) : FinalSegment p := by
  obtain ⟨lp,hl,hp⟩ := flatMap_last_nonempty listSegments (planLists 0 0 8 lists) p (by intro p _;simp [listSegments]) h
  exact listSegments_final lp (planLists_last_flag lists 0 0 8 lp hl) p hp

theorem planned_last_final_segment (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (a : PlannedRow)
    (h : (plannedRows lists).getLast?=some a) :
    ∃p,FinalSegment p ∧ p.rows.getLast?=some a := by
  rw [←plannedSegments_rows] at h
  obtain ⟨p,hp,ha⟩ := flatMap_last_nonempty SegmentPlan.rows _ a (plannedSegments_nonempty lists hw) h
  exact ⟨p,plannedSegments_final lists p hp,ha⟩

end ZkFormal.NearV3.Assembly.RcptSkeleton
