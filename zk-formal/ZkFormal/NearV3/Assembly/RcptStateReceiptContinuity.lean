import ZkFormal.NearV3.Assembly.RcptStateTableEnds

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

def ReceiptSegmentEnd : SegmentPlan→Prop
  | .header _=>True
  | .receipt p s=>s=finalState p.input

def ReceiptContinues (a b : SegmentPlan) : Prop :=
  match a with
  | .header _=>True
  | .receipt p s=>s=finalState p.input ∨ ∃t,b=.receipt p t

theorem ReceiptSegmentEnd.continues {a : SegmentPlan} (h : ReceiptSegmentEnd a) (b : SegmentPlan) : ReceiptContinues a b := by
  cases a with
  | header => trivial
  | receipt p s => exact Or.inl h

theorem receiptSegments_continues (p : ReceiptPlan) (a b : SegmentPlan)
    (hab : Neighbors (receiptSegments p) a b) : ReceiptContinues a b := by
  obtain ⟨s,t,_,rfl,rfl⟩ := neighbors_map (SegmentPlan.receipt p) (fields p.input.refund) a b hab
  exact Or.inr ⟨t,rfl⟩

theorem receiptSegments_end (p : ReceiptPlan) (a : SegmentPlan)
    (ha : (receiptSegments p).getLast?=some a) : ReceiptSegmentEnd a := by
  rw [receiptSegments_last p a ha]
  rfl

theorem listSegments_continues (p : ListPlan) (a b : SegmentPlan)
    (hab : Neighbors (listSegments p) a b) : ReceiptContinues a b := by
  rw [listSegments,neighbors_cons] at hab
  rcases hab with ⟨ha,_⟩|hab
  · rw [←ha];trivial
  · rcases neighbors_flatMap receiptSegments _ a b hab with ⟨rp,_,hh⟩|⟨_,rp,_,_,ha,_⟩
    · exact receiptSegments_continues rp a b hh
    · exact (receiptSegments_end rp a ha).continues b

theorem listSegments_end (p : ListPlan) (a : SegmentPlan)
    (ha : (listSegments p).getLast?=some a) : ReceiptSegmentEnd a := by
  unfold listSegments at ha
  by_cases he : (planReceipts p.listIndex p.inputs.length p.receiptIndex 1 12 p.bodyOffset p.lastList p.inputs).flatMap receiptSegments=[]
  · rw [he] at ha
    simp only [List.getLast?_singleton,Option.some.injEq] at ha
    subst a;trivial
  · rw [List.getLast?_cons_of_ne_nil he] at ha
    obtain ⟨rp,_,hr⟩ := flatMap_last_nonempty receiptSegments _ a (fun p _=>receiptSegments_nonempty p) ha
    exact receiptSegments_end rp a hr

theorem plannedSegments_continues (lists : List (List Input)) (a b : SegmentPlan)
    (hab : Neighbors (plannedSegments lists) a b) : ReceiptContinues a b := by
  rcases neighbors_flatMap listSegments _ a b hab with ⟨lp,_,hh⟩|⟨_,lp,_,_,ha,_⟩
  · exact listSegments_continues lp a b hh
  · exact (listSegments_end lp a ha).continues b

theorem terminal_receiptEnd (p : ReceiptPlan) (row : Coord)
    (hs : row.state=finalState p.input) (he : row.index+1=row.length) :
    receiptEnd p row=true := by
  simp only [receiptEnd,hs,he,beq_self_eq_true,Bool.true_and,finalState]
  cases p.input.refund <;> decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
