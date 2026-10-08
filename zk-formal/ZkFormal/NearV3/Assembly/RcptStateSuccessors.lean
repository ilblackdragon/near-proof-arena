import ZkFormal.NearV3.Assembly.RcptStateBoundary

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def SegmentPlan.refund : SegmentPlan→Bool
  | .header _=>false
  | .receipt p _=>p.input.refund

def SuccessorTo (p q : SegmentPlan) : Prop := ∀s t g,(s,t,g)∈succ→s=p.state→
  g.eval (refundTrace p.refund) 0 0 []=0 ∨ t=q.state

def SuccessorsOff (p : SegmentPlan) : Prop := ∀s t g,(s,t,g)∈succ→s=p.state→
  g.eval (refundTrace p.refund) 0 0 []=0

theorem header_successorsOff (p : ListPlan) : SuccessorsOff (.header p) := by
  intro s t g hg hs
  change s=sCL at hs
  subst s
  simp [succ,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,sXRI,sXG,sXST,sXL0,sXLH,sXRH,sXRF,sXRZ] at hg

theorem terminal_successorsOff (p : ReceiptPlan) : SuccessorsOff (.receipt p (finalState p.input)) := by
  intro s t g hg hs
  change s=finalState p.input at hs
  subst s
  cases hr : p.input.refund <;>
    simp [finalState,hr,succ,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,sXRI,sXG,sXST,sXL0,sXLH,sXRH,sXRF,sXRZ] at hg
  rcases hg with ⟨rfl,rfl⟩
  change (if p.input.refund then (1:Fp) else 0)=0
  rw [hr];rfl

theorem SuccessorsOff.to (p q : SegmentPlan) (h : SuccessorsOff p) : SuccessorTo p q := by
  intro s t g hg hs;exact Or.inl (h s t g hg hs)

theorem receiptSegments_successor (p : ReceiptPlan) (a b : SegmentPlan)
    (hab : Neighbors (receiptSegments p) a b) : SuccessorTo a b := by
  obtain ⟨s,t,hst,rfl,rfl⟩ := neighbors_map (SegmentPlan.receipt p) (fields p.input.refund) a b hab
  intro s' t' g hg hs
  exact fields_successor_unique p.input hst hg hs [] |>.imp_left (fun hh=>(successor_shape p.input hg []).symm.trans hh)

theorem receiptSegments_last_off (p : ReceiptPlan) (a : SegmentPlan)
    (ha : (receiptSegments p).getLast?=some a) : SuccessorsOff a := by
  rw [receiptSegments_last p a ha]
  exact terminal_successorsOff p

theorem listSegments_successor (p : ListPlan) (a b : SegmentPlan)
    (hab : Neighbors (listSegments p) a b) : SuccessorTo a b := by
  rw [listSegments,neighbors_cons] at hab
  rcases hab with ⟨ha,_⟩|hab
  · rw [←ha];exact (header_successorsOff p).to _ _
  · rcases neighbors_flatMap receiptSegments _ a b hab with ⟨rp,_,hh⟩|⟨_,rp,_,_,ha,_⟩
    · exact receiptSegments_successor rp a b hh
    · exact (receiptSegments_last_off rp a ha).to _ _

theorem listSegments_last_off (p : ListPlan) (a : SegmentPlan)
    (ha : (listSegments p).getLast?=some a) : SuccessorsOff a := by
  change (([SegmentPlan.header p] ++ (planReceipts p.listIndex p.inputs.length p.receiptIndex 1 12 p.bodyOffset p.lastList p.inputs).flatMap receiptSegments).getLast?=some a) at ha
  by_cases he : (planReceipts p.listIndex p.inputs.length p.receiptIndex 1 12 p.bodyOffset p.lastList p.inputs).flatMap receiptSegments=[]
  · rw [he] at ha
    simp only [List.append_nil,List.getLast?_cons,List.getLast?_nil] at ha
    cases ha
    exact header_successorsOff p
  · simp only [List.singleton_append] at ha
    rw [List.getLast?_cons_of_ne_nil he] at ha
    obtain ⟨rp,_,hr⟩ := flatMap_last_nonempty receiptSegments _ a (fun p _=>receiptSegments_nonempty p) ha
    exact receiptSegments_last_off rp a hr

theorem plannedSegments_successor (lists : List (List Input)) (a b : SegmentPlan)
    (hab : Neighbors (plannedSegments lists) a b) : SuccessorTo a b := by
  rcases neighbors_flatMap listSegments _ a b hab with ⟨lp,_,hh⟩|⟨_,lp,_,_,ha,_⟩
  · exact listSegments_successor lp a b hh
  · exact (listSegments_last_off lp a ha).to _ _

end ZkFormal.NearV3.Assembly.RcptSkeleton
