import ZkFormal.NearV3.Assembly.RcptSegmentAdjacency

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

theorem plannedSegment_receipt_input (lists : List (List Input)) (p : ReceiptPlan) (s : Nat)
    (hp : SegmentPlan.receipt p s∈plannedSegments lists) :
    (lists.flatten.map Input.receipt)[p.receiptIndex]?=some p.input.receipt := by
  obtain ⟨lp,hl,hp⟩ := List.mem_flatMap.mp hp
  simp only [listSegments,List.mem_cons] at hp
  rcases hp with he|hp
  · cases he
  · obtain ⟨rp,hr,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨state,_,he⟩ := List.mem_map.mp hp
    cases he
    simp only [List.getElem?_map,global_plan_receipt lists lp hl p hr,Option.map_some]

theorem receiptPlanToken_old (ctx : ApplyCtx) (lists : List (List Input)) (p : ReceiptPlan) :
    (receiptPlanToken ctx lists p).oldBytes=
      u128 (prefixBurn ctx (lists.flatten.map Input.receipt) 0 p.receiptIndex) := rfl

theorem receiptPlanToken_new (ctx : ApplyCtx) (lists : List (List Input)) (p : ReceiptPlan)
    (s : Nat) (hp : SegmentPlan.receipt p s∈plannedSegments lists) :
    (receiptPlanToken ctx lists p).newBytes=
      u128 (prefixBurn ctx (lists.flatten.map Input.receipt) 0 (p.receiptIndex+1)) := by
  unfold receiptPlanToken TokenInput.newBytes
  rw [prefixBurn_succ ctx _ 0 _ _ (plannedSegment_receipt_input lists p s hp)]

/-- At the first coordinate of every receipt segment, tokens encode exactly
its processed-receipt start index. This includes the first GP byte. -/
theorem receipt_segment_first_token (ctx : ApplyCtx) (lists : List (List Input))
    (p : ReceiptPlan) (s j : Nat) (hj : j<16)
    (hp : SegmentPlan.receipt p s∈plannedSegments lists) :
    tokenOf (receiptPlanToken ctx lists p) ⟨s,0,fieldLen p.input s⟩ j=
      (u128 (prefixBurn ctx (lists.flatten.map Input.receipt) 0
        (SegmentPlan.receipt p s).startIndex)).getD j 0 := by
  by_cases hlt : s<sGP
  · have hnot : ¬sGP<s := by omega
    simp only [tokenOf,if_pos hlt,SegmentPlan.startIndex,if_neg hnot,Nat.add_zero,receiptPlanToken_old]
  · by_cases he : s=sGP
    · subst s
      simp only [tokenOf,show ¬sGP<sGP by omega,ite_false,ite_true,SegmentPlan.startIndex,Nat.add_zero]
      exact token_window_start _ j hj
    · have hgt : sGP<s := by omega
      simp only [tokenOf,if_neg hlt,if_neg he,SegmentPlan.startIndex,if_pos hgt]
      rw [receiptPlanToken_new ctx lists p s hp]

/-- Non-GP segment endpoints carry the exact processed-receipt end total.
The GP endpoint instead uses the checked shifting-window equations. -/
theorem receipt_segment_end_token (ctx : ApplyCtx) (lists : List (List Input))
    (p : ReceiptPlan) (s i len j : Nat) (hs : s≠sGP)
    (hp : SegmentPlan.receipt p s∈plannedSegments lists) :
    tokenOf (receiptPlanToken ctx lists p) ⟨s,i,len⟩ j=
      (u128 (prefixBurn ctx (lists.flatten.map Input.receipt) 0
        (SegmentPlan.receipt p s).endIndex)).getD j 0 := by
  by_cases hlt : s<sGP
  · have hnot : ¬sGP≤s := by omega
    simp only [tokenOf,if_pos hlt,SegmentPlan.endIndex,if_neg hnot,Nat.add_zero,receiptPlanToken_old]
  · have hge : sGP≤s := by omega
    simp only [tokenOf,if_neg hlt,if_neg hs,SegmentPlan.endIndex,if_pos hge]
    rw [receiptPlanToken_new ctx lists p s hp]

end ZkFormal.NearV3.Assembly.RcptSkeleton
