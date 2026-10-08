import ZkFormal.NearV3.Assembly.RcptRoutingRowLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

theorem receiver_not_final (p : ReceiptPlan) : sV≠finalState p.input := by
  unfold finalState
  cases p.input.refund <;> decide

theorem planned_receiver_next (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (pos : Nat) (p : ReceiptPlan) (i : Nat)
    (ha : (plannedRows lists)[pos]?=some (.receipt p ⟨sV,i,p.input.receipt.receiverId.length⟩)) :
    (plannedRows lists)[pos+1]?=some (.receipt p (routingNextCoord p i)) := by
  by_cases hi : i+1<p.input.receipt.receiverId.length
  · simpa only [routingNextCoord,if_pos hi,advance] using
      planned_receipt_next lists pos p ⟨sV,i,p.input.receipt.receiverId.length⟩ ha hi
  · have hib := planned_row_coord_bound lists _ (List.mem_of_getElem? ha)
    change i<p.input.receipt.receiverId.length at hib
    have hend : i+1=p.input.receipt.receiverId.length := by omega
    cases hb : (plannedRows lists)[pos+1]? with
    | none =>
      have hp := (List.getElem?_eq_some_iff.mp ha).1
      have hn := List.getElem?_eq_none_iff.mp hb
      have hl : (plannedRows lists).getLast?=some (.receipt p ⟨sV,i,p.input.receipt.receiverId.length⟩) := by
        rw [List.getLast?_eq_getElem?,show (plannedRows lists).length-1=pos by omega]
        exact ha
      obtain ⟨seg,hfinal,hlast⟩ := planned_last_final_segment lists hw _ hl
      obtain ⟨row,hs,_,_,he⟩ := seg.last _ hlast
      cases seg with
      | header => cases he
      | receipt rp state =>
        change PlannedRow.receipt p _=PlannedRow.receipt rp row at he
        cases he
        change sV=state at hs
        subst state
        exact False.elim (receiver_not_final p hfinal.2.2)
    | some next =>
      rcases planned_neighbors_indexed lists hw _ next (neighbors_of_get _ _ next pos ha hb) with
        ⟨seg,_,hn⟩|⟨seg,seg',hne,hl,hh,_⟩
      · obtain ⟨row,_,hlen,hlt,he,_⟩ := seg.neighbors _ next hn
        have hx := congrArg eraseRow he
        rw [seg.erase_wrap] at hx
        change (⟨sV,i,p.input.receipt.receiverId.length⟩ : Coord)=row at hx
        subst row
        dsimp only at hlen hlt
        omega
      · obtain ⟨row,hs,_,_,he⟩ := seg.last _ hl
        cases seg with
        | header => cases he
        | receipt rp state =>
          change PlannedRow.receipt p _=PlannedRow.receipt rp row at he
          cases he
          change sV=state at hs
          subst state
          have hcont := plannedSegments_continues lists _ _ hne
          change sV=finalState p.input ∨ ∃t,seg'=.receipt p t at hcont
          rcases hcont with hf|⟨state,rfl⟩
          · exact False.elim (receiver_not_final p hf)
          · have hsuc := plannedSegments_successor lists _ _ hne sV sRID (Dsl.k 1) (by simp [succ]) rfl
            rcases hsuc with hbad|hstate
            · exact False.elim ((by decide : (1:Fp)≠0) hbad)
            · change sRID=state at hstate
              subst state
              have hnext := (SegmentPlan.receipt p sRID).head next hh
              simpa only [routingNextCoord,if_neg hi,SegmentPlan.wrap,SegmentPlan.state,SegmentPlan.length,fieldLen,
                sRID,sCL,sPL,sP,sVL,sV,Nat.reduceEqDiff,ite_false,ite_true] using congrArg some hnext

end ZkFormal.NearV3.Assembly.RcptSkeleton
