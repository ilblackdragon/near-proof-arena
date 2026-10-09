import ZkFormal.NearV3.Assembly.RcptBooleanInputs

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

theorem shapeCell_boolean (x : Input) (hw : x.receipt.wf=true) (col : Nat) (hc : col∈boolCols) :
    BooleanValue (shapeCell x col) := by
  obtain ⟨_,_,_,_,_,_,_,_,hlp,hlv,hls,_⟩ := boolCols_disjoint col hc
  simp only [shapeCell,if_neg hlp,if_neg hlv,if_neg hls]
  split
  · have ht : x.receipt.signerPk.tag=0 ∨ x.receipt.signerPk.tag=1 := by
      simp only [Receipt.wf,PublicKey.wf,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at hw
      grind only
    rcases ht with ht|ht <;> rw [ht] <;> first | exact Or.inl rfl | exact Or.inr rfl
  · split
    · cases x.refund <;> first | exact Or.inl rfl | exact Or.inr rfl
    · exact Or.inl rfl

theorem receiptCell_boolean (constants : ReceiptPlan→Nat→Fp) (aux : ReceiptPlan→Coord→Nat→Fp)
    (hconst : ∀p col,col∈boolCols→BooleanValue (constants p col))
    (haux : ∀p row col,col∈boolCols→BooleanValue (aux p row col))
    (p : ReceiptPlan) (row : Coord) (hw : p.input.receipt.wf=true) (col : Nat) (hc : col∈boolCols) :
    BooleanValue (receiptCell constants aux p row col) := by
  obtain ⟨hj,hnj,hr,hcj,ho,hoe,ho2,ho2e,_,_,_,hidx,_⟩ := boolCols_disjoint col hc
  simp only [receiptCell,if_neg hj,if_neg hnj,if_neg hr,if_neg hcj,if_neg ho,if_neg hoe,if_neg ho2,if_neg ho2e]
  split
  · exact bitCell_boolean _
  · split
    · exact bitCell_boolean _
    · split
      · exact bitCell_boolean _
      · split
        · exact bitCell_boolean _
        · split
          · exact shapeCell_boolean p.input hw col hc
          · split
            · exact control_boolean row col hidx
            · split
              · exact hconst p col hc
              · exact haux p row col hc

theorem headerCell_boolean (aux : ListPlan→Coord→Nat→Fp)
    (haux : ∀p row col,col∈boolCols→BooleanValue (aux p row col))
    (p : ListPlan) (row : Coord) (col : Nat) (hc : col∈boolCols) :
    BooleanValue (headerCell aux p row col) := by
  obtain ⟨hj,hnj,hr,hcj,_,hoe,ho2,ho2e,_,_,_,hidx,_⟩ := boolCols_disjoint col hc
  have hbody : ¬(col=o2 ∨ col=o2End) := by simp [ho2,ho2e]
  simp only [headerCell,if_neg hj,if_neg hnj,if_neg hr,if_neg hcj,if_neg hoe,ho2,ho2e,Bool.false_or,Bool.or_false,decide_false,ite_false]
  split
  · exact Or.inl rfl
  · split
    · exact bitCell_boolean _
    · split
      · exact bitCell_boolean _
      · split
        · rename_i h
          simp_all
        · split
          · exact control_boolean row col hidx
          · exact haux p row col hc

end ZkFormal.NearV3.Assembly.RcptSkeleton
