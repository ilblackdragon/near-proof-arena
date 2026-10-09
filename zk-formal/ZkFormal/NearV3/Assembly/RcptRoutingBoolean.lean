import ZkFormal.NearV3.Assembly.RcptRoutingFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

set_option maxRecDepth 4096 in
theorem routing_boolean_columns : ∀col∈boolCols,routingScratch col=true→
    col∈[gBd,eqL,eqH,eL,eH,hnB] ∨ xb 20≤col ∧ col<xb 38 := by decide

theorem routing_frame_boolean (f : RouteFrame) (col : Nat)
    (hc : routingScratch col=true) (hb : col∈boolCols) : BooleanValue (frameCell f col) := by
  rcases routing_boolean_columns col hb hc with hs|hs
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [frame_cell_13,frame_cell_11,frame_cell_12,frame_cell_14,frame_cell_15,frame_cell_10]
    all_goals split <;> first | exact Or.inl rfl | exact Or.inr rfl
  · have hne : col≠iL ∧ col≠iH ∧ col≠sV ∧ col≠sRID ∧ col≠fs ∧ col≠idx ∧ col≠Lv ∧ col≠iB ∧
        col≠b ∧ col≠vB ∧ col≠loB ∧ col≠hiB ∧ col≠hnB ∧ col≠eqL ∧ col≠eqH ∧ col≠gBd ∧ col≠eL ∧ col≠eH := by
      simp only [xb] at hs
      simp only [iL,iH,sV,sRID,fs,idx,Lv,iB,b,vB,loB,hiB,hnB,eqL,eqH,gBd,eL,eH]
      omega
    simp only [frameCell,if_neg hne.1,if_neg hne.2.1]
    simp only [hne.2.2.1,hne.2.2.2.1,hne.2.2.2.2.1]
    rcases hne with ⟨_,_,hsv,hsrid,hfs,hidx,hlv,hib,hb,hvb,hlo,hhi,hhn,hel,heh,hg,helb,hehb⟩
    simp only [if_neg hsv,if_neg hsrid,if_neg hfs,hidx,hlv,hib,hb,hvb,hlo,hhi,hhn,hel,heh,hg,helb,hehb,
      decide_false,Bool.false_or,Bool.false_eq_true,ite_false,false_or]
    split
    · exact frameBit_boolean _ _
    · split
      · exact frameBit_boolean _ _
      · exact Or.inl rfl

theorem routingAux_normalized_active (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) (col : Nat)
    (ha : routingActive row=true) (hc : routingScratch col=true) :
    booleanReceiptAux (routingAux interval fallback) p row col=frameCell (receiptRoutingFrame interval p row) col := by
  unfold booleanReceiptAux
  rw [routingAux_active interval fallback p row col ha hc]
  by_cases hb : col∈boolCols
  · exact boolInput_preserves _ _ (routing_frame_boolean _ col hc hb)
  · exact if_neg hb

end ZkFormal.NearV3.Assembly.RcptSkeleton
