import ZkFormal.NearV3.Assembly.RcptRoutingBoolean

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

theorem routingScratch_bounds (col : Nat) (hc : routingScratch col=true) :
    (158≤col ∧ col<176) ∨ (250≤col ∧ col≤262) := by
  have hr : col∈[gBd,eqL,eqH,eL,eH,vB,iB,loB,hiB,hnB,iL,iH] ∨ (xb 20≤col ∧ col<xb 38) := by
    simpa only [routingScratch,Bool.or_eq_true,decide_eq_true_eq] using hc
  simp only [List.mem_cons,List.not_mem_nil,or_false,gBd,eqL,eqH,eL,eH,vB,iB,loB,hiB,hnB,iL,iH,xb] at hr
  omega

theorem routingActive_not_gp (row : Coord) (ha : routingActive row=true) : row.state≠sGP := by
  simp only [routingActive,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at ha
  simp only [sV,sRID,sGP] at *
  omega

set_option maxRecDepth 4096 in
theorem routingAux_transport (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat)
    (ha : routingActive row=true) (hc : routingScratch col=true) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (routingAux interval fallback))) p row col=
        frameCell (receiptRoutingFrame interval p row) col := by
  have hbound := routingScratch_bounds col hc
  have hrc := (routingScratch_independent col hc).1
  have hgp := routingActive_not_gp row ha
  have hn : col≠rf ∧ col≠rl ∧ col≠lastR ∧ col≠le ∧ col≠j ∧ col≠nj ∧ col≠r ∧ col≠cj ∧
      col≠o ∧ col≠oEnd ∧ col≠o2 ∧ col≠o2End ∧ col≠Lp ∧ col≠Lv ∧ col≠Ls ∧ col≠kt ∧ col≠hr ∧
      ¬col≤29 ∧ ¬(reg 0≤col ∧ col<reg 32) ∧ col≠b ∧ ¬(tok 0≤col ∧ col<tok 16) := by
    simp only [rf,rl,lastR,le,j,nj,r,cj,o,oEnd,o2,o2End,Lp,Lv,Ls,kt,hr,reg,tok,b]
    omega
  rcases hn with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21⟩
  simp only [receiptCell,tokenReceiptAux,streamAux,tokenAux,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,
    h13,h14,h15,h16,h17,h18,h19,h20,h21,hrc,hgp,decide_false,Bool.false_or,Bool.false_eq_true,ite_false,false_and]
  exact routingAux_normalized_active interval fallback p row col ha hc

end ZkFormal.NearV3.Assembly.RcptSkeleton
