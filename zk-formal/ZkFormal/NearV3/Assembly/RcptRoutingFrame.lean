import ZkFormal.NearV3.Assembly.RcptRoutingFootprint

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

def routingScratch (col : Nat) : Bool :=
  col∈[gBd,eqL,eqH,eL,eH,vB,iB,loB,hiB,hnB,iL,iH] || decide (xb 20≤col ∧ col<xb 38)

def routingActive (row : Coord) : Bool := row.state==sV || (row.state==sRID && row.index==0)

def routingPosition (p : ReceiptPlan) (row : Coord) : Nat :=
  if row.state=sV then row.index else p.input.receipt.receiverId.length

def receiptRoutingFrame (interval : ReceiptPlan→Option Bytes×Option Bytes) (p : ReceiptPlan) (row : Coord) : RouteFrame :=
  frameOf p.input.receipt.receiverId (interval p) (routingPosition p row)

/-- Only routing rows claim the shared byte-difference scratch bits. Gas and
other states retain their independent arithmetic assignments. -/
def routingAux (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if routingActive row && routingScratch col then frameCell (receiptRoutingFrame interval p row) col
  else if col=gBd then 0 else fallback p row col

def routingHeaderAux (fallback : ListPlan→Coord→Nat→Fp) (p : ListPlan) (row : Coord) (col : Nat) : Fp :=
  if col=gBd then 0 else fallback p row col

theorem routingAux_active (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) (col : Nat)
    (ha : routingActive row=true) (hc : routingScratch col=true) :
    routingAux interval fallback p row col=frameCell (receiptRoutingFrame interval p row) col := by
  simp only [routingAux,ha,hc,Bool.true_and,ite_true]

theorem routingAux_inactive (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) (col : Nat)
    (ha : routingActive row=false) (hc : col≠gBd) :
    routingAux interval fallback p row col=fallback p row col := by
  simp only [routingAux,ha,Bool.false_and,Bool.false_eq_true,ite_false,if_neg hc]

theorem routingAux_gate_zero (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (ha : routingActive row=false) : routingAux interval fallback p row gBd=0 := by
  simp only [routingAux,ha,Bool.false_and,Bool.false_eq_true,ite_false,ite_true]

theorem routingScratch_independent (col : Nat) (hc : routingScratch col=true) :
    col∉rconsts ∧ 29<col ∧ col≠b ∧ col≠gV ∧ col≠gS ∧ col≠sx ∧ col≠invD ∧ col≠scnt ∧ col≠invL ∧
    ¬(111≤col ∧ col≤123) := by
  have hr : col∈[gBd,eqL,eqH,eL,eH,vB,iB,loB,hiB,hnB,iL,iH] ∨ (xb 20≤col ∧ col<xb 38) := by
    simpa only [routingScratch,Bool.or_eq_true,decide_eq_true_eq] using hc
  rcases hr with hr|hr
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · simp only [xb] at hr
    simp only [rconsts,List.mem_cons,List.not_mem_nil,or_false,gBd,eqL,eqH,eL,eH,vB,iB,loB,hiB,hnB,iL,iH,
      b,gV,gS,sx,invD,scnt,invL,r,cj,o,oEnd,o2,o2End,Lp,Lv,Ls,kt,RcptV3.hr,kslot,tprev,ge,big,sys,ee,gq,dm,dd,q]
    omega

end ZkFormal.NearV3.Assembly.RcptSkeleton
