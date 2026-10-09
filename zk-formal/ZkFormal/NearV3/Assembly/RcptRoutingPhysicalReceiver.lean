import ZkFormal.NearV3.Assembly.RcptRoutingNeighbors

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

theorem routing_no_emission (col : Nat) (hc : routingColumn col=true) : emissionColumn col=false := by
  rcases routingColumn_split col hc with hm|hm
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · have hh := routingScratch_bounds col hm
    simp only [emissionColumn,decide_eq_false_iff_not]
    omega

theorem booleanReceiptTrace_receiver_route (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i : Nat)
    (ha : (plannedRows lists)[pos]?=some (.receipt p ⟨sV,i,p.input.receipt.receiverId.length⟩))
    (hcap : (plannedRows lists).length≤2^log)
    (hv : inInterval p.input.receipt.receiverId (interval p)=true)
    (hu : ∀v∈(interval p).2.getD [],0<v.toNat) :
    ∀e∈cRoute,e.eval (booleanReceiptTrace own ctx lists log constants pub digests
      (routingAux interval fallback) (routingHeaderAux headerFallback)) 0 pos pub=0 := by
  let tr := booleanReceiptTrace own ctx lists log constants pub digests
    (routingAux interval fallback) (routingHeaderAux headerFallback)
  have hi := planned_row_coord_bound lists _ (List.mem_of_getElem? ha)
  change i<p.input.receipt.receiverId.length at hi
  have hn := planned_receiver_next lists hw pos p i ha
  have hpos : pos+1<2^log := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hn).1 hcap
  apply routing_adjusted_transport tr 0 pos pub (frameOf p.input.receipt.receiverId (interval p) i)
    (frameOf_ordered _ _ _ (Nat.le_of_lt hi) hv hu) p.input.receipt.receiverId.length 0
  · intro col hc
    exact (booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests
      (routingAux interval fallback) (routingHeaderAux headerFallback) _ ha col (routing_no_emission col hc)).trans
      (routing_receiver_current interval constants pub digests (receiptPlanToken ctx lists) fallback p i _ hi col hc)
  · intro col hc
    change tr.cell 0 ((pos+1)%2^log) col=_
    rw [Nat.mod_eq_of_lt hpos]
    exact (booleanReceiptTrace_planned_cell own ctx lists log (pos+1) constants pub digests
      (routingAux interval fallback) (routingHeaderAux headerFallback) _ hn col
      (by rcases hc with rfl|rfl <;> decide)).trans
      (routing_receiver_next_cells interval constants pub digests (receiptPlanToken ctx lists) fallback p i hi col hc)

end ZkFormal.NearV3.Assembly.RcptSkeleton
