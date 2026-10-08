import ZkFormal.NearV3.Assembly.RcptRegPadding

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Near RcptV3

/-- Number of fully processed receipts at the start/end of a field segment.
Exactly the GP segment advances this index; headers never advance it. -/
def SegmentPlan.startIndex : SegmentPlan→Nat
  | .header p=>p.receiptIndex
  | .receipt p s=>p.receiptIndex+(if sGP<s then 1 else 0)
def SegmentPlan.endIndex : SegmentPlan→Nat
  | .header p=>p.receiptIndex
  | .receipt p s=>p.receiptIndex+(if sGP≤s then 1 else 0)

def segmentLedger (start : Nat) : List SegmentPlan→Nat→Prop
  | [],finish=>start=finish
  | p::ps,finish=>start=p.startIndex ∧ segmentLedger p.endIndex ps finish

theorem segmentLedger_append (xs ys : List SegmentPlan) (a b c : Nat)
    (hx : segmentLedger a xs b) (hy : segmentLedger b ys c) :
    segmentLedger a (xs++ys) c := by
  induction xs generalizing a with
  | nil => exact (show a=b from hx) ▸ hy
  | cons p ps ih => exact ⟨hx.1,ih p.endIndex hx.2⟩

theorem receiptSegments_ledger (p : ReceiptPlan) :
    segmentLedger p.receiptIndex (receiptSegments p) (p.receiptIndex+1) := by
  cases hr : p.input.refund <;>
    simp [receiptSegments,fields,hr,segmentLedger,SegmentPlan.startIndex,SegmentPlan.endIndex,
      sGP,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sTL,sDEP,sXP0,sXRI,sXG,sXST,sXL0,sXLH,sXRH,sXRF,sXRZ]

theorem planReceipts_ledger (xs : List Input) (j nj r cj o o2 : Nat) (ll : Bool) :
    segmentLedger r ((planReceipts j nj r cj o o2 ll xs).flatMap receiptSegments) (r+xs.length) := by
  induction xs generalizing r cj o o2 with
  | nil => simp [planReceipts,segmentLedger]
  | cons x xs ih =>
    simp only [planReceipts,List.flatMap_cons,List.length_cons]
    have hh := segmentLedger_append _ _ r (r+1) (r+1+xs.length)
      (receiptSegments_ledger ⟨x,j,nj,r,cj,o,o2,xs.isEmpty,ll⟩)
      (ih (r+1) (cj+1) (o+rcLength x) (o2+refundLength x))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem listSegments_ledger (p : ListPlan) :
    segmentLedger p.receiptIndex (listSegments p) (p.receiptIndex+p.inputs.length) := by
  exact ⟨rfl,planReceipts_ledger p.inputs _ _ _ _ _ _ _⟩

theorem planLists_ledger (lists : List (List Input)) (j r o2 : Nat) :
    segmentLedger r ((planLists j r o2 lists).flatMap listSegments) (r+lists.flatten.length) := by
  induction lists generalizing j r o2 with
  | nil => simp [planLists,segmentLedger]
  | cons xs lists ih =>
    simp only [planLists,List.flatMap_cons,List.flatten_cons,List.length_append]
    have hh := segmentLedger_append _ _ r (r+xs.length) (r+xs.length+lists.flatten.length)
      (listSegments_ledger ⟨xs,j,r,o2,lists.isEmpty⟩)
      (ih (j+1) (r+xs.length) (o2+(xs.map refundLength).sum))
    simpa [Nat.add_assoc] using hh

theorem plannedSegments_ledger (lists : List (List Input)) :
    segmentLedger 0 (plannedSegments lists) lists.flatten.length := by
  simpa [plannedSegments] using planLists_ledger lists 0 0 8

/-- Consecutive segment indices meet exactly; no field/refund/list-boundary
arithmetic equality is supplied as a witness premise. -/
theorem segmentLedger_neighbors (ps : List SegmentPlan) (a b : Nat)
    (h : segmentLedger a ps b) (p q : SegmentPlan) (hpq : Neighbors ps p q) :
    p.endIndex=q.startIndex := by
  induction ps generalizing a with
  | nil => simp [Neighbors] at hpq
  | cons x xs ih =>
    rw [neighbors_cons] at hpq
    rcases hpq with ⟨rfl,hq⟩|hpq
    · cases xs with
      | nil => simp at hq
      | cons y ys =>
        simp only [List.head?_cons,Option.some.injEq] at hq
        subst y
        exact h.2.1
    · exact ih x.endIndex h.2 hpq

theorem plannedSegments_neighbor_indices (lists : List (List Input)) (p q : SegmentPlan)
    (hpq : Neighbors (plannedSegments lists) p q) : p.endIndex=q.startIndex :=
  segmentLedger_neighbors _ 0 _ (plannedSegments_ledger lists) p q hpq

end ZkFormal.NearV3.Assembly.RcptSkeleton
