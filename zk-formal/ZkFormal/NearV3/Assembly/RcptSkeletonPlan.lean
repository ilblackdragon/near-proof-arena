import ZkFormal.NearV3.Assembly.RcptSkeletonLastIndex

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3

/-- Offsets from the unchanged cStates receipt-size equations. Their equality
with serialized native receipts/refunds is a separate encoding obligation. -/
def rcLength (x : Input) : Nat :=
  123+x.receipt.predecessorId.length+x.receipt.receiverId.length+
    x.receipt.signerId.length+32*x.receipt.signerPk.tag

def refundLength (x : Input) : Nat :=
  if x.refund then 129+2*x.receipt.signerId.length+32*x.receipt.signerPk.tag else 0

structure ReceiptPlan where
  input : Input
  listIndex : Nat
  listCount : Nat
  receiptIndex : Nat
  withinList : Nat
  rcOffset : Nat
  bodyOffset : Nat
  lastInList : Bool
  lastList : Bool

structure ListPlan where
  inputs : List Input
  listIndex : Nat
  receiptIndex : Nat
  bodyOffset : Nat
  lastList : Bool

def planReceipts (j nj r cj o o2 : Nat) (lastList : Bool) : List Input→List ReceiptPlan
  | []=>[]
  | x::xs=>⟨x,j,nj,r,cj,o,o2,xs.isEmpty,lastList⟩::
      planReceipts j nj (r+1) (cj+1) (o+rcLength x) (o2+refundLength x) lastList xs

def planLists (j r o2 : Nat) : List (List Input)→List ListPlan
  | []=>[]
  | xs::lists=>⟨xs,j,r,o2,lists.isEmpty⟩::
      planLists (j+1) (r+xs.length) (o2+(xs.map refundLength).sum) lists

inductive PlannedRow where
  | header (plan : ListPlan) (coord : Coord)
  | receipt (plan : ReceiptPlan) (coord : Coord)

def plannedReceiptRows (plan : ReceiptPlan) : List PlannedRow :=
  (receiptRows plan.input).map (PlannedRow.receipt plan)

def plannedListRows (plan : ListPlan) : List PlannedRow :=
  headerRows.map (PlannedRow.header plan) ++
    (planReceipts plan.listIndex plan.inputs.length plan.receiptIndex 1 12 plan.bodyOffset
      plan.lastList plan.inputs).flatMap plannedReceiptRows

/-- The initial list/receipt indices are zero, RC starts at 12 per list and body
starts at 8 globally. Empty lists are retained as complete 12-row headers. -/
def plannedRows (lists : List (List Input)) : List PlannedRow :=
  (planLists 0 0 8 lists).flatMap plannedListRows

def eraseRow : PlannedRow→Coord
  | .header _ c | .receipt _ c=>c

theorem planReceipts_inputs (xs : List Input) (j nj r cj o o2 : Nat) (ll : Bool) :
    (planReceipts j nj r cj o o2 ll xs).map ReceiptPlan.input=xs := by
  induction xs generalizing r cj o o2 with
  | nil => rfl
  | cons x xs ih => simp only [planReceipts,List.map_cons,ih]

theorem planned_receipts_erase (xs : List Input) (j nj r cj o o2 : Nat) (ll : Bool) :
    ((planReceipts j nj r cj o o2 ll xs).flatMap plannedReceiptRows).map eraseRow=
      xs.flatMap receiptRows := by
  induction xs generalizing r cj o o2 with
  | nil => rfl
  | cons x xs ih =>
    simp only [planReceipts,List.flatMap_cons,List.map_append,ih,plannedReceiptRows,List.map_map]
    congr 1
    simp only [Function.comp_def,eraseRow]
    exact List.map_id _

theorem planned_list_erase (plan : ListPlan) :
    (plannedListRows plan).map eraseRow=listRows plan.inputs := by
  simp only [plannedListRows,List.map_append,List.map_map,Function.comp_def,eraseRow,
    planned_receipts_erase,listRows]
  congr 1

theorem planLists_erase (lists : List (List Input)) (j r o2 : Nat) :
    ((planLists j r o2 lists).flatMap plannedListRows).map eraseRow=allRows lists := by
  induction lists generalizing j r o2 with
  | nil => rfl
  | cons xs lists ih =>
    simp only [planLists,List.flatMap_cons,List.map_append,planned_list_erase,ih,allRows]

theorem plannedRows_erase (lists : List (List Input)) :
    (plannedRows lists).map eraseRow=allRows lists := planLists_erase lists 0 0 8

theorem plannedRows_bound (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) :
    (plannedRows lists).length≤12*lists.length+474*(lists.map List.length).sum := by
  have hh := congrArg List.length (plannedRows_erase lists)
  simp only [List.length_map] at hh
  rw [hh]
  exact allRows_bound lists hw

end ZkFormal.NearV3.Assembly.RcptSkeleton
