import ZkFormal.NearV3.Assembly.RcptStateHeaderCheckpoint

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3

/-- Whole list headers and whole receipts, retaining the exact plans already
used by the physical trace. This coarser view exposes list-boundary bookkeeping. -/
inductive EntityPlan where
  | header (p : ListPlan)
  | receipt (p : ReceiptPlan)

def EntityPlan.rows : EntityPlan→List PlannedRow
  | .header p=>headerRows.map (.header p)
  | .receipt p=>plannedReceiptRows p

def listEntities (p : ListPlan) : List EntityPlan :=
  .header p :: (planReceipts p.listIndex p.inputs.length p.receiptIndex 1 12 p.bodyOffset p.lastList p.inputs).map EntityPlan.receipt

def entityPlans (lists : List (List Input)) : List EntityPlan :=
  (planLists 0 0 8 lists).flatMap listEntities

theorem listEntities_rows (p : ListPlan) :
    (listEntities p).flatMap EntityPlan.rows=plannedListRows p := by
  simp only [listEntities,List.flatMap_cons,List.flatMap_map,EntityPlan.rows,plannedListRows]

theorem entityPlans_rows (lists : List (List Input)) :
    (entityPlans lists).flatMap EntityPlan.rows=plannedRows lists := by
  simp only [entityPlans,List.flatMap_assoc,listEntities_rows,plannedRows]

def EntityPlan.isHeader : EntityPlan→Bool
  | .header _=>true
  | .receipt _=>false

def EntityPlan.listIndex : EntityPlan→Nat
  | .header p=>p.listIndex
  | .receipt p=>p.listIndex

def EntityPlan.listCount : EntityPlan→Nat
  | .header p=>p.inputs.length
  | .receipt p=>p.listCount

def EntityPlan.receiptIndex : EntityPlan→Nat
  | .header p=>p.receiptIndex
  | .receipt p=>p.receiptIndex

def EntityPlan.withinList : EntityPlan→Nat
  | .header _=>0
  | .receipt p=>p.withinList

def EntityPlan.rcStart : EntityPlan→Nat
  | .header _=>0
  | .receipt p=>p.rcOffset

def EntityPlan.rcEnd : EntityPlan→Nat
  | .header _=>12
  | .receipt p=>p.rcOffset+rcLength p.input

def EntityPlan.bodyStart : EntityPlan→Nat
  | .header p=>p.bodyOffset
  | .receipt p=>p.bodyOffset

def EntityPlan.bodyEnd : EntityPlan→Nat
  | .header p=>p.bodyOffset
  | .receipt p=>p.bodyOffset+refundLength p.input

def EntityPlan.lastInList : EntityPlan→Bool
  | .header p=>p.inputs.isEmpty
  | .receipt p=>p.lastInList

def EntityPlan.lastList : EntityPlan→Bool
  | .header p=>p.lastList
  | .receipt p=>p.lastList

/-- Ordinary natural bookkeeping required between consecutive whole entities.
No AIR condition or main correctness equivalence is built into this predicate. -/
def EntityBoundary (a b : EntityPlan) : Prop :=
  b.listIndex=a.listIndex+(if a.lastInList then 1 else 0) ∧
  b.receiptIndex=a.receiptIndex+(if a.isHeader then 0 else 1) ∧
  b.bodyStart=a.bodyEnd ∧ a.lastInList=b.isHeader ∧
  (a.lastInList && a.lastList)=false ∧
  (b.isHeader=false→b.withinList=a.withinList+1 ∧ b.rcStart=a.rcEnd) ∧
  (a.lastInList=false→b.listCount=a.listCount)

theorem planReceipts_entity_neighbors (xs : List Input) (j nj r cj o o2 : Nat) (ll : Bool)
    (a b : ReceiptPlan)
    (hab : Neighbors (planReceipts j nj r cj o o2 ll xs) a b) :
    EntityBoundary (.receipt a) (.receipt b) := by
  induction xs generalizing r cj o o2 a b with
  | nil => simp [Neighbors,planReceipts] at hab
  | cons x xs ih =>
    rw [planReceipts,neighbors_cons] at hab
    rcases hab with ⟨ha,hb⟩|hab
    · cases xs with
      | nil => simp [planReceipts] at hb
      | cons y ys =>
        simp only [planReceipts,List.head?_cons,Option.some.injEq] at hb
        subst a b
        simp [EntityBoundary,EntityPlan.listIndex,EntityPlan.receiptIndex,EntityPlan.bodyStart,EntityPlan.bodyEnd,
          EntityPlan.isHeader,EntityPlan.lastInList,EntityPlan.lastList,EntityPlan.withinList,EntityPlan.rcStart,
          EntityPlan.rcEnd,EntityPlan.listCount]
    · exact ih _ _ _ _ a b hab

theorem listEntities_neighbors (p : ListPlan) (a b : EntityPlan)
    (hab : Neighbors (listEntities p) a b) : EntityBoundary a b := by
  rw [listEntities,neighbors_cons] at hab
  rcases hab with ⟨ha,hb⟩|hab
  · cases hp : p.inputs with
    | nil => simp [hp,planReceipts] at hb
    | cons x xs =>
      simp only [hp,planReceipts,List.map_cons,List.head?_cons,Option.some.injEq] at hb
      subst a b
      simp [EntityBoundary,EntityPlan.listIndex,EntityPlan.receiptIndex,EntityPlan.bodyStart,EntityPlan.bodyEnd,
        EntityPlan.isHeader,EntityPlan.lastInList,EntityPlan.lastList,EntityPlan.withinList,EntityPlan.rcStart,
        EntityPlan.rcEnd,EntityPlan.listCount,hp]
  · obtain ⟨rp,rq,hr,hra,hrb⟩ := neighbors_map EntityPlan.receipt _ a b hab
    subst a b
    exact planReceipts_entity_neighbors p.inputs _ _ _ _ _ _ _ rp rq hr

end ZkFormal.NearV3.Assembly.RcptSkeleton
