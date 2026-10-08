import ZkFormal.NearV3.Assembly.RcptRowNeighbors

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Near RcptV3

inductive SegmentPlan where
  | header (plan : ListPlan)
  | receipt (plan : ReceiptPlan) (state : Nat)

def SegmentPlan.state : SegmentPlan→Nat
  | .header _=>sCL
  | .receipt _ s=>s

def SegmentPlan.length : SegmentPlan→Nat
  | .header _=>12
  | .receipt p s=>fieldLen p.input s

def SegmentPlan.wrap : SegmentPlan→Coord→PlannedRow
  | .header p=>.header p
  | .receipt p _=>.receipt p

def SegmentPlan.rows (p : SegmentPlan) : List PlannedRow :=
  (segment p.state p.length).map p.wrap

def receiptSegments (p : ReceiptPlan) : List SegmentPlan :=
  (fields p.input.refund).map (.receipt p)

def listSegments (p : ListPlan) : List SegmentPlan :=
  .header p :: (planReceipts p.listIndex p.inputs.length p.receiptIndex 1 12 p.bodyOffset
    p.lastList p.inputs).flatMap receiptSegments

def plannedSegments (lists : List (List Input)) : List SegmentPlan :=
  (planLists 0 0 8 lists).flatMap listSegments

theorem receiptSegments_rows (p : ReceiptPlan) :
    (receiptSegments p).flatMap SegmentPlan.rows=plannedReceiptRows p := by
  simp [receiptSegments,SegmentPlan.rows,SegmentPlan.state,SegmentPlan.length,
    SegmentPlan.wrap,plannedReceiptRows,receiptRows,List.map_flatMap,List.flatMap_map]

theorem listSegments_rows (p : ListPlan) :
    (listSegments p).flatMap SegmentPlan.rows=plannedListRows p := by
  simp only [listSegments,List.flatMap_cons,List.flatMap_assoc,receiptSegments_rows]
  rfl

theorem plannedSegments_rows (lists : List (List Input)) :
    (plannedSegments lists).flatMap SegmentPlan.rows=plannedRows lists := by
  simp only [plannedSegments,List.flatMap_assoc,listSegments_rows,plannedRows]

/-- Exact segmentation of the physical row list, retaining annotations and
empty-list headers. -/
theorem planned_neighbors (lists : List (List Input)) (a b : PlannedRow)
    (h : Neighbors (plannedRows lists) a b) :
    (∃ p∈plannedSegments lists,Neighbors p.rows a b) ∨
    (∃ pre p post,plannedSegments lists=pre++p::post ∧ p.rows.getLast?=some a ∧
      (post.flatMap SegmentPlan.rows).head?=some b) := by
  rw [←plannedSegments_rows] at h
  exact neighbors_flatMap SegmentPlan.rows _ a b h

theorem SegmentPlan.neighbors (p : SegmentPlan) (a b : PlannedRow)
    (h : Neighbors p.rows a b) :
    ∃ row,row.state=p.state ∧ row.length=p.length ∧ row.index+1<p.length ∧
      a=p.wrap row ∧ b=p.wrap (advance row) := by
  obtain ⟨x,y,hxy,ha,hb⟩ := neighbors_map p.wrap _ a b h
  obtain ⟨hs,hl,hi,he⟩ := segment_neighbors p.state p.length x y hxy
  exact ⟨x,hs,hl,hi,ha.symm,by simpa [he] using hb.symm⟩

theorem SegmentPlan.last (p : SegmentPlan) (a : PlannedRow)
    (h : p.rows.getLast?=some a) :
    ∃ row,row.state=p.state ∧ row.length=p.length ∧ row.index+1=p.length ∧ a=p.wrap row := by
  simp only [SegmentPlan.rows,List.getLast?_map] at h
  obtain ⟨row,hr,ha⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hs,hl,hi⟩ := segment_last p.state p.length row hr
  exact ⟨row,hs,hl,hi,ha.symm⟩

/-- Complete next-active-row classification: either the exact same annotated
segment advances, or its last coordinate is reached. Empty source lists retain
their header segments; empty field segments cannot hide an interior step. -/
theorem planned_neighbor_shape (lists : List (List Input)) (a b : PlannedRow)
    (h : Neighbors (plannedRows lists) a b) :
    (∃ p∈plannedSegments lists,∃ row,row.state=p.state ∧ row.length=p.length ∧
      row.index+1<p.length ∧ a=p.wrap row ∧ b=p.wrap (advance row)) ∨
    (∃ (p : SegmentPlan) (row : Coord),row.state=p.state ∧ row.length=p.length ∧ row.index+1=p.length ∧ a=p.wrap row) := by
  rcases planned_neighbors lists a b h with ⟨p,hp,hh⟩|⟨pre,p,post,_,ha,_⟩
  · obtain ⟨row,hs,hl,hi,ha,hb⟩ := p.neighbors a b hh
    exact Or.inl ⟨p,hp,row,hs,hl,hi,ha,hb⟩
  · obtain ⟨row,hs,hl,hi,ha⟩ := p.last a ha
    exact Or.inr ⟨p,row,hs,hl,hi,ha⟩

/-- Indexed physical rows inherit the same exact classification. -/
theorem planned_index_neighbor_shape (lists : List (List Input)) (i : Nat) (a b : PlannedRow)
    (ha : (plannedRows lists)[i]?=some a) (hb : (plannedRows lists)[i+1]?=some b) :
    (∃ p∈plannedSegments lists,∃ row,row.state=p.state ∧ row.length=p.length ∧
      row.index+1<p.length ∧ a=p.wrap row ∧ b=p.wrap (advance row)) ∨
    (∃ (p : SegmentPlan) (row : Coord),row.state=p.state ∧ row.length=p.length ∧ row.index+1=p.length ∧ a=p.wrap row) :=
  planned_neighbor_shape lists a b (neighbors_of_get _ a b i ha hb)

end ZkFormal.NearV3.Assembly.RcptSkeleton
