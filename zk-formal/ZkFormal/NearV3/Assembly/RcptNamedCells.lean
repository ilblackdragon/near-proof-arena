import ZkFormal.NearV3.Assembly.RcptNamedFixedComposition

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

theorem planned_receipt_field_length (lists : List (List Input)) (p : ReceiptPlan) (row : Coord)
    (ha : PlannedRow.receipt p row∈plannedRows lists) : row.length=fieldLen p.input row.state := by
  rw [←plannedSegments_rows] at ha
  obtain ⟨seg,_,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨coord,hc,he⟩ := List.mem_map.mp ha
  obtain ⟨hs,_,hl⟩ := segment_member hc
  cases seg with
  | header lp => cases he
  | receipt rp state =>
    cases he
    change row.state=state at hs
    change row.length=fieldLen p.input state at hl
    rw [hs]
    exact hl

theorem characterByte_receiver (p : ReceiptPlan) (row : Coord) (hs : row.state=sV) :
    characterByte p row=(characterData p.input.receipt).recv.getD row.index 0 := by
  simp only [characterByte,characterBytes,hs,sV,sP,sS,Nat.reduceEqDiff,↓reduceIte,characterData,toNats,
    List.getD_eq_getElem?_getD,List.getElem?_map]
  cases p.input.receipt.receiverId[row.index]? <;> rfl

theorem booleanReceiptTrace_named_cells (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (ha : (plannedRows lists)[pos]?=some (.receipt p row)) (col : Nat)
    (hc : col∈[acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3]) :
    (booleanReceiptTrace own ctx lists log constants pub digests
      (characterAux (namedAux fallback)) (characterHeaderAux headerFallback)).cell 0 pos col=
        namedAux (characterAux fallback) p row col := by
  rw [←named_character_commute]
  have hem : emissionColumn col=false := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact (booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests
    (namedAux (characterAux fallback)) (characterHeaderAux headerFallback) _ ha col hem).trans
      (namedAux_transport ctx lists constants pub digests (characterAux fallback) p row col hc)

theorem booleanReceiptTrace_named_byte (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (ha : (plannedRows lists)[pos]?=some (.receipt p row)) (hs : row.state=sV) :
    (booleanReceiptTrace own ctx lists log constants pub digests
      (characterAux (namedAux fallback)) (characterHeaderAux headerFallback)).cell 0 pos b=
        Fp.ofNat ((characterData p.input.receipt).recv.getD row.index 0) := by
  have hchar := character_receipt_cells ctx lists constants pub digests (namedAux fallback) p row
    (show row.state∈[sP,sV,sS] by rw [hs];decide)
  have hc := booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests
    (characterAux (namedAux fallback)) (characterHeaderAux headerFallback) _ ha b (by decide)
  have hh := hc.trans (hchar b (by decide))
  change _=Fp.ofNat (characterByte p row) at hh
  rw [characterByte_receiver p row hs] at hh
  exact hh

theorem booleanReceiptTrace_named_hex (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (ha : (plannedRows lists)[pos]?=some (.receipt p row)) (hs : row.state=sV)
    (hw : p.input.receipt.wf=true) :
    hexE.eval (booleanReceiptTrace own ctx lists log constants pub digests
      (characterAux (namedAux fallback)) (characterHeaderAux headerFallback)) 0 pos pub=
        Fp.ofNat (b2n (isHexC ((characterData p.input.receipt).recv.getD row.index 0))) := by
  have hl := planned_receipt_field_length lists p row (List.mem_of_getElem? ha)
  have hi := planned_row_coord_bound lists (.receipt p row) (List.mem_of_getElem? ha)
  change row.index<row.length at hi
  have hh := booleanReceiptTrace_hex own ctx lists log pos constants pub digests
    (namedAux fallback) headerFallback p row ha hw (show row.state∈[sP,sV,sS] by rw [hs];decide) (by omega)
  rw [characterByte_receiver p row hs] at hh
  rw [hh]
  cases isHexC ((characterData p.input.receipt).recv.getD row.index 0) <;> rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
