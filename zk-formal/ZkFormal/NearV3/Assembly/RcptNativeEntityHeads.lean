import ZkFormal.NearV3.Assembly.RcptDecodedEntities

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

def nativeEntity (start : Nat) : EntityPlan→DecodedEntity
  | .header _=>.header start
  | .receipt p=>.receipt (inputShape start p.input)

theorem nativeEntity_start (start : Nat) (p : EntityPlan) :
    (nativeEntity start p).start=start := by cases p <;> rfl

theorem nativeEntity_rows (start : Nat) (p : EntityPlan) :
    (nativeEntity start p).rows=p.rows.length := by
  cases p with
  | header p => rfl
  | receipt p =>
    simp only [nativeEntity,DecodedEntity.rows,RS.tot,inputShape,EntityPlan.rows,
      plannedReceiptRows,List.length_map,receiptRows_length,total,Vt]
    split <;> omega

def nativeEntities (start : Nat) : List EntityPlan→List DecodedEntity
  | []=>[]
  | p::ps=>nativeEntity start p::nativeEntities (start+p.rows.length) ps

/-- Physical native entity heads are active and distinguish list headers from
receipt blocks before any arithmetic or digest interpretation. -/
theorem native_entity_head (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : EntityPlan)
    (ha : (plannedRows lists)[pos]?=some p.firstRow) :
    let tr := RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0
    tr.cell 0 pos act=1 ∧ tr.cell 0 pos sCL=(if p.isHeader then 1 else 0) := by
  dsimp only
  rw [RoutingQCandidate.patch_other _ 0 pos act (by decide),
    RoutingQCandidate.patch_other _ 0 pos sCL (by decide)]
  rw [booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests fallback headerFallback _ ha act (by decide),
    booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests fallback headerFallback _ ha sCL (by decide)]
  cases p <;> exact ⟨rfl,rfl⟩

/-- An actual prefix decomposition supplies the entity's real first-row address. -/
theorem entity_head_lookup (lists : List (List Input)) (pre post : List EntityPlan) (p : EntityPlan)
    (he : entityPlans lists=pre++p::post) :
    (plannedRows lists)[(pre.flatMap EntityPlan.rows).length]?=some p.firstRow := by
  rw [←entityPlans_rows,he,List.flatMap_append,List.flatMap_cons]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.sub_self]
  rw [List.getElem?_append_left (by have := p.rows_nonempty; exact List.length_pos_iff.mpr this)]
  simpa only [List.head?_eq_getElem?] using p.rows_first

end ZkFormal.NearV3.Assembly.RcptSkeleton
