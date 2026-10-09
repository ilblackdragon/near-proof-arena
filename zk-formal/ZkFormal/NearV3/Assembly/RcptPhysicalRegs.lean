import ZkFormal.NearV3.Assembly.RcptFinalRegs

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem planned_row_coord_bound (lists : List (List Input)) (a : PlannedRow)
    (ha : a∈plannedRows lists) : (eraseRow a).index<(eraseRow a).length := by
  rw [←plannedSegments_rows] at ha
  obtain ⟨p,_,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨row,hr,he⟩ := List.mem_map.mp ha
  obtain ⟨_,hi,hl⟩ := segment_member hr
  rw [←he,p.erase_wrap,hl]
  exact hi

/-- The single physical receipt trace used by all register subgroups. SHA digest
streams and non-register columns remain parameters for their separate proofs. -/
def nativeReceiptTrace (own : Nat) (ctx : ApplyCtx) (lists : List (List Input)) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) : Trace Fp :=
  plannedTrace lists log constants
    (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
    (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt)) headerFallback)

/-- All 200 unchanged cRegs polynomials on every physical row of one concrete
trace. Includes empty lists, every field/receipt/header boundary, GP final shift,
final active row, padding and cyclic wrap. Native receipt wf, actual public own
bytes and row capacity are explicit; full receipt TableLocal is not claimed. -/
theorem nativeReceiptTrace_cRegs (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length≤2^log)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀pos,pos<2^log→∀e∈cRegs,
      e.eval (nativeReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro pos _
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    exact planned_padding_cRegs lists log pos constants _ _ pub (List.getElem?_eq_none_iff.mp ha)
  | some a =>
    cases hb : (plannedRows lists)[pos+1]? with
    | none =>
      exact planned_final_cRegs own ctx lists hw log pos constants pub digests fallback headerFallback a ha hb hown
    | some b =>
      have hlen := (List.getElem?_eq_some_iff.mp hb).1
      have hh : pos+1<2^log := by omega
      have hrow := planned_row_coord_bound lists a (List.mem_of_getElem? ha)
      by_cases hi : (eraseRow a).index+1<(eraseRow a).length
      · exact planned_interior_cRegs own ctx lists log pos constants pub digests fallback headerFallback a b hown ha hb hi hh
      · have hend : (eraseRow a).index+1=(eraseRow a).length := by omega
        exact planned_active_boundary_cRegs own ctx lists hw log pos constants pub digests fallback headerFallback a b ha hb hend hh hown

end ZkFormal.NearV3.Assembly.RcptSkeleton
