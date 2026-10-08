import ZkFormal.NearV3.Assembly.RcptEntityOtherLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem booleanReceiptTrace_listBoundaries (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length<2^log) :
    ∀e∈listBoundaryConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    exact entityPadding_local _ pos pub (booleanReceiptTrace_padding own ctx lists log pos constants pub digests fallback headerFallback ha)
  | some a =>
    have hpos : pos+1<2^log := by have hh := (List.getElem?_eq_some_iff.mp ha).1;omega
    have ht : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).height 0=2^log := rfl
    cases hb : (plannedRows lists)[pos+1]? with
    | none =>
      have hlast : (plannedRows lists).getLast?=some a := by
        have hh := (List.getElem?_eq_some_iff.mp ha).1
        have hn := List.getElem?_eq_none_iff.mp hb
        rw [List.getLast?_eq_getElem?,show (plannedRows lists).length-1=pos by omega]
        exact ha
      rw [←entityPlans_rows] at hlast
      obtain ⟨p,hp,hpa⟩ := flatMap_last_nonempty EntityPlan.rows (entityPlans lists) a
        (fun p _=>p.rows_nonempty) hlast
      have hpm := List.mem_of_getLast? hp
      have hcells := booleanReceiptTrace_entityCells own ctx lists log pos constants pub digests fallback headerFallback p a ha (List.mem_of_getLast? hpa)
      have hflags := booleanReceiptTrace_entityEnd own ctx lists log pos constants pub digests fallback headerFallback p a ha (entityPlans_wf lists hw p hpm) hpa
      obtain ⟨hl,hll,hcount⟩ := entityPlans_final_flags lists p hp
      apply entityTerminal_local _ pos pub p hcells hflags hl hll hcount
      simpa only [ht,Nat.mod_eq_of_lt hpos] using booleanReceiptTrace_padding own ctx lists log (pos+1) constants pub digests fallback headerFallback hb
    | some b =>
      have hab := neighbors_of_get _ a b pos ha hb
      rw [←entityPlans_rows] at hab
      rcases neighbors_flatMap_nonempty EntityPlan.rows (entityPlans lists) a b
          (fun p _=>p.rows_nonempty) hab with ⟨p,hp,hab⟩|⟨p,q,hpq,hpa,hqb⟩
      · obtain ⟨i,hap,hbp⟩ := neighbors_get p.rows a b hab
        have hca := booleanReceiptTrace_entityCells own ctx lists log pos constants pub digests fallback headerFallback p a ha (List.mem_of_getElem? hap)
        have hcb := booleanReceiptTrace_entityCells own ctx lists log (pos+1) constants pub digests fallback headerFallback p b hb (List.mem_of_getElem? hbp)
        have hi : EntityInside p a := by
          cases p with
          | header lp => exact EntityPlan.header_inside lp a b hab
          | receipt rp => exact EntityPlan.receipt_inside rp (entityPlans_receipt_wf lists hw rp hp) a b hab
        have hf := booleanReceiptTrace_entityInside own ctx lists log pos constants pub digests fallback headerFallback p a ha hi
        apply entityInterior_local _ pos pub p hca _ hf
        simpa only [ht,Nat.mod_eq_of_lt hpos] using hcb
      · obtain ⟨i,hpp,hqq⟩ := neighbors_get (entityPlans lists) p q hpq
        have hpm := List.mem_of_getElem? hpp
        have hca := booleanReceiptTrace_entityCells own ctx lists log pos constants pub digests fallback headerFallback p a ha (List.mem_of_getLast? hpa)
        have hcb := booleanReceiptTrace_entityCells own ctx lists log (pos+1) constants pub digests fallback headerFallback q b hb (List.mem_of_head? hqb)
        have hfa := booleanReceiptTrace_entityEnd own ctx lists log pos constants pub digests fallback headerFallback p a ha (entityPlans_wf lists hw p hpm) hpa
        have he := q.head b hqb
        subst b
        have hfb := booleanReceiptTrace_entityStart own ctx lists log (pos+1) constants pub digests fallback headerFallback q hb
        apply entityBoundary_local _ pos pub p q hca _ hfa _ (entityPlans_boundaries lists p q hpq)
          (fun hl=>entityPlans_listEnd_count lists p hpm hl)
        · simpa only [ht,Nat.mod_eq_of_lt hpos] using hcb
        · simpa only [ht,Nat.mod_eq_of_lt hpos] using hfb

end ZkFormal.NearV3.Assembly.RcptSkeleton
