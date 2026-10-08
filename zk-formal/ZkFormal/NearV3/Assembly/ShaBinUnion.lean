import ZkFormal.NearV3.Assembly.ShaUnionFacts
import ZkFormal.NearV3.Assembly.ShaBinRender

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

private theorem getD_mem {α : Type} {xs : List α} {t : Nat} (ht : t<xs.length) (d : α) :
    xs.getD t d∈xs := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ht,Option.getD_some]
  exact List.getElem_mem ht

theorem shaBinUnionFacts (bins : List (List Sha.Gen.Msg)) (pub : List Fp)
    (hok : ∀bin∈bins,Sha.MsgsOk bin) :
    ShaFacts (shaUnionCount (shaBinTrace bins) pub (List.range bins.length) true)
      (shaUnionCount (shaBinTrace bins) pub (List.range bins.length) false) := by
  apply shaUnionFacts
  intro t ht
  have hmem := getD_mem (List.mem_range.mp ht) ([] : List Sha.Gen.Msg)
  have hl := shaBin_local bins t pub (hok _ hmem)
  exact ⟨hl.log_ge,hl.log_le,hl.constr⟩

private theorem getD_sum {α : Type} (xs : List α) (d : α) (f : α→Nat) :
    ((List.range xs.length).map fun t=>f (xs.getD t d)).sum=(xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,
      Function.comp_def,List.getD_cons_zero,List.getD_cons_succ,List.sum_cons,ih]

private theorem count_flatMap {α β : Type} [BEq β] [LawfulBEq β]
    (xs : List α) (f : α→List β) (m : β) :
    ((xs.map fun x=>(f x).count m)).sum=(xs.flatMap f).count m := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.count_append,ih]

private theorem union_as_sum (tr : Trace Fp) (pub : List Fp) (ts : List Nat)
    (sd : Bool) (b : Nat) (m : List Fp) :
    shaUnionCount tr pub ts sd b m=(ts.map fun t=>shaCountAt tr pub t sd b m).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [shaUnionCount,List.map_cons,List.sum_cons,ih]

/-- Exact total multiplicities over physical bins, including off-bus zero counts. -/
theorem shaBinUnion_traffic (bins : List (List Sha.Gen.Msg)) (pub : List Fp)
    (hok : ∀bin∈bins,Sha.MsgsOk bin) (b : Nat) (m : List Fp) :
    shaUnionCount (shaBinTrace bins) pub (List.range bins.length) true b m=
      ((bins.flatMap fun bin=>(shaBinTraffic bin).sends b).map Msg.toFp).count m ∧
    shaUnionCount (shaBinTrace bins) pub (List.range bins.length) false b m=
      ((bins.flatMap fun bin=>(shaBinTraffic bin).recvs b).map Msg.toFp).count m := by
  have ht : ∀t∈List.range bins.length,
      shaCountAt (shaBinTrace bins) pub t true b m=
        (((shaBinTraffic (bins.getD t [])).sends b).map Msg.toFp).count m ∧
      shaCountAt (shaBinTrace bins) pub t false b m=
        (((shaBinTraffic (bins.getD t [])).recvs b).map Msg.toFp).count m := by
    intro t ht
    exact shaBin_traffic bins t pub (hok _ (getD_mem (List.mem_range.mp ht) [])) b m
  constructor
  · rw [union_as_sum]
    rw [List.map_congr_left (fun t ht' =>(ht t ht').1)]
    rw [getD_sum bins [] (fun bin=>(((shaBinTraffic bin).sends b).map Msg.toFp).count m),count_flatMap,List.map_flatMap]
  · rw [union_as_sum]
    rw [List.map_congr_left (fun t ht' =>(ht t ht').2)]
    rw [getD_sum bins [] (fun bin=>(((shaBinTraffic bin).recvs b).map Msg.toFp).count m),count_flatMap,List.map_flatMap]

end ZkFormal.NearV3.Assembly
