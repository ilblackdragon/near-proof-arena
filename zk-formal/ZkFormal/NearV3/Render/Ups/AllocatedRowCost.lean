import ZkFormal.NearV3.Render.Ups.AcceptedInstanceList

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec Assembly

private theorem range_getD {α : Type} (xs : List α) (d : α) :
    (List.range xs.length).map (fun k=>xs.getD k d)=xs := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2,Option.getD_some]

theorem R_eq_sum_rows (insts : List UpsInst) :
    R insts=(insts.map (fun I=>(recsI I).length)).sum := by
  unfold R recs
  simp only [List.length_flatMap,List.length_map]
  conv => rhs; rw [←range_getD insts default]
  simp only [List.map_map,Function.comp_def]

private theorem scheduler_charge_sum (us : List SchedulerUpsertWitness) :
    (us.map (fun u=>4+u.value.length+outputByteCharge u.run)).sum=
      4*us.length+(us.map (fun u=>u.value.length)).sum+
      (us.map (fun u=>outputByteCharge u.run)).sum := by
  induction us with
  | nil => simp
  | cons u us ih => simp only [List.map_cons,List.sum_cons,List.length_cons]; omega

/-- Actual row count of the entire allocated UPS list, with no assumed cap. -/
theorem allocated_rows {us : List SchedulerUpsertWitness} {insts : List UpsInst}
    (hl : insts.length=us.length)
    (ha : ∀ tau u I,us[tau]?=some u → insts[tau]?=some I → AllocatedNativeInstance us tau u I) :
    R insts=4*us.length+(us.map (fun u=>u.value.length)).sum+
      (us.map (fun u=>outputByteCharge u.run)).sum := by
  rw [R_eq_sum_rows]
  have hm : insts.map (fun I=>(recsI I).length)=
      us.map (fun u=>4+u.value.length+outputByteCharge u.run) := by
    apply List.ext_getElem (by simpa only [List.length_map] using hl)
    intro k hk hi
    simp only [List.length_map] at hk hi
    simp only [List.getElem_map]
    exact (ha k us[k] insts[k] (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hk)).2.2.2.2.2.2.1
  rw [hm,scheduler_charge_sum]

/-- Ordered allocation also derives the exact instance-index column. -/
theorem allocated_taus {us : List SchedulerUpsertWitness} {insts : List UpsInst}
    (hl : insts.length=us.length)
    (ha : ∀ tau u I,us[tau]?=some u → insts[tau]?=some I → AllocatedNativeInstance us tau u I) :
    insts.map UpsInst.tau=List.range us.length := by
  apply List.ext_getElem (by simpa using hl)
  intro k hk hi
  simp only [List.length_map] at hk
  simp only [List.length_range] at hi
  simp only [List.getElem_map,List.getElem_range]
  exact (ha k us[k] insts[k] (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hk)).1

/-- Present accepted byte budgets prove this bound, which by itself does not
establish the current 2^22 UPS row capacity. -/
theorem allocated_rows_bound {us : List SchedulerUpsertWitness} {insts : List UpsInst}
    (hl : insts.length=us.length)
    (ha : ∀ tau u I,us[tau]?=some u → insts[tau]?=some I → AllocatedNativeInstance us tau u I)
    (hn : us.length≤32) (hv : (us.map (fun u=>u.value.length)).sum≤3146912)
    (ho : (us.map (fun u=>outputByteCharge u.run)).sum≤2131072) :
    R insts≤5278112 := by
  rw [allocated_rows hl ha]
  omega
end ZkFormal.NearV3.Render.UpsGen
