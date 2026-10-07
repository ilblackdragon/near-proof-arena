import ZkFormal.NearV3.Assembly.QueueLocation

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv

/-- Prefix-use ordinal for the walk-side counter chain; the provider retains total users. -/
def queueRankResolve (pre : PTrie) (rs : List ReadRequest) (base slot : Nat) : Nat × Nat :=
  ((valueIndex pre (rs.getD slot ⟨[],none,.raw⟩).key).map
    (fun i => (base+i,queueUsers pre (rs.take slot) i))).getD (0,0)

def queueForestRankResolve : List (PTrie × List ReadRequest) → Nat → Nat → Nat → Nat × Nat
  | [],_,_,_ => (0,0)
  | (pre,rs)::_,base,0,slot => queueRankResolve pre rs base slot
  | (pre,_)::rest,base,tau+1,slot =>
    queueForestRankResolve rest (base+(NearSpecV3.valsOf pre).length) tau slot

/-- All selected prefix-use counters form exactly the consecutive chain. -/
theorem prefix_count_ranks {α : Type} (p : α → Bool) (xs : List α) (start : Nat) :
    xs.zipIdx.filterMap (fun x => if p x.1 then some (start+(xs.take x.2).countP p) else none) =
      List.range' start (xs.countP p) := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
    rw [List.zipIdx_cons']
    by_cases hp : p x = true
    · simpa [List.filterMap_map,Function.comp_def,Prod.map,List.countP_cons,hp,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
        List.range'_succ] using congrArg (start :: ·) (ih (start+1))
    · simpa [List.filterMap_map,Function.comp_def,Prod.map,List.countP_cons,hp] using ih start

theorem queueRankResolve_present {pre : PTrie} {rs : List ReadRequest} {slot i : Nat}
    {r : ReadRequest} (hr : rs[slot]?=some r) (hi : valueIndex pre r.key=some i) (base : Nat) :
    queueRankResolve pre rs base slot=(base+i,queueUsers pre (rs.take slot) i) := by
  simp [queueRankResolve,List.getD_eq_getElem?_getD,hr,hi]

def queueUseRanks (pre : PTrie) (rs : List ReadRequest) (base i : Nat) : List Nat :=
  rs.zipIdx.filterMap (fun x => if valueIndex pre x.1.key == some i
    then some (queueRankResolve pre rs base x.2).2 else none)

private theorem filterMap_congr_mem {α β : Type} (xs : List α) (f g : α → Option β)
    (h : ∀ x ∈ xs, f x=g x) : xs.filterMap f=xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons]
    rw [h x (by simp),ih (fun y hy => h y (by simp [hy]))]

theorem queueUseRanks_eq (pre : PTrie) (rs : List ReadRequest) (base i : Nat) :
    queueUseRanks pre rs base i=List.range' 0 (queueUsers pre rs i) := by
  have he : queueUseRanks pre rs base i = rs.zipIdx.filterMap (fun x =>
      if valueIndex pre x.1.key == some i then some ((rs.take x.2).countP
        (fun r => valueIndex pre r.key == some i)) else none) := by
    apply filterMap_congr_mem
    intro x hx
    by_cases hi : valueIndex pre x.1.key=some i
    · have hr := queueRankResolve_present (List.mk_mem_zipIdx_iff_getElem?.mp hx) hi base
      simp [hi,hr,queueUsers]
    · simp [hi]
  rw [he]
  simpa [queueUsers] using prefix_count_ranks (fun r => valueIndex pre r.key == some i) rs 0

/-- Parser emits zero and consumes the final total; walks advance every
 intermediate counter exactly once. This is the natural-counter bus identity. -/
theorem queueUseRanks_balance (pre : PTrie) (rs : List ReadRequest) (base i : Nat) :
    0 :: (queueUseRanks pre rs base i).map (·+1) =
      queueUseRanks pre rs base i ++ [queueUsers pre rs i] := by
  rw [queueUseRanks_eq]
  rw [← List.range'_succ_left]
  have h := List.range'_1_concat (s := 0) (n := queueUsers pre rs i)
  simpa only [List.range'_succ,Nat.zero_add] using h

theorem queueRankResolve_bound {pre : PTrie} {rs : List ReadRequest} {slot i : Nat}
    {r : ReadRequest} (hr : rs[slot]?=some r) (hi : valueIndex pre r.key=some i) (base : Nat) :
    (queueRankResolve pre rs base slot).2 < rs.length := by
  rw [queueRankResolve_present hr hi base]
  have hc := queueUsers_bound pre (rs.take slot) i
  have ht := List.length_take_le slot rs
  have hs := (List.getElem?_eq_some_iff.mp hr).1
  dsimp only
  omega

open Qv.Candidates.CombinedWalkGen

/-- Generated main walks carry exactly the selected prefix-use chain. -/
theorem mainPlan_useRanks (pre : PTrie) (v : MainValues) (pres : List PTrie) (i : Nat) :
    (mainPlan pre v pres.length (queueForestRankResolve (queueInputs pre v pres) 0)).filterMap
      (fun w => if valueIndex pre (w.request v.shards).key == some i then some w.users else none) =
      List.range' 0 (queueUsers pre (mainRequests pre v) i) := by
  let rs := mainRequests pre v
  let resolve := queueForestRankResolve (queueInputs pre v pres) 0
  let f := fun slot => if valueIndex pre (rs.getD slot ⟨[],none,.raw⟩).key == some i
    then some (queueRankResolve pre rs 0 slot).2 else none
  have hm := congrArg (List.filterMap f) (mainPlan_slots pre v pres.length resolve)
  simp only [List.filterMap_map,Function.comp_def] at hm
  have hl : (mainPlan pre v pres.length resolve).filterMap
      (fun w => if valueIndex pre (w.request v.shards).key == some i then some w.users else none) =
      (mainPlan pre v pres.length resolve).filterMap (fun w => f w.slot) := by
    apply filterMap_congr_mem
    intro w hw
    obtain ⟨ht,hs,hr⟩ := mainPlan_slot hw
    have hr' := congrArg Prod.snd hr
    change w.users=(resolve w.tau w.slot).2 at hr'
    rw [ht] at hr'
    simp only [f,List.getD_eq_getElem?_getD,rs,hs,Option.getD_some]
    rw [hr']
    rfl
  have hh : rs.zipIdx.filterMap (fun x => f x.2)=queueUseRanks pre rs 0 i := by
    apply filterMap_congr_mem
    intro x hx
    have hr := List.mk_mem_zipIdx_iff_getElem?.mp hx
    simp [f,List.getD_eq_getElem?_getD,hr]
  exact hl.trans (hm.trans (hh.trans (queueUseRanks_eq pre rs 0 i)))

end ZkFormal.NearV3.Assembly
