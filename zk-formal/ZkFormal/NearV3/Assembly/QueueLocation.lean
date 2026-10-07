import ZkFormal.NearV3.Assembly.QueueUsers

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv

/-- Invert provider allocation without losing its concrete local resolver. -/
theorem queueForest_provider_location : ∀ xs start base (p : QueueProvider),
    p ∈ queueForestProviders start base xs →
    ∃ j t rs offset, xs[j]?=some (t,rs) ∧ p.tau=start+j ∧
      p ∈ queueProviders t rs (start+j) offset ∧
      ∀ slot, queueForestResolve xs base j slot=queueResolve t rs offset slot
  | [],_,_,_,h => by simp [queueForestProviders] at h
  | (t,rs)::rest,start,base,p,h => by
    simp only [queueForestProviders,List.mem_append] at h
    rcases h with h | h
    · refine ⟨0,t,rs,base,rfl,?_,?_,fun _ => rfl⟩
      · simpa using (queueProviders_owner h).1
      · simpa using h
    · obtain ⟨j,u,us,offset,hj,ht,hp,hr⟩ := queueForest_provider_location rest
        (start+1) (base+(NearSpecV3.valsOf t).length) p h
      refine ⟨j+1,u,us,offset,?_,?_,?_,?_⟩
      · simpa using hj
      · omega
      · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hp
      · intro slot; exact hr slot

theorem queueProvider_resolver {pre : PTrie} {rs : List ReadRequest} {tau base : Nat}
    {p : QueueProvider} (hp : p ∈ queueProviders pre rs tau base) :
    ∃ slot r, rs[slot]?=some r ∧ pre.find r.key=some (some p.bytes) ∧
      queueResolve pre rs base slot=(p.vid,p.users) := by
  obtain ⟨⟨b,i⟩,hi,rfl⟩ := List.mem_map.mp hp
  obtain ⟨hb,r,hr,hi⟩ := queueSelected_mem.mp hi
  obtain ⟨slot,hs⟩ := List.mem_iff_getElem?.mp hr
  refine ⟨slot,r,hs,valueIndex_bytes hi hb,?_⟩
  simp [queueResolve,List.getD_eq_getElem?_getD,hs,hi]

open Qv.Candidates.CombinedWalkGen

theorem implicitPlan_one (pres : List PTrie) (resolve : Resolve) (j vid users : Nat)
    (hj : j < pres.length) (hr : resolve (j+1) 0=(vid,users)) :
    (implicitPlan pres resolve).countP (fun w => (w.tau,w.vid,w.users)==(j+1,vid,users))=1 := by
  simp only [implicitPlan,List.countP_map,Function.comp_def]
  have he : pres.zipIdx.countP (fun x =>
      (x.2+1,(resolve (x.2+1) 0).1,(resolve (x.2+1) 0).2)==(j+1,vid,users)) =
      pres.zipIdx.countP (fun x => x.2==j) := by
    apply List.countP_congr
    intro x hx
    by_cases h : x.2=j
    · simp [h,hr]
    · simp [h]
  rw [he]
  have hc := List.countP_map (p := fun i => i==j) (f := Prod.snd) (l := pres.zipIdx)
  simp only [Function.comp_def] at hc
  rw [← hc,List.zipIdx_map_snd]
  change List.count j (List.range' 0 pres.length)=1
  simp [List.count_range_1',hj]

/-- Every allocated queue provider has exactly its advertised multiplicity in
 the entire generated walk plan, including implicit transitions. -/
theorem plan_provider_users {pre : PTrie} {v : MainValues} (pres : List PTrie)
    {p : QueueProvider} (hp : p ∈ queueForestProviders 0 0 (queueInputs pre v pres)) :
    (plan pre v pres (queueForestResolve (queueInputs pre v pres) 0)).countP
      (fun w => (w.tau,w.vid,w.users)==(p.tau,p.vid,p.users)) = p.users := by
  obtain ⟨j,t,rs,offset,hj,ht,hp',hr⟩ := queueForest_provider_location _ 0 0 p hp
  cases j with
  | zero =>
    simp only [queueInputs,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hj
    obtain ⟨rfl,rfl⟩ := hj
    -- The actual head allocator retains its original base zero.
    simp only [queueInputs,queueForestProviders,List.mem_append] at hp
    rcases hp with hp | hp
    · exact plan_main_provider_users pres hp
    · have hb := queueForestProviders_bounds _ _ _ hp
      simp only [Nat.zero_add,Nat.add_zero] at ht
      omega
  | succ j =>
    simp only [queueInputs,List.getElem?_cons_succ,List.getElem?_map] at hj
    obtain ⟨u,hu,he⟩ := Option.map_eq_some_iff.mp hj
    cases he
    have hus := queueProviders_singleton_users hp'
    obtain ⟨slot,r,hs,hfind,hresolve⟩ := queueProvider_resolver hp'
    have hslot : slot=0 := by
      cases slot with
      | zero => rfl
      | succ n => simp at hs
    subst slot
    have hresolved : queueForestResolve (queueInputs pre v pres) 0 (j+1) 0=(p.vid,p.users) :=
      (hr 0).trans hresolve
    simp only [Nat.zero_add] at ht
    unfold plan
    rw [List.countP_append]
    have hmain : (mainPlan pre v pres.length (queueForestResolve (queueInputs pre v pres) 0)).countP
        (fun w => (w.tau,w.vid,w.users)==(p.tau,p.vid,p.users))=0 := by
      apply List.countP_eq_zero.mpr
      intro w hw
      have hw' := (mainPlan_slot hw).1
      simp [hw',ht]
    rw [hmain,Nat.zero_add,ht]
    rw [implicitPlan_one pres _ j p.vid p.users (List.getElem?_eq_some_iff.mp hu).1 hresolved]
    exact hus.symm

end ZkFormal.NearV3.Assembly
