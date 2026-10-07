import ZkFormal.NearV3.Assembly.QueueWalk

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv

/-- Positive selected-provider counters exclude the absent-value resolver default. -/
theorem queueResolve_eq_iff {pre : PTrie} {rs : List ReadRequest} {slot i : Nat}
    {r : ReadRequest} (hr : rs[slot]?=some r) (base : Nat)
    (hu : 0 < queueUsers pre rs i) :
    queueResolve pre rs base slot=(base+i,queueUsers pre rs i) ↔
      valueIndex pre r.key=some i := by
  unfold queueResolve
  rw [List.getD_eq_getElem?_getD,hr]
  cases hi : valueIndex pre r.key with
  | none => simp [hi]; omega
  | some j => simp [hi,Prod.mk.injEq]; intro h; subst j; rfl

/-- The provider's counter is exactly the number of request slots resolving to it.
Repeated requests are counted separately while sharing a single provider. -/
theorem queueResolve_users {pre : PTrie} {rs : List ReadRequest} {i : Nat}
    (base : Nat) (hu : 0 < queueUsers pre rs i) :
    (rs.zipIdx.countP (fun x => queueResolve pre rs base x.2 ==
      (base+i,queueUsers pre rs i))) = queueUsers pre rs i := by
  have h : rs.zipIdx.countP (fun x => queueResolve pre rs base x.2 ==
      (base+i,queueUsers pre rs i)) =
      rs.zipIdx.countP (fun x => valueIndex pre x.1.key == some i) := by
    apply List.countP_congr
    intro x hx
    simpa only [beq_iff_eq] using queueResolve_eq_iff
      (List.mk_mem_zipIdx_iff_getElem?.mp hx) base hu
  rw [h]
  change _ = rs.countP (fun r => valueIndex pre r.key == some i)
  have hh := List.countP_map (p := fun r => valueIndex pre r.key == some i) (f := Prod.fst) (l := rs.zipIdx)
  simpa only [List.zipIdx_map_fst,Function.comp_def] using hh.symm

open Qv.Candidates.CombinedWalkGen

theorem mainPlan_slots (pre : PTrie) (v : MainValues) (K : Nat) (resolve : Resolve) :
    (mainPlan pre v K resolve).map Walk.slot =
      (mainRequests pre v).zipIdx.map Prod.snd := by
  have hs : v.shards.zipIdx.map (fun x => 3+x.2) = List.range' 3 v.shards.length := by
    calc
      _ = (v.shards.zipIdx.map Prod.snd).map (3+·) := (List.map_map ..).symm
      _ = _ := by rw [List.zipIdx_map_snd,List.map_add_range']
  simp only [mainPlan,List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def,mainWalk]
  rw [hs,List.zipIdx_map_snd]
  have hl : (mainRequests pre v).length = v.shards.length+3 := by simp [mainRequests]
  rw [hl]
  simp only [List.range'_succ]
  rfl

theorem mainPlan_provider_users (pre : PTrie) (v : MainValues) (K base i : Nat)
    (resolve : Resolve) (hr : ∀ slot, resolve 0 slot = queueResolve pre (mainRequests pre v) base slot)
    (hu : 0 < queueUsers pre (mainRequests pre v) i) :
    (mainPlan pre v K resolve).countP (fun w => (w.vid,w.users) ==
      (base+i,queueUsers pre (mainRequests pre v) i)) = queueUsers pre (mainRequests pre v) i := by
  have he : (mainPlan pre v K resolve).countP (fun w => (w.vid,w.users) ==
      (base+i,queueUsers pre (mainRequests pre v) i)) =
      (mainPlan pre v K resolve).countP (fun w => queueResolve pre (mainRequests pre v) base w.slot ==
        (base+i,queueUsers pre (mainRequests pre v) i)) := by
    apply List.countP_congr
    intro w hw
    obtain ⟨ht,_,hh⟩ := mainPlan_slot hw
    rw [hh,ht,hr]
  rw [he]
  have hm := mainPlan_slots pre v K resolve
  have hc := congrArg (List.countP (fun slot => queueResolve pre (mainRequests pre v) base slot ==
    (base+i,queueUsers pre (mainRequests pre v) i))) hm
  simp only [List.countP_map,Function.comp_def] at hc
  exact hc.trans (queueResolve_users base hu)

theorem mainPlan_queue_provider_users {pre : PTrie} {v : MainValues} (pres : List PTrie)
    {p : QueueProvider} (hp : p ∈ queueProviders pre (mainRequests pre v) 0 0) :
    (mainPlan pre v pres.length (queueForestResolve (queueInputs pre v pres) 0)).countP
      (fun w => (w.vid,w.users)==(p.vid,p.users)) = p.users := by
  obtain ⟨⟨b,i⟩,hi,rfl⟩ := List.mem_map.mp hp
  exact mainPlan_provider_users pre v pres.length 0 i _
    (fun _ => rfl) (queueUsers_pos hi)

theorem queueProviders_singleton_users {pre : PTrie} {r : ReadRequest} {tau base : Nat}
    {p : QueueProvider} (hp : p ∈ queueProviders pre [r] tau base) : p.users=1 := by
  have h := queueProviders_owner hp
  simp only [List.length_singleton] at h
  omega

/-- The full combined plan charges a main provider exactly its declared users. -/
theorem plan_main_provider_users {pre : PTrie} {v : MainValues} (pres : List PTrie)
    {p : QueueProvider} (hp : p ∈ queueProviders pre (mainRequests pre v) 0 0) :
    (plan pre v pres (queueForestResolve (queueInputs pre v pres) 0)).countP
      (fun w => (w.tau,w.vid,w.users)==(p.tau,p.vid,p.users)) = p.users := by
  have ht := (queueProviders_owner hp).1
  unfold plan
  rw [List.countP_append]
  have hm : (mainPlan pre v pres.length (queueForestResolve (queueInputs pre v pres) 0)).countP
      (fun w => (w.tau,w.vid,w.users)==(p.tau,p.vid,p.users)) =
    (mainPlan pre v pres.length (queueForestResolve (queueInputs pre v pres) 0)).countP
      (fun w => (w.vid,w.users)==(p.vid,p.users)) := by
    apply List.countP_congr
    intro w hw
    have hw' := (mainPlan_slot hw).1
    simp [ht,hw']
  rw [hm,mainPlan_queue_provider_users pres hp]
  have hi : (implicitPlan pres (queueForestResolve (queueInputs pre v pres) 0)).countP
      (fun w => (w.tau,w.vid,w.users)==(p.tau,p.vid,p.users))=0 := by
    apply List.countP_eq_zero.mpr
    intro w hw
    obtain ⟨⟨t,i⟩,_,rfl⟩ := List.mem_map.mp hw
    simp [ht]
  rw [hi,Nat.add_zero]

end ZkFormal.NearV3.Assembly
