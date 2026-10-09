import ZkFormal.NearV3.Rcpt.Candidates.UpsActiveCoverage
import ZkFormal.NearV3.Render.Ups.AcceptedExactTrafficList

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen UpsRows Assembly

/-- Exactly the four physical UPS walk rows; this is a traffic inventory, not
an assertion that every remaining field satisfies the separate Walk table. -/
def upsWalkInventory (insts : List Render.UpsInst) : List WalkR :=
  insts.map (fun I=>{w:=I.tau,tau:=I.tau,steps:=List.ofFn (fun i : Fin 4=>step I i)})

theorem ups_edge_inventory_coverage (pairs : List (PTrie×PTrie)) (insts : List Render.UpsInst)
    (h : ∀I∈insts,∃run,InstOk I ∧ ExactNativeWalkProviders pairs run I ∧ I.ci=run.terminal.ix) :
    ∀e∈walkEdgeKeys (upsWalkInventory insts),
      e∈headEdgeKeys (forestWalkHeads 0 0 pairs)++nodeEdgeKeys (forestStoreViews (pairs.map Prod.fst)).nodes := by
  intro e he
  obtain ⟨st,hs,he⟩:=List.mem_filterMap.mp he
  obtain ⟨w,hw,hs⟩:=List.mem_flatMap.mp hs
  obtain ⟨I,hI,rfl⟩:=List.mem_map.mp hw
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hs
  split at he
  · rename_i hm
    simp only [Option.some.injEq] at he
    subst e
    obtain ⟨run,ho,hp,hci⟩:=h I hI
    exact native_ups_active_edges pairs run I ho hp hci i i.isLt hm
  · contradiction

theorem ups_bitmap_inventory_coverage (pairs : List (PTrie×PTrie)) (insts : List Render.UpsInst)
    (h : ∀I∈insts,∃run,InstOk I ∧ DispatchNativeWalkProviders pairs run I ∧ I.ci=run.terminal.ix) :
    ∀e∈walkBmapKeys (upsWalkInventory insts),e∈nodeBitmapKeys (forestStoreViews (pairs.map Prod.fst)).nodes := by
  intro e he
  obtain ⟨st,hs,he⟩:=List.mem_filterMap.mp he
  obtain ⟨w,hw,hs⟩:=List.mem_flatMap.mp hs
  obtain ⟨I,hI,rfl⟩:=List.mem_map.mp hw
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hs
  split at he
  · rename_i hm
    simp only [Option.some.injEq] at he
    subst e
    obtain ⟨run,ho,hp,hci⟩:=h I hI
    exact native_ups_active_bmaps pairs run I ho hp hci i i.isLt hm
  · contradiction

theorem ups_inventory_rows (insts : List Render.UpsInst) :
    ((upsWalkInventory insts).flatMap (·.steps)).length=4*insts.length := by
  induction insts with
  | nil=>rfl
  | cons I insts ih=>
    simp only [upsWalkInventory,List.map_cons,List.flatMap_cons,List.length_append,List.length_ofFn,
      List.length_cons] at *
    omega

open NearSpecV3 in
theorem accepted_ups_inventory {cb wb : Bytes} {claim : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok claim) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    (baseI : Nat→Render.UpsInst) (base : Nat→Nat→Render.UpsPartI) :
    ∃(us : List SchedulerUpsertWitness)(insts : List Render.UpsInst),
      insts.length=us.length ∧ 1≤us.length ∧ us.length≤32 ∧
      ((upsWalkInventory insts).flatMap (·.steps)).length≤128 ∧
      (∀I∈insts,∃tau u,us[tau]?=some u ∧ insts[tau]?=some I ∧ AllocatedNativeInstance us tau u I) ∧
      (∀e∈walkEdgeKeys (upsWalkInventory insts),e∈headEdgeKeys (forestWalkHeads 0 0 (us.map (fun u=>(u.pre,u.run.output))))++
        nodeEdgeKeys (forestStoreViews (us.map SchedulerUpsertWitness.pre)).nodes) ∧
      (∀e∈walkBmapKeys (upsWalkInventory insts),e∈nodeBitmapKeys (forestStoreViews (us.map SchedulerUpsertWitness.pre)).nodes) := by
  obtain ⟨us,insts,hpos,hlen,hcount,_,_,_,hi⟩:=checkD0a_exactNativeTrafficList hk hw h baseI base
  have hm : ∀I∈insts,∃tau u,us[tau]?=some u ∧ insts[tau]?=some I ∧
      AllocatedNativeInstance us tau u I ∧ ExactNativeWalkProviders (us.map (fun u=>(u.pre,u.run.output))) u.run I ∧
      I.ci=u.run.terminal.ix ∧ DispatchNativeWalkProviders (us.map (fun u=>(u.pre,u.run.output))) u.run I := by
    intro I hI
    obtain ⟨tau,ht,hget⟩:=List.mem_iff_getElem.mp hI
    have hu : tau<us.length := by omega
    have hI' : insts[tau]?=some I := by rw [List.getElem?_eq_getElem ht,hget]
    have hu' : us[tau]?=some us[tau] := List.getElem?_eq_getElem hu
    have hh:=hi tau us[tau] I hu' hI'
    exact ⟨tau,us[tau],hu',hI',hh.1,hh.2.2⟩
  refine ⟨us,insts,hcount,hpos,hlen,?_,?_,?_,?_⟩
  · rw [ups_inventory_rows];omega
  · intro I hI;obtain ⟨tau,u,hu,hi,ho,_⟩:=hm I hI;exact ⟨tau,u,hu,hi,ho⟩
  · have hc:=ups_edge_inventory_coverage (us.map (fun u=>(u.pre,u.run.output))) insts (by
      intro I hI;obtain ⟨_,u,_,_,ho,hp,hci,_⟩:=hm I hI
      exact ⟨u.run,ho.2.2.2.2.1,hp,hci⟩)
    simpa only [List.map_map,Function.comp_def] using hc
  · have hc:=ups_bitmap_inventory_coverage (us.map (fun u=>(u.pre,u.run.output))) insts (by
      intro I hI;obtain ⟨_,u,_,_,ho,_,hci,hp⟩:=hm I hI
      exact ⟨u.run,ho.2.2.2.2.1,hp,hci⟩)
    simpa only [List.map_map,Function.comp_def] using hc

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
