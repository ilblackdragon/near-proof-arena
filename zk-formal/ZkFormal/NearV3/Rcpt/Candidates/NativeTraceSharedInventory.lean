import ZkFormal.NearV3.Rcpt.Candidates.NativeTraceExactInstances
import ZkFormal.NearV3.Rcpt.Candidates.ForestProviderPrestate

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen UpsRows Assembly

/-- Chosen native query walks and allocated UPS instances share the exact
ordered prestate providers. Scheduler intermediate posts are kept separate. -/
theorem native_trace_shared_inventory {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hlen : steps.length≤31) (hwf : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true)
    (qs : List NativeLookupQuery) (ws : List WalkR)
    (hq : nativeQueryWalks ((m.pre,m.result.trie)::steps.map (fun s => (s.pre,s.post))) qs=some ws)
    (baseI : Nat→UpsInst) (base : Nat→Nat→UpsPartI) :
    ∃us : List SchedulerUpsertWitness,∃Is : List UpsInst,
      us.map SchedulerUpsertWitness.pre=m.pre::steps.map ImplicitStepV3.pre ∧
      Is.length=us.length ∧ Is.length≤32 ∧
      (∀tau u I,us[tau]?=some u→Is[tau]?=some I→AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I) ∧
      (∀e∈walkEdgeKeys (ws++upsWalkInventory Is),e∈
        headEdgeKeys (forestWalkHeads 0 0 ((m.pre,m.result.trie)::steps.map (fun s => (s.pre,s.post))))++
        nodeEdgeKeys (forestStoreViews (m.pre::steps.map ImplicitStepV3.pre)).nodes) ∧
      (∀e∈walkBmapKeys (ws++upsWalkInventory Is),e∈
        nodeBitmapKeys (forestStoreViews (m.pre::steps.map ImplicitStepV3.pre)).nodes) := by
  obtain ⟨us,Is,hpre,_,hlenU,hIs,_,_,_,hall⟩:=native_trace_exact_instances hk hw h hm hv hlen hwf baseI base
  have hp : (us.map (fun u => (u.pre,u.run.output))).map Prod.fst=
      ((m.pre,m.result.trie)::steps.map (fun s => (s.pre,s.post))).map Prod.fst := by
    simpa only [List.map_map,Function.comp_def,List.map_cons] using hpre
  have hc:=native_query_ups_prestate_coverage _ _ hp qs ws Is hq (by
    intro I hi
    obtain ⟨i,hget⟩:=List.mem_iff_getElem?.mp hi
    have hib : i<us.length := by
      obtain ⟨hh,_⟩:=List.getElem?_eq_some_iff.mp hget
      omega
    have hu:=List.getElem?_eq_getElem hib
    have hh:=hall i us[i] I hu hget
    exact ⟨us[i].run,hh.1.2.2.2.2.1,hh.2.2.2.2,hh.2.2.2.1⟩)
  refine ⟨us,Is,hpre,hIs,by omega,?_,?_⟩
  · intro tau u I hu hi
    have hh:=hall tau u I hu hi
    exact ⟨hh.1,hh.2.1⟩
  · simpa only [List.map_cons,List.map_map,Function.comp_def] using hc

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
