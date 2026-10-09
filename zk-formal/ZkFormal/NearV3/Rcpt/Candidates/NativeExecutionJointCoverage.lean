import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedQueryCoverage
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedRankedWindowBalance

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render Render.UpsGen UpsRows Assembly

/-- Indexed metadata from the chosen accepted UPS witness supplies the exact
combined original-query and rebased-UPS inventory without forest identification
by an independent existential choice. -/
theorem native_execution_joint_coverage
    (m : MainExecutionV3) (steps : List ImplicitStepV3) (oldPost : PTrie)
    (writes : List (List Nat×Bytes)) (us : List SchedulerUpsertWitness) (insts : List UpsInst)
    (hpairs : us.map (fun u=>(u.pre,u.run.output))=
      (oldPost,m.result.trie)::steps.map (fun s=>(s.pre,s.post)))
    (hcount : insts.length=us.length)
    (hinst : ∀(tau : Nat)(u : SchedulerUpsertWitness)(I : UpsInst),us[tau]?=some u→insts[tau]?=some I→
      InstOk I ∧ DispatchNativeWalkProviders (us.map (fun u=>(u.pre,u.run.output))) u.run I ∧ I.ci=u.run.terminal.ix)
    (hvalid : ∀r∈nativeReplayForest m steps oldPost writes,r.Valid)
    (qs : List NativeLookupQuery) (ws : List WalkR)
    (hq : nativeQueryWalks ((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post))) qs=some ws) :
    (∀e∈walkEdgeKeys (ws++upsWalkInventory insts),
      e∈headEdgeKeys (forestWalkHeads 0 0 ((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post))))++
        nodeEdgeKeys (forestNodes 0 0 0 (m.pre::steps.map ImplicitStepV3.pre))) ∧
    (∀e∈walkBmapKeys (ws++upsWalkInventory insts),
      e∈nodeBitmapKeys (forestNodes 0 0 0 (m.pre::steps.map ImplicitStepV3.pre))) := by
  have hu : ∀I∈insts,∃run,InstOk I ∧
      DispatchNativeWalkProviders (us.map (fun u=>(u.pre,u.run.output))) run I ∧ I.ci=run.terminal.ix := by
    intro I hI
    obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp hI
    have hui : i<us.length := by omega
    refine ⟨us[i].run,?_⟩
    exact hinst i us[i] I (by simp [hui]) (by simp [hi,he])
  have hc:=native_rebased_query_ups_coverage (nativeReplayForest m steps oldPost writes)
    ((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post)))
    (us.map (fun u=>(u.pre,u.run.output)))
    (by simp [nativeReplayForest,List.map_map,Function.comp_def])
    (by rw [hpairs];simp [nativeReplayForest,List.map_map,Function.comp_def]) hvalid qs ws insts hq hu
  simpa only [forestStoreViews,List.map_cons,List.map_map,Function.comp_def] using hc

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
