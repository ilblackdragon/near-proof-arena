import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderRankList
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedSameLookup
import ZkFormal.NearV3.Rcpt.Candidates.NativeExecutionJointCoverage
import ZkFormal.NearV3.Rcpt.Candidates.ExecutionProviderKeys
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedWindowCoverage
import ZkFormal.NearV3.Rcpt.Candidates.WindowProviderKeys
import ZkFormal.NearV3.Candidates.CompactPhysicalShaBytes

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Render.UpsRelay UpsRows Assembly

/-- Accepted executions construct the SAME post-updated original node providers
and compact UPS readers with complete physical UPB conservation. -/
theorem accepted_query_window_balance {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (resolve : Qv.Candidates.CombinedWalkGen.Resolve) (tw : Nat) (pubw : List Fp)
    (baseI : Nat→UpsInst) (base : Nat→Nat→UpsPartI) :
    ∃writes,∃oldPost : PTrie,∃us : List SchedulerUpsertWitness,∃insts : List UpsInst,∃v : Qv.MainValues,∃ws : List WalkR,
      nativeQueryWalks ((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post)))
        (allLookupQueries (appliedReceipts k w) m.pre v (steps.map ImplicitStepV3.pre) resolve)=some ws ∧
      TableLocal {WalkV3.table with maxLog:=22} (nativeWalkTrace (rankWalks [] ws)) tw pubw ∧
      TableTraffic WalkV3.interactions (nativeWalkTrace (rankWalks [] ws)) tw pubw (walkTraffic3 (rankWalks [] ws)) ∧
      let previous:=ws.flatMap (·.steps)
      let edges:=walkEdgeKeys (ws++upsWalkInventory insts)
      let bmaps:=walkBmapKeys (ws++upsWalkInventory insts)
      edges.length<Algebra.P ∧ bmaps.length<Algebra.P ∧
      SizedAccountRun m.pre writes oldPost ∧
      us.map (fun u=>(u.pre,u.run.output))=(oldPost,m.result.trie)::steps.map (fun s=>(s.pre,s.post)) ∧
      1≤us.length ∧ us.length≤32 ∧
      (∀u∈us,u.Valid ∧ u.pre.wf=true ∧ u.run.parts.length≤403 ∧ fdepth u.pre keyBwState≤400 ∧ u.value.length≤98341) ∧
      preBytes (us.map SchedulerUpsertWitness.pre)≤2000000 ∧
      (us.map (fun u=>outputByteCharge u.run)).sum≤2131072 ∧
      (us.map (fun u=>u.value.length)).sum≤3146912 ∧
      insts.length=us.length ∧
      (∀tau u I,us[tau]?=some u→insts[tau]?=some I→
        AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I ∧
        ExactNativeWalkProviders (us.map (fun u=>(u.pre,u.run.output))) u.run I ∧
        I.ci=u.run.terminal.ix ∧ DispatchNativeWalkProviders (us.map (fun u=>(u.pre,u.run.output))) u.run I ∧
        ∃root,forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau=some root ∧
          NativeReaderOrigin root u.run u.value I) ∧
      let rs:=nativeReplayForest m steps oldPost writes
      (∀r∈rs,r.Valid) ∧
      (records (forestOldInputs rs) (forestNodes 0 0 0 (m.pre::steps.map ImplicitStepV3.pre))).map (fun s=>s.v.ser true)=
        ((rs.map ReplayTree.post).flatMap occs).map (fun t=>(nodeEnc t).map UInt8.toNat) ∧
      (∀e∈edges,e∈headEdgeKeys (forestWalkHeads 0 0 ((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post))))++
        nodeEdgeKeys (forestNodes 0 0 0 (m.pre::steps.map ImplicitStepV3.pre))) ∧
      (∀e∈bmaps,e∈nodeBitmapKeys (forestNodes 0 0 0 (m.pre::steps.map ImplicitStepV3.pre))) ∧
      ∀tu tn pub,
      let ts:=m.pre::steps.map ImplicitStepV3.pre
      let vs:=initializeList 0 (forestNodes 0 0 0 ts)
      let es:=seedValuesFrom 0 (forestBytes ts)
      let cs:=Candidates.StoreClassPartition.chain
        (Candidates.CombinedStoreOccurrences.allOccurrences vs (Candidates.NativeStoreProvenance.valueTau ts) es)
      let provider:=records (forestOldInputs rs) (Candidates.ChainMetadata.assign cs 0 vs)
      let tr:=Candidates.CompactHeight.trace (physicalPrefixUps previous insts)
      let q : UseRequests:=⟨edges,bmaps,Candidates.PhysicalWindowRequests.keys tr tu⟩
      let nodeTrace:=Candidates.TrieCountHeight.node (assignList q 0 provider) pub
      let upsTrace:=patchWindowCounters tr tu (physicalWindowRank tr tu)
      nodeTrace.log tn=22 ∧ TableLocal Candidates.SizeCount.nodeTable nodeTrace tn pub ∧
      TableLocal compactTable upsTrace tu pub ∧
      ∀msg,tableBusCount Candidates.SizeCount.nodeTable.interactions nodeTrace tn pub B_UPB true msg+
        tableBusCount compactTable.interactions upsTrace tu pub B_UPB true msg=
        tableBusCount compactTable.interactions upsTrace tu pub B_UPB false msg+
        tableBusCount Candidates.SizeCount.nodeTable.interactions nodeTrace tn pub B_UPB false msg := by
  obtain ⟨writes,oldPost,us,insts,hr,hpairs,hpos,hlen,hgood,hpre,hout,hval,hcount,hinst,hforest,hbytes,hcoverage⟩:=
    accepted_window_coverage hk hw h hm hv baseI base
  obtain ⟨v,ws,hvvalid,hvreads,hws,hwlocal,hwtraffic,hranges⟩:=
    accepted_same_lookup_physical hk hw h hm hv resolve tw pubw
  let previous:=ws.flatMap (·.steps)
  let edges:=walkEdgeKeys (ws++upsWalkInventory insts)
  let bmaps:=walkBmapKeys (ws++upsWalkInventory insts)
  have hilen : insts.length≤32 := by omega
  obtain ⟨hedges,hbmaps⟩:=hranges insts hilen
  have hcover:=native_execution_joint_coverage m steps oldPost writes us insts hpairs hcount
    (fun tau u I hu hI=>by
      obtain ⟨a,sha,ex,ci,dispatch,origin⟩:=hinst tau u I hu hI
      exact ⟨a.2.2.2.2.1,dispatch,ci⟩) hforest _ ws hws
  refine ⟨writes,oldPost,us,insts,v,ws,hws,hwlocal,hwtraffic,hedges,hbmaps,
    hr,hpairs,hpos,hlen,hgood,hpre,hout,hval,hcount,hinst,hforest,hbytes,hcover.1,hcover.2,?_⟩
  intro tu tn pub
  dsimp only
  have hmeta:=physicalPrefixUps_origins (fun tau u I hu hI=>by
    obtain ⟨a,sha,ex,ci,dispatch,root,hroot,origin⟩:=hinst tau u I hu hI
    exact ⟨a,sha,root,hroot,origin⟩) previous
  have hcount' : (physicalPrefixUps previous insts).length=us.length := hmeta.1.trans hcount
  have hlocal:=(Candidates.CompactPhysicalShaBytes.allocated hcount' hpos hlen
    (fun tau u I hu hI=>⟨(hmeta.2 tau u I hu hI).1,(hmeta.2 tau u I hu hI).2.1⟩) hout tu pub).1
  obtain ⟨hn,hvls⟩:=Candidates.NativeExecutionUsage.inputs hk hw h (by decide) hm hv
  have hids:=(Candidates.StoreClassPartition.combined_metadata _
    (Candidates.NativeStoreProvenance.valueTau (m.pre::steps.map ImplicitStepV3.pre)) _ hn.wf hvls).2.1
  have hprovider:=Candidates.PostNodeLocal.node_ok (forestOldInputs (nativeReplayForest m steps oldPost writes)) _
    (Candidates.ChainMetadata.node_ok _ _ hn hids)
  apply Candidates.PhysicalWindowBalance.concrete _ tu tn pub hlocal edges bmaps _ hprovider hedges hbmaps
  intro r hread
  let rs:=nativeReplayForest m steps oldPost writes
  have hrs : rs.map ReplayTree.pre=m.pre::steps.map ImplicitStepV3.pre := by
    simp [rs,nativeReplayForest,List.map_map,Function.comp_def]
  have hpreEq : us.map SchedulerUpsertWitness.pre=rs.map ReplayTree.post := by
    have hh:=congrArg (List.map Prod.fst) hpairs
    simpa [rs,nativeReplayForest,List.map_map,Function.comp_def] using hh
  have hwf : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl|ht
    · rw [hm.pre]; exact (built_spec _ trieFuel _ _ hm.root_length).2.1
    · obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
      exact (hv.input_facts s hs).2.2
  have hwr : ∀r∈rs,r.pre.wf=true := by
    intro r hr
    exact hwf _ (hrs ▸ List.mem_map.mpr ⟨r,hr,rfl⟩)
  have hbase:=native_window_provider_ok hk hw h hm hv (forestOldInputs rs)
  have hc:=native_physical_window_coverage rs hforest hwr (hpreEq ▸ hpre) us
    (physicalPrefixUps previous insts) hpreEq
    (fun u hu=>⟨(hgood u hu).1,(hgood u hu).2.1⟩) hcount'
    (fun tau u I hu hI=>⟨(hmeta.2 tau u I hu hI).1,(hmeta.2 tau u I hu hI).2.2⟩)
    (by simpa only [hrs] using hbase.wf)
    (by intro s hs x hx; rw [hrs] at hs
        exact native_window_provider_bytes _ hwf (forestOldInputs rs) s hs true x hx)
    tu r hread
  rw [hrs] at hc
  exact nodeWindowKeys_chain_member _ _ _ _ hc

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
