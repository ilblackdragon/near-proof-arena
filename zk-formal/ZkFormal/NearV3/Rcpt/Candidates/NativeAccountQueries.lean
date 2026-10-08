import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountPrestate

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpec.TransferV1 NearSpecV3 ReexecV3D0 Assembly ZkFormal.Near Render.UpsGen

/-- One receiver lookup for each actual receipt occurrence; IDs match KEYNIB r. -/
def accountLookupQueries (rs : List Receipt) : List NativeLookupQuery :=
  rs.zipIdx.map (fun (r,i)=>⟨i,0,accountKeyPath r.receiverId⟩)

theorem accountLookupQueries_complete {ctx : ApplyCtx} {pre : PTrie} {rs : List Receipt}
    {out : MainOut} (hw : TrieShape pre) (h : applyNewChunk prims ctx pre rs=.ok out)
    (after : List (PTrie×PTrie)) :
    ∃ws,nativeQueryWalks ((pre,out.trie)::after) (accountLookupQueries rs)=some ws := by
  apply nativeQueryWalks_complete
  intro q hq
  obtain ⟨⟨r,i⟩,hr,rfl⟩:=List.mem_map.mp hq
  have hr' : r∈rs := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hr)
  have hk:=newchunk_accounts_prestate hw h r hr'
  cases hf : pre.find (accountKeyPath r.receiverId) with
  | none=>exact False.elim (hk hf)
  | some value=>exact nativeQueryWalk_complete _ _ pre out.trie value rfl hf

/-- Account lookups use the same native execution forest as queue and UPS. -/
theorem native_execution_account_lookups {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} (hm : m.NativeValid k w) (steps : List ImplicitStepV3) :
    ∃ws,nativeQueryWalks ((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post)))
      (accountLookupQueries (appliedReceipts k w))=some ws ∧
      (∀e∈walkEdgeKeys ws,e∈headEdgeKeys (forestWalkHeads 0 0
        ((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post))))++
        nodeEdgeKeys (forestStoreViews (m.pre::steps.map ImplicitStepV3.pre)).nodes) ∧
      (∀e∈walkBmapKeys ws,e∈nodeBitmapKeys (forestStoreViews (m.pre::steps.map ImplicitStepV3.pre)).nodes) := by
  have hw : m.pre.wf=true := by
    rw [hm.pre]
    exact (built_spec w.main.values trieFuel k.slotB2.prevStateRoot _ hm.root_length).2.1
  obtain ⟨ws,hws⟩:=accountLookupQueries_complete (TrieShape.of_wf _ hw) hm.run (steps.map (fun s=>(s.pre,s.post)))
  refine ⟨ws,hws,?_⟩
  simpa only [List.map_cons,List.map_map,Function.comp_def] using nativeQueryWalks_coverage _ _ ws hws

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
