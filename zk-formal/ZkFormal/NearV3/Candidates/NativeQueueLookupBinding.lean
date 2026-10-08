import ZkFormal.NearV3.Candidates.NativeQueueIds

namespace ZkFormal.NearV3.Candidates.NativeQueueLookupBinding
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen Rcpt.Candidates.NodePostUpdate
open Qv Qv.Candidates.CombinedWalkGen

theorem query_fields (pairs : List (PTrie×PTrie)) (q : NativeLookupQuery)
    (w : WalkR) (h:nativeQueryWalk pairs q=some w) : w.w=q.wid ∧ w.tau=q.tau := by
  cases hp:pairs[q.tau]? with
  | none=>simp [nativeQueryWalk,hp] at h
  | some pair=>
    obtain ⟨tree,post⟩:=pair
    simp only [nativeQueryWalk,hp,bind,Option.bind] at h
    cases hs:nativeLookupSteps (forestLookupNid ((pairs.take q.tau).map Prod.fst))
      (forestLookupVid ((pairs.take q.tau).map Prod.fst)) tree q.key with
    | none=>simp only [hs,reduceCtorEq] at h
    | some ss=>
      simp only [hs] at h
      change some (nativeLookupWalk q.wid q.tau (forestLookupNid ((pairs.take q.tau).map Prod.fst)) tree ss)=some w at h
      have he:=Option.some.inj h
      subst w
      exact ⟨rfl,rfl⟩

theorem planned_result (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (pairs : List (PTrie×PTrie)) (hp:pairs.map Prod.fst=pre::pres)
    (w : Walk) (hw:w∈plan pre v pres (NativeQueueIds.resolve pre v pres))
    (hholds:∀x∈queueInputs pre v pres,∀r∈x.2,r.Holds x.1)
    (walk : WalkR) (hwalk:nativeQueryWalk pairs (queueLookupQuery v.shards w)=some walk) :
    walk.steps.getLast?.map lookupFinal=some (if w.value.isSome then some w.vid else none) := by
  obtain ⟨tree,requests,ht,hr,hvalue⟩:=NativeQueueIds.plan_value pre v pres w hw hholds
  have hpre:(pairs.map Prod.fst)[w.tau]?=some tree := by
    rw [hp,←queueInputs_pre pre v pres]
    simp only [List.getElem?_map,ht,Option.map_some]
  cases hpair:pairs[w.tau]? with
  | none=>simp [List.getElem?_map,hpair] at hpre
  | some pair=>
    obtain ⟨tree',post⟩:=pair
    simp only [List.getElem?_map,hpair,Option.map_some,Option.some.injEq] at hpre
    subst tree'
    have he:=NativeQueueIds.query_result pairs (queueLookupQuery v.shards w) tree post walk hpair hwalk
    simp only [queueLookupQuery,List.map_take,hp] at he
    rw [he,hvalue]

/-- A queue plan using concrete forest IDs binds to the SAME combined native
lookup list even if that list was originally constructed with another resolver. -/
theorem same_walk (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (pairs : List (PTrie×PTrie)) (hp:pairs.map Prod.fst=pre::pres)
    (before after : List NativeLookupQuery) (f : Resolve) (ws : List WalkR)
    (hws:nativeQueryWalks pairs (before++queueLookupQueries pre v pres f++after)=some ws)
    (w : Walk) (hw:w∈plan pre v pres (NativeQueueIds.resolve pre v pres))
    (hholds:∀x∈queueInputs pre v pres,∀r∈x.2,r.Holds x.1) :
    ∃walk∈ws,walk.w=walkId w.tau w.slot ∧ walk.tau=w.tau ∧
      walk.steps.getLast?.map lookupFinal=some (if w.value.isSome then some w.vid else none) := by
  have hq:queueLookupQuery v.shards w∈queueLookupQueries pre v pres f := by
    rw [NativeQueueIds.queries_independent pre v pres f (NativeQueueIds.resolve pre v pres)]
    exact List.mem_map.mpr ⟨w,hw,rfl⟩
  have hx:nativeQueryWalk pairs (queueLookupQuery v.shards w)∈ws.map some := by
    rw [nativeQueryWalks_exact _ _ ws hws]
    exact List.mem_map.mpr ⟨_,List.mem_append_left _ (List.mem_append_right _ hq),rfl⟩
  obtain ⟨walk,hm,he⟩:=List.mem_map.mp hx
  have hf:=query_fields pairs _ walk he.symm
  exact ⟨walk,hm,hf.1,hf.2,planned_result pre v pres pairs hp w hw hholds walk he.symm⟩

theorem ranked_same_walk (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (pairs : List (PTrie×PTrie)) (hp:pairs.map Prod.fst=pre::pres)
    (before after : List NativeLookupQuery) (f : Resolve) (ws : List WalkR)
    (hws:nativeQueryWalks pairs (before++queueLookupQueries pre v pres f++after)=some ws)
    (w : Walk) (hw:w∈plan pre v pres (NativeQueueIds.resolve pre v pres))
    (hholds:∀x∈queueInputs pre v pres,∀r∈x.2,r.Holds x.1) :
    ∃walk∈rankWalks [] ws,walk.w=walkId w.tau w.slot ∧ walk.tau=w.tau ∧
      walk.steps.getLast?.map lookupFinal=some (if w.value.isSome then some w.vid else none) := by
  obtain ⟨walk,hm,hi,ht,hv⟩:=same_walk pre v pres pairs hp before after f ws hws w hw hholds
  obtain ⟨j,hj⟩:=List.mem_iff_getElem?.mp hm
  obtain ⟨p,hp⟩:=NativeRankedAccountIds.ranked_at ws [] j walk hj
  exact ⟨rankWalk p walk,List.mem_of_getElem? hp,hi,ht,
    by rw [NativeRankedAccountIds.final_preserved,hv]⟩

/-- The already allocated native MainValues supplies the queue read evidence;
no second independently chosen queue execution is introduced. -/
theorem native_holds {k : WalkD0} {m : MainExecutionV3} {w : StateWitness}
    {steps : List ImplicitStepV3} {last : Bytes}
    (hv:ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (v : MainValues) (hvalid:v.Valid) (hreads:v.Reads m.pre m.pre m.pre) :
    ∀x∈queueInputs m.pre v (steps.map ImplicitStepV3.pre),∀r∈x.2,r.Holds x.1 := by
  intro x hx r hr
  simp only [queueInputs,List.mem_cons,List.mem_map] at hx
  rcases hx with rfl|⟨pre,⟨s,hs,rfl⟩,rfl⟩
  · exact mainRequests_hold m.pre v hvalid hreads r hr
  · have he:r=missingRequest s.pre:=by simpa using hr
    subst r
    exact hv.missing_requests s hs

theorem accepted {k : WalkD0} {m : MainExecutionV3} {w : StateWitness}
    {steps : List ImplicitStepV3} {last : Bytes}
    (hv:ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (v : MainValues) (hvalid:v.Valid) (hreads:v.Reads m.pre m.pre m.pre)
    (f : Resolve) (ws : List WalkR)
    (hws:nativeQueryWalks ((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post)))
      (allLookupQueries (appliedReceipts k w) m.pre v (steps.map ImplicitStepV3.pre) f)=some ws) :
    ∀q∈plan m.pre v (steps.map ImplicitStepV3.pre)
      (NativeQueueIds.resolve m.pre v (steps.map ImplicitStepV3.pre)),
      (∃walk∈ws,walk.w=walkId q.tau q.slot ∧ walk.tau=q.tau ∧
        walk.steps.getLast?.map lookupFinal=some (if q.value.isSome then some q.vid else none)) ∧
      (∃walk∈rankWalks [] ws,walk.w=walkId q.tau q.slot ∧ walk.tau=q.tau ∧
        walk.steps.getLast?.map lookupFinal=some (if q.value.isSome then some q.vid else none)) := by
  have hh:=native_holds hv v hvalid hreads
  have hp:(((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post))).map Prod.fst)=
      m.pre::steps.map ImplicitStepV3.pre:=by simp [List.map_map,Function.comp_def]
  have hs:nativeQueryWalks ((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post)))
      ((accountLookupQueries (appliedReceipts k w)++accessKeyLookupQueries (appliedReceipts k w))++
        queueLookupQueries m.pre v (steps.map ImplicitStepV3.pre) f++[])=some ws:=by
    simpa only [List.append_nil,allLookupQueries] using hws
  intro q hq
  exact ⟨same_walk _ _ _ _ hp _ [] f ws hs q hq hh,
    ranked_same_walk _ _ _ _ hp _ [] f ws hs q hq hh⟩

end ZkFormal.NearV3.Candidates.NativeQueueLookupBinding
