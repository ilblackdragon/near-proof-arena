import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupQueryComplete
import ZkFormal.NearV3.Assembly.QueueWalk

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly Qv Qv.Candidates.CombinedWalkGen

def queueLookupQuery (shards : List Nat) (w : Walk) : NativeLookupQuery :=
  ⟨walkId w.tau w.slot,w.tau,(w.request shards).key⟩

def queueLookupQueries (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve) :
    List NativeLookupQuery := (plan pre v pres resolve).map (queueLookupQuery v.shards)

/-- Every request in the actual queue plan constructs a trie walk in its own
transition prestate, including absent values and repeated requests. -/
theorem queueLookupQueries_complete (pairs : List (PTrie×PTrie)) (pre : PTrie)
    (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (hp : pairs.map Prod.fst=pre::pres)
    (hh : ∀x∈queueInputs pre v pres,∀r∈x.2,r.Holds x.1) :
    ∃ws,nativeQueryWalks pairs (queueLookupQueries pre v pres resolve)=some ws := by
  apply nativeQueryWalks_complete
  intro q hq
  obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hq
  obtain ⟨t,rs,ht,hr,_⟩:=plan_slot hw
  have hf := (hh (t,rs) (List.mem_of_getElem? ht) _ (List.mem_of_getElem? hr)).1
  have hpre : (pairs.map Prod.fst)[w.tau]?=some t := by
    rw [hp,←queueInputs_pre pre v pres]
    simp only [List.getElem?_map,ht,Option.map_some]
  cases hpair : pairs[w.tau]? with
  | none=>simp [List.getElem?_map,hpair] at hpre
  | some pair=>
    obtain ⟨tree,post⟩:=pair
    simp only [List.getElem?_map,hpair,Option.map_some,Option.some.injEq] at hpre
    subst tree
    exact nativeQueryWalk_complete pairs (queueLookupQuery v.shards w) t post _ hpair hf

/-- Native main and implicit execution discharge query availability themselves. -/
theorem native_execution_queue_lookups {k : NearSpecV3.WalkD0} {w : NearSpecV3.StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (resolve : Resolve) :
    ∃v : MainValues,∃ws,
      nativeQueryWalks ((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post)))
        (queueLookupQueries m.pre v (steps.map ImplicitStepV3.pre) resolve)=some ws ∧
      (∀e∈walkEdgeKeys ws,e∈headEdgeKeys (forestWalkHeads 0 0
        ((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post))))++
        nodeEdgeKeys (forestStoreViews (m.pre::steps.map ImplicitStepV3.pre)).nodes) ∧
      (∀e∈walkBmapKeys ws,e∈nodeBitmapKeys (forestStoreViews (m.pre::steps.map ImplicitStepV3.pre)).nodes) := by
  obtain ⟨v,_,_,hh,_⟩:=native_queueInputs hm hv
  have hp : (((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post))).map Prod.fst)=
      m.pre::steps.map ImplicitStepV3.pre := by simp [List.map_map,Function.comp_def]
  obtain ⟨ws,hws⟩:=queueLookupQueries_complete _ m.pre v (steps.map ImplicitStepV3.pre) resolve hp hh
  refine ⟨v,ws,hws,?_⟩
  simpa only [hp] using nativeQueryWalks_coverage _ _ ws hws

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
