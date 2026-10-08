import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupQueries
import ZkFormal.NearV3.Rcpt.Candidates.HeadNodeBalance

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

def nativeQueryWalks (pairs : List (PTrie×PTrie)) : List NativeLookupQuery→Option (List WalkR)
  | []=>some []
  | q::qs=>do
    let w ← nativeQueryWalk pairs q
    let ws ← nativeQueryWalks pairs qs
    pure (w::ws)

theorem nativeQueryWalks_exact (pairs : List (PTrie×PTrie)) : ∀qs ws,
    nativeQueryWalks pairs qs=some ws→
    ws.map some=qs.map (nativeQueryWalk pairs)
  | [],ws,h=>by cases h;rfl
  | q::qs,ws,h=>by
    cases hq : nativeQueryWalk pairs q with
    | none=>simp [nativeQueryWalks,hq] at h
    | some w=>
      cases ht : nativeQueryWalks pairs qs with
      | none=>simp [nativeQueryWalks,hq,ht] at h
      | some tail=>
        simp [nativeQueryWalks,hq,ht] at h
        subst ws
        simp only [List.map_cons,hq,nativeQueryWalks_exact pairs qs tail ht]

theorem nativeQueryWalks_length (pairs : List (PTrie×PTrie)) (qs : List NativeLookupQuery)
    (ws : List WalkR) (h : nativeQueryWalks pairs qs=some ws) : ws.length=qs.length := by
  have hh:=congrArg List.length (nativeQueryWalks_exact pairs qs ws h)
  simpa only [List.length_map] using hh

theorem nativeQueryWalks_coverage (pairs : List (PTrie×PTrie)) (qs : List NativeLookupQuery)
    (ws : List WalkR) (h : nativeQueryWalks pairs qs=some ws) :
    (∀e∈walkEdgeKeys ws,e∈headEdgeKeys (forestWalkHeads 0 0 pairs)++
      nodeEdgeKeys (forestStoreViews (pairs.map Prod.fst)).nodes) ∧
    (∀e∈walkBmapKeys ws,e∈nodeBitmapKeys (forestStoreViews (pairs.map Prod.fst)).nodes) := by
  have hm : ∀w∈ws,∃q∈qs,nativeQueryWalk pairs q=some w := by
    intro w hw
    have hh : some w∈ws.map some := List.mem_map.mpr ⟨w,hw,rfl⟩
    rw [nativeQueryWalks_exact pairs qs ws h] at hh
    exact List.mem_map.mp hh
  constructor
  · intro e he
    obtain ⟨s,hs,he⟩:=List.mem_filterMap.mp he
    obtain ⟨w,hw,hs⟩:=List.mem_flatMap.mp hs
    obtain ⟨q,hq,hqw⟩:=hm w hw
    split at he
    · rename_i ha
      cases he
      exact (nativeQueryWalk_coverage pairs q w hqw).1 s hs ha
    · cases he
  · intro e he
    obtain ⟨s,hs,he⟩:=List.mem_filterMap.mp he
    obtain ⟨w,hw,hs⟩:=List.mem_flatMap.mp hs
    obtain ⟨q,hq,hqw⟩:=hm w hw
    split at he
    · rename_i ha
      cases he
      exact (nativeQueryWalk_coverage pairs q w hqw).2 s hs ha
    · cases he

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
