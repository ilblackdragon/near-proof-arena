import ZkFormal.NearV3.Assembly.RoutingBoundedRender
import ZkFormal.NearV3.Assembly.QueueRanks

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open ZkFormal.Near

/-- Assign each routing request its prefix-use ordinal for the exact four-field
key. Repeated requests share one provider and advance a single chain. -/
def rankedRequests (keys : List Msg) : List (Msg×Nat) :=
  keys.zipIdx.map (fun x=>(x.1,(keys.take x.2).count x.1))

def requestRanks (keys : List Msg) (key : Msg) : List Nat :=
  (rankedRequests keys).filterMap (fun x=>if x.1==key then some x.2 else none)

theorem requestRanks_exact (keys : List Msg) (key : Msg) :
    requestRanks keys key=List.range' 0 (keys.count key) := by
  have h := prefix_count_ranks (fun x=>x==key) keys 0
  simp only [Nat.zero_add,←List.count_eq_countP] at h
  rw [←h]
  unfold requestRanks rankedRequests
  rw [List.filterMap_map]
  congr 1
  funext x
  by_cases he : x.1=key <;> simp [Function.comp_def,he]

theorem requestRanks_balance (keys : List Msg) (key : Msg) :
    0::(requestRanks keys key).map (·+1)=requestRanks keys key++[keys.count key] := by
  rw [requestRanks_exact,←List.range'_succ_left]
  simpa only [List.range'_succ,Nat.zero_add] using
    (List.range'_1_concat (s:=0) (n:=keys.count key))

/-- Exact natural-message identity including the concrete provider's terminal
usage counter; this remains true when a provider has no users. -/
theorem boundaryEntry_counter_balance (bounds : List (Option NearSpec.Bytes×Option NearSpec.Bytes))
    (keys : List Msg) (x : Nat) :
    let e := boundaryEntry bounds keys x
    (e.rec4++[0])::((requestRanks keys e.rec4).map (fun u=>e.rec4++[u+1]))=
      (requestRanks keys e.rec4).map (fun u=>e.rec4++[u])++[e.rec4++[e.U]] := by
  dsimp only
  rw [boundaryEntry_usage]
  have h := congrArg (List.map (fun u=>(boundaryEntry bounds keys x).rec4++[u]))
    (requestRanks_balance keys (boundaryEntry bounds keys x).rec4)
  simpa only [List.map_cons,List.map_map,List.map_append,List.map_nil,Function.comp_def] using h

theorem rankedRequest_bound (keys : List Msg) {key : Msg} {u : Nat}
    (h : (key,u)∈rankedRequests keys) : u<keys.length := by
  obtain ⟨⟨k,i⟩,hm,he⟩ := List.mem_map.mp h
  have hi := List.mk_mem_zipIdx_iff_getElem?.mp hm
  have hib : i<keys.length := List.getElem?_eq_some_iff.mp hi |>.1
  have hu : u=(keys.take i).count k := by simpa using (Prod.mk.inj he).2.symm
  rw [hu]
  have hb := List.count_le_length (a:=k) (l:=keys.take i)
  rw [List.length_take] at hb
  omega

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
