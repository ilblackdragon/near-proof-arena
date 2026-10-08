import ZkFormal.NearV3.Rcpt.Candidates.NodeUsageTraffic
import ZkFormal.NearV3.Extract.WalkView

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Algebra

def walkEdgeKeys (ws : List WalkR) : List Msg :=
  (ws.flatMap (·.steps)).filterMap (fun st=>if st.mode≤1 then some st.e else none)

def walkBmapKeys (ws : List WalkR) : List Msg :=
  (ws.flatMap (·.steps)).filterMap (fun st=>if st.mode=2 then some [st.e.getD 0 0,st.bm,st.hv] else none)

theorem walk_request_bounds (ws : List WalkR) (h : WalkWf3 ws) :
    (walkEdgeKeys ws).length<P ∧ (walkBmapKeys ws).length<P := by
  have he:=List.length_filterMap_le (l:=ws.flatMap (·.steps))
    (f:=fun st=>if st.mode≤1 then some st.e else none)
  have hb:=List.length_filterMap_le (l:=ws.flatMap (·.steps))
    (f:=fun st=>if st.mode=2 then some [st.e.getD 0 0,st.bm,st.hv] else none)
  have hn:=h.nrows
  change (walkEdgeKeys ws).length<2013265921 ∧ (walkBmapKeys ws).length<2013265921
  unfold walkEdgeKeys walkBmapKeys
  omega

/-- Counter-only update using the same earlier physical walk-step sequence.
The EDGE sequence includes START; its provider is the corresponding head. -/
def rankWalkStep (previous : List WStep3) (st : WStep3) : WStep3 :=
  {st with
    u := (previous.filterMap (fun s=>if s.mode≤1 then some s.e else none)).count st.e
    ub := (previous.filterMap (fun s=>if s.mode=2 then some [s.e.getD 0 0,s.bm,s.hv] else none)).count
      [st.e.getD 0 0,st.bm,st.hv]}

theorem rankWalkStep_ok (previous : List WStep3) (st : WStep3) (last : Bool)
    (h : StepOk st last) : StepOk (rankWalkStep previous st) last :=
  ⟨h.mode,h.elen,h.stepE,h.absK,h.absB,h.lastEnd⟩

theorem rankWalkStep_bounds (previous : List WStep3) (st : WStep3) :
    (rankWalkStep previous st).u≤previous.length ∧ (rankWalkStep previous st).ub≤previous.length := by
  constructor
  · exact Nat.le_trans List.count_le_length (List.length_filterMap_le ..)
  · exact Nat.le_trans List.count_le_length (List.length_filterMap_le ..)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
