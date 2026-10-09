import ZkFormal.NearV3.Rcpt.Candidates.WalkRanksFlatten
import ZkFormal.Near.Render.Proof.BusEdge

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near

def counterMessages : List Msg→List Msg→Bool→List Msg
  | _,[],_=>[]
  | p,e::es,sd=>(e++[p.count e+(if sd then 1 else 0)])::counterMessages (p++[e]) es sd

def completeCounterMessages (es : List Msg) (sd : Bool) : List Msg :=
  if sd then Near.Render.BusEdge.sendsW es else Near.Render.BusEdge.recvsW es

theorem completeCounterMessages_snoc (es : List Msg) (e : Msg) (sd : Bool) :
    completeCounterMessages (es++[e]) sd=
    completeCounterMessages es sd++[e++[es.count e+(if sd then 1 else 0)]] := by
  cases sd <;> simp [completeCounterMessages,Near.Render.BusEdge.sendsW_snoc,
    Near.Render.BusEdge.recvsW_snoc]

theorem counterMessages_append (p es : List Msg) (sd : Bool) :
    completeCounterMessages p sd++counterMessages p es sd=completeCounterMessages (p++es) sd := by
  induction es generalizing p with
  | nil => simp [counterMessages]
  | cons e es ih =>
    rw [counterMessages,List.append_cons,←completeCounterMessages_snoc,ih]
    simp [List.append_assoc]

theorem counterMessages_empty (es : List Msg) (sd : Bool) :
    counterMessages [] es sd=completeCounterMessages es sd := by
  simpa [completeCounterMessages,Near.Render.BusEdge.sendsW,Near.Render.BusEdge.recvsW]
    using counterMessages_append [] es sd

def edgeKey (st : WStep3) : Option Msg := if st.mode≤1 then some st.e else none
def bitmapKey (st : WStep3) : Option Msg := if st.mode=2 then some [st.e.getD 0 0,st.bm,st.hv] else none

def edgeTraffic (ss : List WStep3) (sd : Bool) : List Msg :=
  ss.filterMap (fun st=>if st.mode≤1 then some (st.e++[st.u+(if sd then 1 else 0)]) else none)
def bitmapTraffic (ss : List WStep3) (sd : Bool) : List Msg :=
  ss.filterMap (fun st=>if st.mode=2 then some ([st.e.getD 0 0,st.bm,st.hv,st.ub+(if sd then 1 else 0)]) else none)

theorem ranked_edge_traffic (p ss : List WStep3) (sd : Bool) :
    edgeTraffic (rankSteps p ss) sd=counterMessages (p.filterMap edgeKey) (ss.filterMap edgeKey) sd := by
  induction ss generalizing p with
  | nil => rfl
  | cons s ss ih =>
    have ht:=ih (p++[s])
    by_cases h : s.mode≤1 <;>
      simp [rankSteps,edgeTraffic,rankWalkStep,edgeKey,h,counterMessages]
    · exact ⟨rfl,by simpa [edgeTraffic,List.filterMap_append,edgeKey,h] using ht⟩
    · simpa [edgeTraffic,List.filterMap_append,edgeKey,h] using ht

theorem ranked_bitmap_traffic (p ss : List WStep3) (sd : Bool) :
    bitmapTraffic (rankSteps p ss) sd=counterMessages (p.filterMap bitmapKey) (ss.filterMap bitmapKey) sd := by
  induction ss generalizing p with
  | nil => rfl
  | cons s ss ih =>
    have ht:=ih (p++[s])
    by_cases h : s.mode=2 <;>
      simp [rankSteps,bitmapTraffic,rankWalkStep,bitmapKey,h,counterMessages]
    · exact ⟨rfl,by simpa [bitmapTraffic,List.filterMap_append,bitmapKey,h] using ht⟩
    · simpa [bitmapTraffic,List.filterMap_append,bitmapKey,h] using ht

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
