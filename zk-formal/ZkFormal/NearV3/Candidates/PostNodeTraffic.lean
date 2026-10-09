import ZkFormal.NearV3.Candidates.PostNodeLocal
import ZkFormal.NearV3.Candidates.NodeUseTraffic
import ZkFormal.NearV3.Rcpt.Candidates.NodePostProviders

namespace ZkFormal.NearV3.Candidates.PostNodeTraffic
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

/-- EDGE counters retain the original provider inventory after post payloads
are installed and usage counts assigned. -/
theorem edge (u : Inputs) (q : UseRequests) (vs : List NodeS3) (hn : NodeOk vs)
    (he : q.edges.length<Algebra.P) (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P)
    (t : Nat) (pub : List Fp) (msg : List Fp) :
    tableBusCount SizeCount.nodeTable.interactions
      (TrieCountHeight.node (assignList q 0 (records u vs)) pub) t pub B_EDGE true msg=
      (((nodeEdgeKeys vs).map (·++[0])).map Msg.toFp).count msg ∧
    tableBusCount SizeCount.nodeTable.interactions
      (TrieCountHeight.node (assignList q 0 (records u vs)) pub) t pub B_EDGE false msg=
      (((nodeEdgeKeys vs).map (fun e=>e++[q.edges.count e])).map Msg.toFp).count msg := by
  simpa only [records_edge_keys] using
    NodeUseTraffic.edge q (records u vs) (PostNodeLocal.node_ok u vs hn) he hb hu t pub msg

/-- Window counters are assigned against updated payloads. Their keys include
the post byte, so assigning counters before updating is not interchangeable. -/
theorem windows (u : Inputs) (q : UseRequests) (vs : List NodeS3) (hn : NodeOk vs)
    (he : q.edges.length<Algebra.P) (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P)
    (t : Nat) (pub : List Fp) (msg : List Fp) :
    tableBusCount SizeCount.nodeTable.interactions
      (TrieCountHeight.node (assignList q 0 (records u vs)) pub) t pub B_UPB false msg=
      (((vs.zip (List.range vs.length)).flatMap fun (s,n)=>
        (List.range (s.v.ser false).length).map fun p=>
          windowKey n p (record u s)++[q.windows.count (windowKey n p (record u s))]).map Msg.toFp).count msg := by
  have h:=NodeUseTraffic.windows q (records u vs) (PostNodeLocal.node_ok u vs hn) he hb hu t pub msg
  simpa only [records,List.length_map,List.zip_map_left,List.flatMap_map,
    Function.comp_def,Prod.map,id_eq,record,node_pre] using h

end ZkFormal.NearV3.Candidates.PostNodeTraffic
