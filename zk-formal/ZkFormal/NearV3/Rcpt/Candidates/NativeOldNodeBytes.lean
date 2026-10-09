import ZkFormal.NearV3.Rcpt.Candidates.NativeAllNodePayloads

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

/-- Every concrete original record contains the actual corresponding post-node
bytes, not just its root record. The same global input function serves all rows. -/
theorem oldTreeInputs_all_node_bytes {pre oldPost : PTrie} {writes : List (List Nat×Bytes)}
    (hr : SizedAccountRun pre writes oldPost) (hw : oldPost.wf=true) (tau d : Nat) :
    (records (oldTreeInputs pre oldPost writes) (seedNodesT tau d 0 0 pre)).map (fun s=>s.v.ser true)=
      (occs oldPost).map (fun t=>(nodeEnc t).map UInt8.toNat) := by
  apply nodes_payload_post _ tau d 0 0 hr.forget.skeleton hw
  · intro i t hi
    simpa using oldTreeInputs_child hi
  · intro i a b ha hb
    simpa using oldTreeInputs_payload hr ha hb

/-- Exact physical record ordinal selects the same actual post subtree. -/
theorem oldTreeInputs_node_at {pre oldPost : PTrie} {writes : List (List Nat×Bytes)}
    (hr : SizedAccountRun pre writes oldPost) (hw : oldPost.wf=true) (tau d i : Nat)
    (s : NodeS3) (post : PTrie)
    (hs : (records (oldTreeInputs pre oldPost writes) (seedNodesT tau d 0 0 pre))[i]?=some s)
    (hp : (occs oldPost)[i]?=some post) : s.v.ser true=(nodeEnc post).map UInt8.toNat := by
  have hh:=congrArg (fun xs : List (List Nat)=>xs[i]?) (oldTreeInputs_all_node_bytes hr hw tau d)
  simpa only [List.getElem?_map,hs,hp,Option.map_some,Option.some.injEq] using hh

/-- UPS post-byte readers use a byte from the actual replayed subtree. -/
theorem oldTreeInputs_node_byte {pre oldPost : PTrie} {writes : List (List Nat×Bytes)}
    (hr : SizedAccountRun pre writes oldPost) (hw : oldPost.wf=true) (tau d i p : Nat)
    (s : NodeS3) (post : PTrie)
    (hs : (records (oldTreeInputs pre oldPost writes) (seedNodesT tau d 0 0 pre))[i]?=some s)
    (hp : (occs oldPost)[i]?=some post) :
    (s.v.ser true).getD p 0=((nodeEnc post).map UInt8.toNat).getD p 0 := by
  rw [oldTreeInputs_node_at hr hw tau d i s post hs hp]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
