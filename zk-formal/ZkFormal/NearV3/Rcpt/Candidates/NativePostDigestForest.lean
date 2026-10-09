import ZkFormal.NearV3.Rcpt.Candidates.NativeValueDigestPipeline
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

/-- One VPOST request per activated occurrence ID, irrespective of how often
native execution writes that account. Length is the original authenticated slot. -/
def postDigestFrom (u : Inputs) : Nat→List Bytes→List ZkFormal.Near.Msg
  | _,[]=>[]
  | i,b::bs=>(match u.value i with
      | none=>[]
      | some post=>[digMsg (msgId K_VPOST i) b.length (digest post)])++postDigestFrom u (i+1) bs

theorem postDigestFrom_append (u : Inputs) (i : Nat) (bs cs : List Bytes) :
    postDigestFrom u i (bs++cs)=postDigestFrom u i bs++postDigestFrom u (i+bs.length) cs := by
  induction bs generalizing i with
  | nil=>simp [postDigestFrom]
  | cons b bs ih=>simp [postDigestFrom,ih,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem seed_updated_postSlot (u : Inputs) (t : PTrie) (tau d n v : Nat) :
    postSlotDigests (record u (seedNodeView tau d n v t))=postDigestFrom u v (ownVals t) := by
  cases t with
  | hash h=>rfl
  | ext k c m=>rfl
  | leaf k sl m=>cases sl with
    | ref l h=>rfl
    | val b=>cases hu:u.value v <;>
      simp [postSlotDigests,record,node,slot,seedNodeView,viewNode,viewSlot,hu,
        NodeV3.value,postDigestFrom,ownVals,slotVal]
  | branch sv cs m=>cases sv with
    | none=>rfl
    | some sl=>cases sl with
      | ref l h=>rfl
      | val b=>cases hu:u.value v <;>
        simp [postSlotDigests,record,node,slot,seedNodeView,viewNode,viewSlot,hu,
          NodeV3.value,postDigestFrom,ownVals,optSlotVal,slotVal]

mutual
theorem seed_post_digests (u : Inputs) : ∀(t : PTrie)(tau d n v : Nat),
    (records u (seedNodesT tau d n v t)).flatMap postSlotDigests=postDigestFrom u v (valsOf t)
  | .hash _,_,_,_,_=>rfl
  | .leaf k sl m,tau,d,n,v=>by
    simp [records,seedNodesT,seed_updated_postSlot,valsOf,occs,ownVals]
  | .ext k child m,tau,d,n,v=>by
    simp only [records,seedNodesT,List.map_cons,List.flatMap_cons,seed_updated_postSlot,
      ownVals,postDigestFrom,List.nil_append]
    exact seed_post_digests u child tau (d+1) (n+1) v
  | .branch sl cs m,tau,d,n,v=>by
    simp only [records,seedNodesT,List.map_cons,List.flatMap_cons,seed_updated_postSlot]
    rw [show (List.map (record u) (seedKidsT tau (d+1) (n+1) (v+(optSlotVal sl).length) cs)).flatMap postSlotDigests=
      postDigestFrom u (v+(optSlotVal sl).length) ((kOccs cs).flatMap ownVals) from seed_kid_post_digests u cs tau (d+1) (n+1) (v+(optSlotVal sl).length)]
    exact (postDigestFrom_append u v (optSlotVal sl) ((kOccs cs).flatMap ownVals)).symm

theorem seed_kid_post_digests (u : Inputs) : ∀(cs : Kids)(tau d n v : Nat),
    (records u (seedKidsT tau d n v cs)).flatMap postSlotDigests=postDigestFrom u v ((kOccs cs).flatMap ownVals)
  | .nil,_,_,_,_=>rfl
  | .none cs,tau,d,n,v=>seed_kid_post_digests u cs tau d n v
  | .some child cs,tau,d,n,v=>by
    simp only [seedKidsT,records,List.map_append,List.flatMap_append]
    change (records u (seedNodesT tau d n v child)).flatMap postSlotDigests++
      (records u (seedKidsT tau d (n+tsize child) (v+(valsOf child).length) cs)).flatMap postSlotDigests=_
    rw [seed_post_digests,seed_kid_post_digests]
    simpa only [kOccs,List.flatMap_append,valsOf] using
      (postDigestFrom_append u v (valsOf child) ((kOccs cs).flatMap ownVals)).symm
end

theorem forest_post_digests (u : Inputs) (ts : List PTrie) (tau n v : Nat) :
    (records u (forestNodes tau n v ts)).flatMap postSlotDigests=postDigestFrom u v (forestBytes ts) := by
  induction ts generalizing tau n v with
  | nil=>rfl
  | cons t ts ih=>
    simp only [records,forestNodes,List.map_append,List.flatMap_append]
    change (records u (seedNodesT tau 0 n v t)).flatMap postSlotDigests++
      (records u (forestNodes (tau+1) (n+tsize t) (v+(valsOf t).length) ts)).flatMap postSlotDigests=_
    rw [seed_post_digests,ih]
    exact (postDigestFrom_append u v (valsOf t) (forestBytes ts)).symm

theorem pipeline_postSlot (u : Inputs) (q : UseRequests)
    (cs : List Candidates.StoreDuplicateChain.Entry) (ss : List NodeS3) :
    (assignList q 0 (records u (Candidates.ChainMetadata.assign cs 0 (initializeList 0 ss)))).flatMap postSlotDigests=
      (records u ss).flatMap postSlotDigests := by
  have hh:=(usage_node_views q _ 0).trans
    (records_node_views u ((chain_node_views cs _ 0).trans (initialize_node_views ss 0)))
  let f:=fun v : NodeV3=>match v.value with
    | some (i,l,_,post,w)=>if w then [digMsg (msgId K_VPOST i) l post] else []
    | none=>[]
  have he:=congrArg (List.flatMap f) hh
  simp only [List.flatMap_map] at he
  exact he

theorem native_postSlot_inventory (rs : List ReplayTree) (q : UseRequests)
    (cs : List Candidates.StoreDuplicateChain.Entry) :
    (assignList q 0 (records (forestOldInputs rs) (Candidates.ChainMetadata.assign cs 0
      (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre)))))).flatMap postSlotDigests=
      postDigestFrom (forestOldInputs rs) 0 (forestBytes (rs.map ReplayTree.pre)) := by
  rw [pipeline_postSlot,forest_post_digests]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
