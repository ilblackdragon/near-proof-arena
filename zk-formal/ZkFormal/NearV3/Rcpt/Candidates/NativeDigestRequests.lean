import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestOwnership
import ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

def ownerDigests (u : Inputs) (o : Nat×PTrie) : List Msg :=
  [digMsg (msgId K_NPRE o.1) (nodeEnc o.2).length (o.2.hashOf.map UInt8.toNat),
   digMsg (msgId K_NPOST o.1) (nodeEnc o.2).length (digest (u.child o.1))]

def childDigests (s : NodeS3) : List Msg :=
  s.v.revealed.flatMap fun (c,l,_,pre,post)=>
    [digMsg (msgId K_NPRE c) l pre,digMsg (msgId K_NPOST c) l post]

def kidDigests (u : Inputs) (k : NKid) : List Msg :=
  match kid u k with
  | .node c l _ pre post=>[digMsg (msgId K_NPRE c) l pre,digMsg (msgId K_NPOST c) l post]
  | _=>[]

theorem viewKid_digests (u : Inputs) (n : Nat) (t : PTrie) :
    kidDigests u (viewKid n t)=(rootOwner n t).flatMap (ownerDigests u) := by
  cases t <;> simp [kidDigests,viewKid,rootOwner,isNode,kid,ownerDigests]

theorem viewKids_digests (u : Inputs) : ∀(cs : Kids)(n : Nat),
    (viewKids n cs).flatMap (kidDigests u)=(kidRootOwners n cs).flatMap (ownerDigests u)
  | .nil,n=>rfl
  | .none cs,n=>by simpa [viewKids,kidRootOwners,kidDigests,kid] using viewKids_digests u cs n
  | .some c cs,n=>by simp only [viewKids,kidRootOwners,List.flatMap_cons,List.flatMap_append,
      viewKid_digests,viewKids_digests]

private theorem kids_flat (u : Inputs) : ∀ks : List NKid,
    ((ks.map (kid u)).filterMap (fun
      | .node c l r pre po=>some (c,l,r,pre,po)
      | _=>none)).flatMap (fun (c,l,_,pre,po)=>[digMsg (msgId K_NPRE c) l pre,digMsg (msgId K_NPOST c) l po])=
      ks.flatMap (kidDigests u)
  | []=>rfl
  | k::ks=>by
    cases k <;> simp only [List.map_cons,kid,List.filterMap_cons,List.flatMap_cons,List.flatMap_nil,
      List.flatMap_cons,kidDigests,List.nil_append,kids_flat]

/-- Actual seed-record child DIGEST requests carry each immediate child's
allocated ID, pre hash and the updated original-record post payload. -/
theorem seed_child_digests (u : Inputs) (tau d n v : Nat) (t : PTrie) :
    childDigests (record u (seedNodeView tau d n v t))=
      (match t with
       | .ext _ c _=>rootOwner (n+1) c
       | .branch _ cs _=>kidRootOwners (n+1) cs
       | _=>[]).flatMap (ownerDigests u) := by
  cases t with
  | hash h=>rfl
  | leaf k sl m=>rfl
  | ext k c m=>
    have he:=viewKid_digests u (n+1) c
    cases c <;> simpa [childDigests,record,seedNodeView,node,viewNode,NodeV3.revealed,
      viewKid,isNode,kid,kidDigests] using he
  | branch sl cs m=>
    simp only [childDigests,record,seedNodeView,node,viewNode,NodeV3.revealed]
    exact (kids_flat u (viewKids (n+1) cs)).trans (viewKids_digests u cs (n+1))

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
