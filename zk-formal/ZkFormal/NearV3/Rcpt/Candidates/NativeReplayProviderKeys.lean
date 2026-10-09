import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayProviderForest
import ZkFormal.NearV3.Rcpt.Candidates.NodePostProviders

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render Render.UpsGen Assembly

theorem edges_eq_of_provider {a b : NodeS3} (n : Nat)
    (h : providerNode a.v=providerNode b.v) : edgesOf3 n a=edgesOf3 n b := by
  rw [←providerNode_edges a n,←providerNode_edges b n]
  unfold edgesOf3
  simp only [h]

theorem bitmap_eq_of_provider {a b : NodeS3}
    (h : providerNode a.v=providerNode b.v) : a.v.bmap=b.v.bmap := by
  rw [←providerNode_bmap a.v,←providerNode_bmap b.v,h]

private theorem zipped_keys_equal {as bs : List NodeS3}
    (h : as.map (fun s=>providerNode s.v)=bs.map (fun s=>providerNode s.v)) (ns : List Nat) :
    (as.zip ns).flatMap (fun (s,n)=>edgesOf3 n s)=(bs.zip ns).flatMap (fun (s,n)=>edgesOf3 n s) ∧
    (as.zip ns).filterMap (fun (s,n)=>s.v.bmap.map (fun (bm,hv)=>[n,bm,hv]))=
      (bs.zip ns).filterMap (fun (s,n)=>s.v.bmap.map (fun (bm,hv)=>[n,bm,hv])) := by
  induction as generalizing bs ns with
  | nil=>cases bs <;> simp_all
  | cons a as ih=>
    cases bs with
    | nil=>simp at h
    | cons b bs=>
      have hh:=List.cons.inj h
      cases ns with
      | nil=>simp
      | cons n ns=>
        obtain ⟨he,hb⟩:=ih hh.2 ns
        simp only [List.zip_cons_cons,List.flatMap_cons,List.filterMap_cons]
        rw [edges_eq_of_provider n hh.1,bitmap_eq_of_provider hh.1,he,hb]
        exact ⟨rfl,rfl⟩

theorem provider_keys_equal {as bs : List NodeS3}
    (h : as.map (fun s=>providerNode s.v)=bs.map (fun s=>providerNode s.v)) :
    nodeEdgeKeys as=nodeEdgeKeys bs ∧ nodeBitmapKeys as=nodeBitmapKeys bs := by
  have hl : as.length=bs.length := by simpa using congrArg List.length h
  simpa only [nodeEdgeKeys,nodeBitmapKeys,hl] using zipped_keys_equal h (List.range bs.length)

theorem replay_provider_keys (rs : List ReplayTree) (tau n v : Nat)
    (h : ∀r∈rs,r.Valid) :
    nodeEdgeKeys (forestNodes tau n v (rs.map ReplayTree.pre))=
      nodeEdgeKeys (forestNodes tau n v (rs.map ReplayTree.post)) ∧
    nodeBitmapKeys (forestNodes tau n v (rs.map ReplayTree.pre))=
      nodeBitmapKeys (forestNodes tau n v (rs.map ReplayTree.post)) :=
  provider_keys_equal (replay_provider_nodes rs tau n v h)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
