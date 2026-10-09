import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestMetadata
import ZkFormal.NearV3.Candidates.TrieCountTraffic

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render

def slotDigests (s : NodeS3) : List ZkFormal.Near.Msg :=
  match s.v.value with
  | some (i,l,pre,post,w)=>[digMsg (msgId K_VPRE i) l pre]++
      (if w then [digMsg (msgId K_VPOST i) l post] else [])
  | none=>[]

theorem node_digest_records (ss : List NodeS3) :
    nodeRecvs3 ss B_DIGEST=ss.flatMap (fun s=>childDigests s++slotDigests s) := by
  have hh:=List.map_fst_zip (by simp : ss.length≤(List.range ss.length).length)
  have he:=congrArg (List.flatMap (fun s=>childDigests s++slotDigests s)) hh
  simp only [List.flatMap_map] at he
  exact he

private theorem split_counts (ss : List NodeS3) (msg : List Fp) :
    ((ss.flatMap (fun s=>childDigests s++slotDigests s)).map Msg.toFp).count msg=
      ((ss.flatMap childDigests).map Msg.toFp).count msg+
      ((ss.flatMap slotDigests).map Msg.toFp).count msg := by
  induction ss with
  | nil=>simp
  | cons s ss ih=>
    simp only [List.flatMap_cons,List.map_append,List.count_append] at *
    omega

/-- Actual count-extended node DIGEST receivers split into child-node ownership
and the separately accounted value-slot requests. -/
theorem physical_node_digest_split (ss : List NodeS3) (hn : NodeOk ss)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount SizeCount.nodeTable.interactions (Candidates.TrieCountHeight.node ss pub) t pub B_DIGEST false msg=
      ((ss.flatMap childDigests).map Msg.toFp).count msg+
      ((ss.flatMap slotDigests).map Msg.toFp).count msg := by
  rw [Candidates.TrieCountTraffic.node_non_size _ _ _ _ _ _ (by decide : B_DIGEST≠B_SIZE),
    ((Candidates.TrieHeight.node_complete ss hn t pub).2.1 B_DIGEST msg).2]
  change ((nodeRecvs3 ss B_DIGEST).map Msg.toFp).count msg=_
  rw [node_digest_records]
  exact split_counts ss msg

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
