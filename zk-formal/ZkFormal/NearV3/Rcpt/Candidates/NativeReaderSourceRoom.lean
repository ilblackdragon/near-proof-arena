import ZkFormal.NearV3.Rcpt.Candidates.UpsWindowSourceRoom
import ZkFormal.NearV3.Render.Ups.NativePrefixBounds

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render Render.UpsGen UpsRows

/-- Source prefix overhead comes from the actual encoded source node. -/
theorem encoded_source_room {base Q : UpsPartI} {p : TreePart}
    (he : encodeTreePart base p=some Q) (hw : p.source.wf=true) :
    Q.phk+9≤Q.pb.length := by
  unfold encodeTreePart at he
  cases hs : treeNode p.source <;> cases hd : treeNode p.output <;> simp [hs,hd] at he
  rename_i src dst
  subst Q
  exact node_source_room src (treeNode_wf hw hs) true

theorem native_reader_source_room (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {value : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] value=some run)
    (hw : root.wf=true) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs) (k : Nat) (hk : k<Qs.length) :
    let Q:=part (nativeInstance recordId baseI root run value Qs) k
    Q.phk+9≤Q.pb.length := by
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩:=nativeInstance_part recordId baseI hr base he k hk
  have hsource:=(traceUpsert_sources root [0,15] value run hw hr).2 p (List.mem_of_getElem? hp)
  dsimp only
  rw [hpart]
  change Q.phk+9≤Q.pb.length
  exact encoded_source_room henc hsource

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
