import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderForest
import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedWindowBytes

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen UpsRows Assembly

/-- Every rebased native reader copies the exact post bytes of an original
record at its actual source-column index. The provider's depth is retained. -/
theorem native_reader_old_post (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid)
    (hw : ∀r∈rs,r.pre.wf=true) {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 (rs.map ReplayTree.post) tau=some root)
    {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value=some run) (hrw : root.tree.wf=true)
    (baseI : UpsInst) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      root.tree run base=some Qs) (k : Nat) (hk : k<Qs.length) :
    let I:=nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      baseI root.tree run value Qs
    ∃p addr s,run.parts[k]?=some p ∧
      addr∈sourceAddresses root.nid root.vid root.depth root.tree [0,15] ∧
      addr.tree=p.source ∧ (part I k).sN=addr.nid ∧
      (records (forestOldInputs rs) (forestNodes 0 0 0 (rs.map ReplayTree.pre)))[(part I k).sN]?=some s ∧
      s.depth=addr.depth ∧ (part I k).pb=s.v.ser true := by
  obtain ⟨p,a,hp,ha,ht,hid,hget,hbytes⟩:=native_reader_forest hroot hr hrw baseI base he k hk
  let old:=records (forestOldInputs rs) (forestNodes 0 0 0 (rs.map ReplayTree.pre))
  have hl:=congrArg List.length (replay_window_bytes rs hv hw false)
  simp only [List.length_map] at hl
  have hbound:=(List.getElem?_eq_some_iff.mp hget).1
  have hb : (part (nativeInstance (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) baseI root.tree run value Qs) k).sN<old.length := by
    change _<(records (forestOldInputs rs) (forestNodes 0 0 0 (rs.map ReplayTree.pre))).length
    rw [hl]
    exact hbound
  let s:=old[(part (nativeInstance (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) baseI root.tree run value Qs) k).sN]'hb
  have hs : old[(part (nativeInstance (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) baseI root.tree run value Qs) k).sN]?=some s := List.getElem?_eq_getElem hb
  have hd:=replay_window_at rs hv hw hs hget
  refine ⟨p,a,s,hp,ha,ht,hid,hs,hd.2,?_⟩
  rw [hbytes,hd.1]
  symm
  exact viewNode_ser a.nid a.vid p.source
    ((traceUpsert_sources root.tree [0,15] value run hrw hr).2 p (List.mem_of_getElem? hp))
    (traceUpsert_nodeParts root.tree [0,15] value run hr p (List.mem_of_getElem? hp)).1 false

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
