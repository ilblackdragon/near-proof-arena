import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderSourceId
import ZkFormal.NearV3.Assembly.ExtendedRecordId

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen UpsRows Assembly

/-- The part's source column selects an actual global forest record at that
exact index. Equal serialized subtrees cannot replace this indexed binding. -/
theorem native_reader_forest {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value=some run) (hw : root.tree.wf=true)
    (baseI : UpsInst) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      root.tree run base=some Qs) (k : Nat) (hk : k<Qs.length) :
    let I:=nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      baseI root.tree run value Qs
    ∃p a,run.parts[k]?=some p ∧
      a∈sourceAddresses root.nid root.vid root.depth root.tree [0,15] ∧
      a.tree=p.source ∧ (part I k).sN=a.nid ∧
      (forestStoreViews ts).nodes[(part I k).sN]?=some (seedNodeView tau a.depth a.nid a.vid p.source) ∧
      (part I k).pb=(nodeEnc p.source).map UInt8.toNat := by
  obtain ⟨p,hp,_,hid,hb⟩:=native_reader_source_id _ baseI hr hw base he k hk
  obtain ⟨a,ha,ht,hid',hget⟩:=forest_traceUpsert_extended_provider hroot hr (List.mem_of_getElem? hp)
  have hi:=hid.trans hid'
  exact ⟨p,a,hp,ha,ht,hi,hi.symm ▸ hget,hb⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
