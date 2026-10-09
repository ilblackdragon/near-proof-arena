import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderForest
import ZkFormal.NearV3.Render.Ups.SourceCidBytes

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen UpsRows Assembly

/-- The honest reader's per-byte child IDs are the source node renderer's
actual child-window cells, at the same global source occurrence. -/
theorem native_reader_cid {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value=some run) (hw : root.tree.wf=true)
    (baseI : UpsInst) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      root.tree run (nativeCidBase
        (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) run base)=some Qs)
    (k : Nat) (hk : k<Qs.length) :
    let I:=nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      baseI root.tree run value Qs
    ∀pos,(part I k).pcid.getD pos 0=NodeGen3.cidAt (forestStoreViews ts).nodes (part I k).sN pos := by
  let recordId:=pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩:=nativeInstance_part recordId baseI hr (nativeCidBase recordId run base) he k hk
  obtain ⟨a,ha,ht,hid,hget⟩:=forest_traceUpsert_extended_provider hroot hr (List.mem_of_getElem? hp)
  dsimp only
  intro pos
  rw [hpart]
  change Q.pcid.getD pos 0=NodeGen3.cidAt (forestStoreViews ts).nodes Q.sN pos
  rw [encodeTreePart_pcid henc,(encodeTreePart_positions henc).2.2.2.1]
  simp only [nativeCidBase,hp]
  change (sourceCidBytes (viewNode (recordId p.source) 0 p.source)).getD pos 0=NodeGen3.cidAt (forestStoreViews ts).nodes (recordId p.source) pos
  change recordId p.source=a.nid at hid
  rw [hid]
  rw [sourceCidBytes_valueId a.nid 0 a.vid p.source]
  exact sourceCidBytes_provider hget pos

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
