import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderDepth
import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderCid
import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedInitializedBytes

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen UpsRows Assembly

/-- All copied-byte, depth and child-ID fields of a generated source reader
belong to one initialized original record with its actual receipt-updated bytes. -/
theorem native_reader_window (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid)
    (hw : ∀r∈rs,r.pre.wf=true) (hbudget : preBytes (rs.map ReplayTree.post)≤2000000)
    {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 (rs.map ReplayTree.post) tau=some root)
    {value : Bytes} {run : TreeRun} (hr : traceUpsert root.tree [0,15] value=some run)
    (baseI : UpsInst) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      root.tree run (nativeCidBase
        (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) run base)=some Qs)
    (k : Nat) (hk : k<Qs.length)
    (hkind : (part (nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      baseI root.tree run value Qs) k).kind≠8) :
    let I:=nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      baseI root.tree run value Qs
    ∃s,(records (forestOldInputs rs) (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre))))[(part I k).sN]?=some s ∧
      (part I k).pb=s.v.ser true ∧ (part I k).pdep=s.depth ∧
      ∀pos,(part I k).pcid.getD pos 0=s.ucid.getD pos 0 := by
  have hpost : ∀t∈rs.map ReplayTree.post,t.wf=true := by
    intro t ht
    obtain ⟨r,hr,rfl⟩:=List.mem_map.mp ht
    exact SizedAccountRun.wf (hv r hr) (hw r hr)
  have ht:=forestRootAt_tree 0 0 (rs.map ReplayTree.post) tau
  rw [hroot,Option.map_some] at ht
  have htm:=List.mem_of_getElem? ht.symm
  have hrw:=hpost root.tree htm
  obtain ⟨p,addr,hp,ha,htree,hid,hget,hbytes⟩:=native_reader_forest hroot hr hrw baseI _ he k hk
  have hpwf : (seedNodeView tau addr.depth addr.nid addr.vid p.source).v.wf := by
    apply native_forest_node_wf _ hpost hbudget
    exact List.mem_flatMap.mpr ⟨root.tree,htm,traceUpsert_source_occurrence hr (List.mem_of_getElem? hp)⟩
  obtain ⟨s,hs,hser,hdepth,hcid⟩:=replay_initialized_fields rs hv hw hget hpwf
  obtain ⟨b,hb,hd⟩:=native_reader_depth hroot hr baseI _ he k hk hkind
  have heq:=Option.some.inj (hget.symm.trans hb)
  subst b
  refine ⟨s,hs,?_,hd.trans hdepth.symm,?_⟩
  · rw [hbytes,hser]
    symm
    exact viewNode_ser addr.nid addr.vid p.source
      ((traceUpsert_sources root.tree [0,15] value run hrw hr).2 p (List.mem_of_getElem? hp))
      (traceUpsert_nodeParts root.tree [0,15] value run hr p (List.mem_of_getElem? hp)).1 false
  · intro pos
    exact (native_reader_cid hroot hr hrw baseI base he k hk pos).trans (hcid pos).symm

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
