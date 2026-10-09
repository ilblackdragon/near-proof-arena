import ZkFormal.NearV3.Rcpt.Candidates.NativePartSourcePosition
import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderSourceId
import ZkFormal.NearV3.Assembly.ExtendedRecordId

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen UpsRows Assembly

private theorem root_depth : ∀n v ts tau root,
    forestRootAt n v ts tau=some root→root.depth=0
  | _,_,[],_,_,h => by simp [forestRootAt] at h
  | _,_,_::_,0,_,h => by cases h;rfl
  | n,v,t::ts,tau+1,root,h => root_depth (n+tsize t) (v+(valsOf t).length) ts tau root h

/-- Every generated source-reading part uses the depth of its actual indexed
forest provider. NLF allocates a new leaf and has no source-window reads. -/
theorem native_reader_depth {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value=some run)
    (baseI : UpsInst) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      root.tree run base=some Qs) (k : Nat) (hk : k<Qs.length)
    (hkind : (part (nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      baseI root.tree run value Qs) k).kind≠8) :
    let I:=nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      baseI root.tree run value Qs
    ∃s,(forestStoreViews ts).nodes[(part I k).sN]?=some s ∧ (part I k).pdep=s.depth := by
  let recordId:=pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩:=nativeInstance_part recordId baseI hr base he k hk
  have hnot : p.kind≠.NLF := by
    intro hn
    rw [hpart] at hkind
    change Q.kind≠8 at hkind
    exact hkind ((encodeTreePart_kind henc).trans (by rw [hn];rfl))
  obtain ⟨a,ha,ht⟩:=native_part_source_position root.tree [0,15] value run hr root.nid root.vid root.depth k p hp hnot
  have ham:=List.mem_of_getElem? ha
  have hd:=source_address_depth root.nid root.vid root.depth root.tree [0,15] _ a ha
  rw [root_depth 0 0 ts tau root hroot,Nat.zero_add,sourcePosition_plan hr] at hd
  have hid : recordId p.source=a.nid := ht ▸ extendedRecordId_source ham
  have hs:=forestRootAt_view (ns:=forestNodes 0 0 0 ts) 0 0 0 ts tau root (by simp) hroot
  have hv:=sourceAddresses_view _ _ _ _ _ hs a ham
  have hn : isNode a.tree=true := ht ▸ (traceUpsert_nodeParts _ _ _ _ hr p (List.mem_of_getElem? hp)).1
  have hget : (forestStoreViews ts).nodes[a.nid]?=some (seedNodeView tau a.depth a.nid a.vid p.source) := by
    simpa only [forestStoreViews,Nat.zero_add,ht] using hv.get hn
  dsimp only
  rw [hpart]
  change ∃s,(forestStoreViews ts).nodes[Q.sN]?=some s ∧ Q.pdep=s.depth
  have hsid : Q.sN=a.nid := (encodeTreePart_positions henc).2.2.2.1.trans hid
  refine ⟨_,hsid.symm ▸ hget,?_⟩
  change Q.pdep=a.depth
  rw [(encodeTreePart_positions henc).1]
  exact hd.symm

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
