import ZkFormal.NearV3.Render.Ups.TreeExtensionWindows
import ZkFormal.NearV3.Render.Ups.ExtensionWindowInput
import ZkFormal.NearV3.Render.Ups.NativeChildId

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near Assembly

/-- Actual native extension parts satisfy the child-window constraints. Source and
child IDs come from the concrete occurrence map, and pcid is constructed from its layout. -/
theorem forest_extension_window {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value=some run) (base : Nat→UpsPartI)
    (I : UpsInst) (k : Nat) (part : TreePart) (hp : run.parts[k+1]?=some part)
    (hk : part.kind=.RDE ∨ part.kind=.PT) {Q : UpsPartI}
    (he : encodeTreePart
      (nativePartBase (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
        root.tree run
        (nativeCidBase (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
          run base) (k+1)) part=some Q) : WindowOk I Q := by
  let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
  let B := nativeCidBase recordId run base
  have hm := List.mem_of_getElem? hp
  obtain ⟨key,child,oldMem,newChild,newMem,hsrc,hout,hn⟩ :=
    traceUpsert_extWindowShapes root.tree [0,15] value run hr part hm hk
  obtain ⟨a,ha,htree,hid,_⟩ := forest_traceUpsert_extended_provider hroot hr hm
  have hchildId : recordId child=a.nid+1 := by
    have hc := sourceExtension_child_extended _ _ _ _ _ a ha key child oldMem (htree.trans hsrc)
    exact extendedAddresses_ids _ _ _ _ _ hc
  have hupper : upperKind part.kind := by rcases hk with hk|hk; exact Or.inr (Or.inl hk); exact Or.inr (Or.inr hk)
  obtain ⟨c,hc,hcn⟩ := positionedPart_nativeChild recordId (fdepth root.tree [0,15]-1) hr k part hp hupper (B (k+1))
  have hce : c=child := by simpa only [sourcePathChild,hsrc,Option.some.injEq] using hc.symm
  subst c
  have hbaseId : (positionedPart recordId (fdepth root.tree [0,15]-1) run (k+1) part (B (k+1))).cN=a.nid+1 :=
    hcn.trans hchildId
  have hbaseCid : (positionedPart recordId (fdepth root.tree [0,15]-1) run (k+1) part (B (k+1))).pcid=
      sourceCidBytes (viewNode a.nid 0 (.ext key child oldMem)) := by
    change (B (k+1)).pcid=_
    simp only [B,nativeCidBase,hp]
    rw [show recordId part.source=a.nid from hid,hsrc]
  have henc : encodeTreePart
      (positionedPart recordId (fdepth root.tree [0,15]-1) run (k+1) part (B (k+1))) part=some Q := by
    simpa only [nativePartBase,hp] using he
  simp [encodeTreePart,hsrc,hout,treeNode] at henc
  subst Q
  apply extension_window_ok I _ a.nid key child oldMem (treeKid newChild) ((u64 newMem).map UInt8.toNat)
  · change part.kind.ix=1 ∨ part.kind.ix=11
    rcases hk with hk|hk <;> simp [hk,UKind.ix]
  · exact hn
  · exact hbaseId
  · exact hbaseCid


theorem WindowOk.withSign {I : UpsInst} {Q : UpsPartI} (h : WindowOk I Q) (J : UpsInst) :
    WindowOk I (withMemorySign J Q) := by
  exact ⟨h.splitCount,h.childId⟩

/-- Final signed native extension parts inherit the constructed source-window proof. -/
theorem nativeInstance_extension_window {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value=some run) (baseI : UpsInst) (base : Nat→UpsPartI)
    {Qs : List UpsPartI}
    (he : encodeNativeParts
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) root.tree run
      (nativeCidBase (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) run base)=some Qs)
    (k : Nat) (hbound : k+1<Qs.length)
    (hkind : (part (nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) baseI root.tree run value Qs)
        (k+1)).kind=1 ∨
      (part (nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) baseI root.tree run value Qs)
        (k+1)).kind=11) :
    let I := nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) baseI root.tree run value Qs
    WindowOk I (part I (k+1)) := by
  let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
  let B := nativeCidBase recordId run base
  let I := nativeInstance recordId baseI root.tree run value Qs
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr B he (k+1) hbound
  change WindowOk I (part (nativeInstance recordId baseI root.tree run value Qs) (k+1))
  rw [hpart] at hkind ⊢
  have hk : p.kind=.RDE ∨ p.kind=.PT := by
    change Q.kind=1 ∨ Q.kind=11 at hkind
    rw [encodeTreePart_kind henc] at hkind
    cases hp : p.kind <;> simp_all [UKind.ix]
  apply WindowOk.withSign
  apply forest_extension_window hroot hr base I k p hp hk
  simpa only [nativePartBase,hp] using henc
end ZkFormal.NearV3.Render.UpsGen
