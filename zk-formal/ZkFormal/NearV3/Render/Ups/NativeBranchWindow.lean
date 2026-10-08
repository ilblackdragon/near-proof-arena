import ZkFormal.NearV3.Render.Ups.NativeBranchGeometry
import ZkFormal.NearV3.Render.Ups.NativeBranchSourceWindow
import ZkFormal.NearV3.Render.Ups.BranchBoundaryCount
import ZkFormal.NearV3.Render.Ups.ForestExtensionWindows
import ZkFormal.NearV3.Render.Ups.NativeChildId
import ZkFormal.NearV3.Render.Ups.TreeProperSources
import ZkFormal.NearV3.Render.Ups.BranchSideAllocation

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near ZkFormal.Near.Render Assembly

/-- Actual RDB parts read their allocated path child's ID at the selected CH
window. All branch geometry and source-byte facts come from native execution. -/
theorem native_branch_window {root : PTrie} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] value=some run) (hw : root.wf=true)
    (n vid d k : Nat) (base : Nat→UpsPartI) (I : UpsInst)
    {p : TreePart} (hp : run.parts[k+1]?=some p) (hk : p.kind=.RDB) {Q : UpsPartI}
    (he : encodeTreePart
      (positionedPart (pathRecordId (extendedAddresses n vid d root [0,15]))
        (fdepth root [0,15]-1) run (k+1) p
        (nativeCidBase (pathRecordId (extendedAddresses n vid d root [0,15])) run base (k+1))) p=some Q) :
    WindowOk I Q := by
  let recordId := pathRecordId (extendedAddresses n vid d root [0,15])
  let B := positionedPart recordId (fdepth root [0,15]-1) run (k+1) p
    (nativeCidBase recordId run base (k+1))
  have hmem := List.mem_of_getElem? hp
  obtain ⟨sv,kids,mem,outKids,outMem,hsrc,hout,hlen,hocc,hwout⟩ :=
    traceUpsert_branch_geometry hr hw hmem hk (recordId p.source+1)
  have hsides := positionedPart_branchSide recordId (fdepth root [0,15]-1) hr (k+1) p hp hk
    (nativeCidBase recordId run base (k+1))
  change (B.sd=0 ∨ B.sd=1) ∧ p.slot=edgeSlot B.sd at hsides
  obtain ⟨child,hpath,hcn⟩ := positionedPart_nativeChild recordId (fdepth root [0,15]-1)
    hr k p hp (Or.inl hk) (nativeCidBase recordId run base (k+1))
  have hc : nativeChildAt kids p.slot=some child := by
    simpa only [sourcePathChild,hsrc] using hpath
  have hn : isNode child=true := by
    have hproper := traceUpsert_properSources root [0,15] value run hr p hmem
    simp only [ProperSource,hk] at hproper
    obtain ⟨sv',kids',mem',c,cm,hs,hchild,hcm⟩ := hproper
    rw [hsrc] at hs
    cases hs
    rw [hc] at hchild
    cases hchild
    cases child <;> simp_all [PTrie.mem?,isNode]
  have hselected := viewKids_selected (recordId p.source+1) kids p.slot child hc
  have hvlen : (viewKids (recordId p.source+1) kids).length=16 := by
    have h := congrArg List.length (viewKids_occupancy (recordId p.source+1) kids)
    simpa only [kidOccupancy,List.length_map,hlen] using h
  have hprefix := boundary_cid_prefix (viewKids (recordId p.source+1) kids) B.sd hvlen hsides.1
    (viewKid (seedChildId (recordId p.source+1) kids p.slot) child)
    (hsides.2 ▸ hselected) (by simp [viewKid,hn])
  have henc : encodeTreePart B p=some Q := he
  simp [encodeTreePart,hsrc,hout,treeNode] at henc
  subst Q
  let E := encodePart {B with kind:=p.kind.ix}
    (.branch (sv.map treeSlot) (treeKids kids) ((u64 mem).map UInt8.toNat))
    (.branch (sv.map treeSlot) (treeKids outKids) ((u64 outMem).map UInt8.toNat))
  change WindowOk I E
  have hfields : FieldsOk E := encodePart_fields _ _ _ hwout
  have hkind : E.kind=0 := by change p.kind.ix=0; simp [hk,UKind.ix]
  have hhead : fieldsLen (nodeHeader E.ty E.qhk)=(if sv.isSome then 39 else 3) := by
    cases sv <;> rfl
  have hcount : nWin E.shape=((viewKids (recordId p.source+1) kids).filter (fun k=>k≠.none)).length := by
    change nWin (nonemptyFields (nodeRawShape (.branch (sv.map treeSlot) (treeKids outKids)
      ((u64 outMem).map UInt8.toNat))))=_
    rw [nonempty_node_shape,nodeFields_windows]
    change (NodeGen3.branchWins (treeKids outKids)).length=_
    rw [windows_eq_of_occupancy hocc,branchWins_count]
  constructor
  · intro hbad; omega
  · intro pos _ hs hi ht _
    have hpos := hfields.target_start I hs hi ht
    have h15 : S15B I E=(B.sd==1) := by simp [S15B,E,encodePart,hk,UKind.ix]
    rw [hhead,h15,hcount,←hprefix,←hsides.2] at hpos
    have hread : (sposV I E 7 0 (fieldAt E.shape pos).2.2.2 pos).toNat=pos := by
      simp [sposV,hkind]
    change E.pcid.getD (sposV I E 7 0 (fieldAt E.shape pos).2.2.2 pos).toNat 0=E.cN
    rw [hread,hpos]
    change (nativeCidBase recordId run base (k+1)).pcid.getD _ 0=B.cN
    rw [hcn]
    simpa only [Nat.add_zero] using native_branch_source_window hr n vid d (k+1) base hp hk hsrc hc hn 0 (by decide)

/-- The final signed instance inherits the native branch window proof. -/
theorem nativeInstance_branch_window {root : PTrie} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] value=some run) (hw : root.wf=true)
    (n vid d : Nat) (baseI : UpsInst) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts (pathRecordId (extendedAddresses n vid d root [0,15])) root run
      (nativeCidBase (pathRecordId (extendedAddresses n vid d root [0,15])) run base)=some Qs)
    (k : Nat) (hbound : k+1<Qs.length)
    (hkind : (part (nativeInstance (pathRecordId (extendedAddresses n vid d root [0,15]))
      baseI root run value Qs) (k+1)).kind=0) :
    let I := nativeInstance (pathRecordId (extendedAddresses n vid d root [0,15])) baseI root run value Qs
    WindowOk I (part I (k+1)) := by
  let recordId := pathRecordId (extendedAddresses n vid d root [0,15])
  let I := nativeInstance recordId baseI root run value Qs
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr
    (nativeCidBase recordId run base) he (k+1) hbound
  change WindowOk I (part (nativeInstance recordId baseI root run value Qs) (k+1))
  rw [hpart] at hkind ⊢
  have hk : p.kind=.RDB := by
    change Q.kind=0 at hkind
    rw [encodeTreePart_kind henc] at hkind
    cases hp : p.kind <;> simp_all [UKind.ix]
  apply WindowOk.withSign
  exact native_branch_window hr hw n vid d k base I hp hk henc
end ZkFormal.NearV3.Render.UpsGen
