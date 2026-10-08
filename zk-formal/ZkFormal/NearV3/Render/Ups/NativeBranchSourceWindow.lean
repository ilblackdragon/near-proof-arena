import ZkFormal.NearV3.Render.Ups.NativeBranchChildIds
import ZkFormal.NearV3.Render.Ups.BranchCidWindows
import ZkFormal.NearV3.Render.Ups.SourceCidBytes

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near Assembly

/-- The constructed pcid reads the selected immediate occurrence, not a hash or
an arbitrary equal sibling, at its ordinary serialized branch window. -/
theorem native_branch_source_window {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) (n vid d k : Nat) (base : Nat→UpsPartI)
    {p : TreePart} (hp : run.parts[k]?=some p) (hkind : p.kind=.RDB)
    {sv kids mem child} (hsrc : p.source=.branch sv kids mem)
    (hc : nativeChildAt kids p.slot=some child) (hn : isNode child=true)
    (i : Nat) (hi : i<32) :
    let recordId := pathRecordId (extendedAddresses n vid d t key)
    let sourceN := recordId p.source
    (nativeCidBase recordId run base k).pcid.getD
      ((if sv.isSome then 39 else 3)+
        (branchCidBytes ((viewKids (sourceN+1) kids).take p.slot)).length+i) 0=recordId child := by
  let recordId := pathRecordId (extendedAddresses n vid d t key)
  obtain ⟨ctx,hctx,htree,hid,hchild⟩ :=
    traceUpsert_branch_childId hr n vid d (List.mem_of_getElem? hp) hkind hsrc
  change (nativeCidBase recordId run base k).pcid.getD _ 0=recordId child
  simp only [nativeCidBase,hp]
  rw [show recordId p.source=ctx.address.nid from hid,hsrc,
    show recordId child=seedChildId (ctx.address.nid+1) kids p.slot from hchild child hc]
  have hselected := viewKids_selected (ctx.address.nid+1) kids p.slot child hc
  simp only [viewKid,hn,ite_true] at hselected
  have hread := sourceCidBytes_branch_at (sv.map (viewSlot 0))
    (viewKids (ctx.address.nid+1) kids) ((u64 mem).map UInt8.toNat) p.slot
    (seedChildId (ctx.address.nid+1) kids p.slot) (nodeEnc child).length
    (viewTarget (seedChildId (ctx.address.nid+1) kids p.slot) child)
    (child.hashOf.map UInt8.toNat) (child.hashOf.map UInt8.toNat) hselected i hi
  have hid' : pathRecordId (extendedAddresses n vid d t key) (.branch sv kids mem)=ctx.address.nid := by
    simpa only [hsrc] using hid
  rw [hid']
  simpa only [viewNode,Option.isSome_map] using hread
end ZkFormal.NearV3.Render.UpsGen
