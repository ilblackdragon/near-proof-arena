import ZkFormal.NearV3.Render.Ups.NativeUpperWindows
import ZkFormal.NearV3.Render.Ups.NativePlanFamily

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows Assembly

/-- Every final native update part satisfies the full window input. Split counts
come from native byte/bitmap semantics; upper child reads come from actual occurrence IDs. -/
theorem nativeInstance_windows {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value=some run) (hw : root.tree.wf=true)
    (baseI : UpsInst) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) root.tree run
      (nativeCidBase (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) run base)=some Qs)
    (k : Nat) (hbound : k<Qs.length) :
    let I := nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) baseI root.tree run value Qs
    WindowOk I (part I k) := by
  let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
  let I := nativeInstance recordId baseI root.tree run value Qs
  change WindowOk I (part I k)
  constructor
  · exact nativeInstance_splitWindows recordId baseI hr hw (nativeCidBase recordId run base) he k hbound
  · intro pos hpos hs hi ht hu
    exact (nativeInstance_upper_window hroot hr hw baseI base he k hbound hu).childId pos hpos hs hi ht hu
end ZkFormal.NearV3.Render.UpsGen
