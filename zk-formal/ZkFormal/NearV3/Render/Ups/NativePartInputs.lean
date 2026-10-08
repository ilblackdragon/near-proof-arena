import ZkFormal.NearV3.Render.Ups.NativeWindows
import ZkFormal.NearV3.Render.Ups.NativeChildLengthBinding
import ZkFormal.NearV3.Render.Ups.NativeMemoryFamily

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows Assembly

/-- CID and memory assignments touch separate fields, so the combined executable
constructor is also in the form required by the native memory proof. -/
theorem nativeSourceBase_asMemory (recordId : PTrie→Nat) (run : TreeRun) (base : Nat→UpsPartI) :
    nativeSourceBase recordId run base=
      nativeMemoryBase run (nativeCidBase recordId run (nativeLengthBase run base)) := by
  funext k
  cases h : run.parts[k]? <;> simp [nativeSourceBase,nativeMemoryBase,nativeCidBase,h]

/-- All per-part semantic renderer inputs from the concrete native constructor.
Only the existing numeric memory bounds remain explicit; no byte, window,
child-ID, child-length, plan, or memory equation is supplied by the caller. -/
theorem nativeInstance_partInputs {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value=some run) (hw : root.tree.wf=true)
    (hv : value.length<2^24) (hd : fdepth root.tree [0,15]≤400)
    (baseI : UpsInst) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) root.tree run
      (nativeSourceBase (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) run base)=some Qs)
    (k : Nat) (hbound : k<Qs.length)
    (hq : (part (nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) baseI root.tree run value Qs) k).qhk<2^22)
    (hprefix : (part (nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) baseI root.tree run value Qs) k).phk<2^22) :
    let I := nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) baseI root.tree run value Qs
    Nonempty (ByteInput I (part I k)) ∧ FieldsOk (part I k) ∧ PartOk I k (part I k) ∧ WindowOk I (part I k) ∧
      MemOk I (part I k) ∧ (part I k).jm-1<Qs.length ∧ (part I k).clen=(child I (part I k)).q.length := by
  let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
  have hemem : encodeNativeMemoryParts recordId root.tree run
      (nativeCidBase recordId run (nativeLengthBase run base))=some Qs := by
    unfold encodeNativeMemoryParts
    rw [←nativeSourceBase_asMemory]
    exact he
  obtain ⟨data⟩ := nativeInstance_byteInputs recordId baseI hr hw (nativeSourceBase recordId run base) he k hbound
  refine ⟨⟨data⟩,data.fieldsOk,
    nativeInstance_plan recordId baseI hr hw (nativeSourceBase recordId run base) he k hbound,
    ?_,nativeInstance_memOk recordId baseI hr hw hv hd _ hemem k hbound hq hprefix,?_⟩
  · exact nativeInstance_windows hroot hr hw baseI (nativeMemoryBase run (nativeLengthBase run base)) he k hbound
  · exact nativeInstance_childLength recordId baseI hr base he k hbound
end ZkFormal.NearV3.Render.UpsGen
