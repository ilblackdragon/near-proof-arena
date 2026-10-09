import ZkFormal.NearV3.Render.Ups.NativeUpperIndex
import ZkFormal.NearV3.Render.Ups.NativeBranchWindow

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows Assembly

/-- Every final upper-path part satisfies WindowOk, including exclusion of the
impossible first-part case. No source-window or child-ID premise remains. -/
theorem nativeInstance_upper_window {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value=some run) (hw : root.tree.wf=true)
    (baseI : UpsInst) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) root.tree run
      (nativeCidBase (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) run base)=some Qs)
    (k : Nat) (hbound : k<Qs.length)
    (hupper : let I := nativeInstance (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) baseI root.tree run value Qs;
      (part I k).kind=0 ∨ (part I k).kind=1 ∨ (part I k).kind=11) :
    let I := nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) baseI root.tree run value Qs
    WindowOk I (part I k) := by
  let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
  have hpos : 0<k := by
    obtain ⟨p,Q,hp,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr
      (nativeCidBase recordId run base) he k hbound
    have hu := hupper
    change (part (nativeInstance recordId baseI root.tree run value Qs) k).kind=0 ∨
      (part (nativeInstance recordId baseI root.tree run value Qs) k).kind=1 ∨
      (part (nativeInstance recordId baseI root.tree run value Qs) k).kind=11 at hu
    rw [hpart] at hu
    change Q.kind=0 ∨ Q.kind=1 ∨ Q.kind=11 at hu
    rw [encodeTreePart_kind henc] at hu
    apply traceUpsert_upper_index hr hp
    cases hk : p.kind <;> simp_all [UKind.ix,upperKind]
  cases k with
  | zero => omega
  | succ j =>
    rcases hupper with hb|hext
    · exact nativeInstance_branch_window hr hw root.nid root.vid root.depth baseI base he j hbound hb
    · exact nativeInstance_extension_window hroot hr baseI base he j hbound hext
end ZkFormal.NearV3.Render.UpsGen
