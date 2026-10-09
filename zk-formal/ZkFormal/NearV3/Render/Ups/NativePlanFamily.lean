import ZkFormal.NearV3.Render.Ups.NativeByteFamily
import ZkFormal.NearV3.Render.Ups.NativeWindowCount

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Every part's complete plan metadata follows from actual execution and its
constructed byte semantics, with no per-part proof supplied by the caller. -/
theorem nativeInstance_plan (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hw : root.wf=true) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs) (k : Nat) (hk : k<Qs.length) :
    PartOk (nativeInstance recordId baseI root run v Qs) k
      (part (nativeInstance recordId baseI root run v Qs) k) := by
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr base he k hk
  obtain ⟨data⟩ := encodedNativePart_byteInput recordId baseI hr hw Qs k p hp (base k) henc
  have hplan := encoded_nativePart_ok recordId baseI hr Qs k p hp (base k) Q henc data
  rw [hpart]
  exact hplan.signedInstance

/-- The split-window count in the final signed instance is constructed as well. -/
theorem nativeInstance_splitWindows (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hw : root.wf=true) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs) (k : Nat) (hk : k<Qs.length) :
    let I := nativeInstance recordId baseI root run v Qs
    let Q := part I k
    Q.kind=10 → nWin Q.shape=if I.ci=6 ∨ I.ci=9 ∨ I.ci=10 then 2 else 1 := by
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr base he k hk
  obtain ⟨data⟩ := encodedNativePart_byteInput recordId baseI hr hw Qs k p hp (base k) henc
  have ht := trace_encoded_typeFacts hr (List.mem_of_getElem? hp) henc
  dsimp only
  intro hkind
  rw [hpart] at hkind ⊢
  exact data.split_windows ht hkind
end ZkFormal.NearV3.Render.UpsGen
