import ZkFormal.NearV3.Render.Ups.TreeByteAssembly
import ZkFormal.NearV3.Render.Ups.NativeInstanceOk

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Every actual allocated native part has ordinary byte semantics; the branch-side
input to local constructors is discharged by the checked traversal coordinate. -/
theorem encodedNativePart_byteInput (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hw : root.wf=true) (Qs : List UpsPartI) (k : Nat) (p : TreePart)
    (hp : run.parts[k]?=some p) (base : UpsPartI) {Q : UpsPartI}
    (he : encodeTreePart (positionedPart recordId (fdepth root [0,15]-1) run k p base) p=some Q) :
    Nonempty (ByteInput (positionedInstance recordId baseI root run v Qs) Q) := by
  apply traceUpsert_byteInputs root [0,15] v run hr hw (Or.inr (Or.inr rfl))
    (positionedInstance recordId baseI root run v Qs) p (List.mem_of_getElem? hp) _ Q he
  intro hkind
  exact positionedPart_branchSide recordId _ hr k p hp hkind base

/-- The complete signed native instance supplies its own byte-input family directly
from actual execution and source well-formedness. No byte or AIR equality is assumed. -/
theorem nativeInstance_byteInputs (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hw : root.wf=true) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs) (k : Nat) (hk : k<Qs.length) :
    Nonempty (ByteInput (nativeInstance recordId baseI root run v Qs)
      (part (nativeInstance recordId baseI root run v Qs) k)) := by
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr base he k hk
  obtain ⟨data⟩ := encodedNativePart_byteInput recordId baseI hr hw Qs k p hp (base k) henc
  rw [hpart]
  exact ⟨data.withMemorySign.withParts _⟩
/-- Membership form of the complete unsigned family, suitable for existing renderer APIs. -/
theorem encodedNativeParts_byteInputs (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hw : root.wf=true) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs) (Q : UpsPartI) (hQ : Q∈Qs) :
    Nonempty (ByteInput (positionedInstance recordId baseI root run v Qs) Q) := by
  obtain ⟨k,hk,hget⟩ := List.mem_iff_getElem.mp hQ
  obtain ⟨p,R,hp,hR,henc,_⟩ := nativeInstance_part recordId baseI hr base he k hk
  have hsame : R=Q := by
    rw [List.getElem?_eq_getElem hk,hget] at hR
    exact (Option.some.inj hR).symm
  subst R
  exact encodedNativePart_byteInput recordId baseI hr hw Qs k p hp (base k) henc

/-- Every instance condition other than the authenticated walk follows directly from
native execution; the former separate byte-family premise is now fully discharged. -/
theorem nativeInstance_semantic_ok (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hw : root.wf=true) (hv : 1≤v.length) (hvsmall : v.length<2^24)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs)
    (walk : WalkOkU (nativeInstance recordId baseI root run v Qs)) :
    InstOk (nativeInstance recordId baseI root run v Qs) :=
  nativeInstance_ok recordId baseI hr hw hv hvsmall base he
    (fun Q hQ => Classical.choice (encodedNativeParts_byteInputs recordId baseI hr hw base he Q hQ)) walk
end ZkFormal.NearV3.Render.UpsGen
