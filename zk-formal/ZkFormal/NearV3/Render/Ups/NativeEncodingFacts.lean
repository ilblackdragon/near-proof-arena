import ZkFormal.NearV3.Render.Ups.TreeTerminalEnd

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

theorem encodeTreePart_positions {base Q : UpsPartI} {p : TreePart}
    (he : encodeTreePart base p=some Q) :
    Q.pdep=base.pdep ∧ Q.rc=base.rc ∧ Q.sd=base.sd ∧ Q.sN=base.sN ∧ Q.cN=base.cN ∧ Q.jm=base.jm := by
  unfold encodeTreePart at he
  cases hs : treeNode p.source <;> cases hd : treeNode p.output <;> simp [hs,hd] at he
  subst Q; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem encodeNativeParts_length (recordId : PTrie→Nat) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs) : Qs.length=run.parts.length := by
  obtain ⟨Rs,henc,_,hlen⟩ := encodeNativeParts_total recordId hr base
  rw [he] at henc
  cases henc
  exact hlen

def nativeInstance (recordId : PTrie→Nat) (baseI : UpsInst) (root : PTrie) (run : TreeRun)
    (v : Bytes) (Qs : List UpsPartI) : UpsInst :=
  signedInstance (positionedInstance recordId baseI root run v Qs)

/-- Every live signed row part comes from its actual runtime part and positional base. -/
theorem nativeInstance_part (recordId : PTrie→Nat) (baseI : UpsInst) {root : PTrie}
    {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run) (base : Nat→UpsPartI)
    {Qs : List UpsPartI} (he : encodeNativeParts recordId root run base=some Qs)
    (k : Nat) (hk : k<Qs.length) : ∃ p Q,
      run.parts[k]?=some p ∧ Qs[k]?=some Q ∧
      encodeTreePart (positionedPart recordId (fdepth root [0,15]-1) run k p (base k)) p=some Q ∧
      part (nativeInstance recordId baseI root run v Qs) k=
        withMemorySign (positionedInstance recordId baseI root run v Qs) Q := by
  have hlen := encodeNativeParts_length recordId hr base he
  have hparts : k<run.parts.length := by omega
  let p := run.parts[k]'hparts
  have hp : run.parts[k]?=some p := List.getElem?_eq_getElem hparts
  obtain ⟨Q,hQ,henc⟩ := encodeTreeParts_at (nativePartBase recordId root run base) run.parts 0 Qs k p he hp
  refine ⟨p,Q,hp,hQ,?_,?_⟩
  · simpa [nativePartBase,hp] using henc
  · simp [nativeInstance,signedInstance,positionedInstance,part,List.getD_eq_getElem?_getD,
      List.getElem?_map,hQ]

theorem termPlan_positive (cs : UCase) (matched : Nat) : 0<(termPlan cs matched).length := by
  cases cs <;> simp [termPlan] <;> omega

theorem trace_parts_positive {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) : 0<run.parts.length := by
  have hs := traceUpsert_rootSource hr
  cases h : run.parts with
  | nil => simp [h] at hs
  | cons p ps => simp

/-- All four bit-valued fields follow from the serializer and honest subtraction sign. -/
theorem encoded_signed_bits {I : UpsInst} {base Q : UpsPartI} {p : TreePart}
    (he : encodeTreePart base p=some Q) (data : ByteInput I Q) :
    (withMemorySign I Q).qodd≤1 ∧ (withMemorySign I Q).nochild≤1 ∧
    (withMemorySign I Q).neg≤1 ∧ (withMemorySign I Q).podd≤1 := by
  obtain ⟨_,hqo,_,hpo⟩ := encodeTreePart_prefix he
  refine ⟨?_,?_,withMemorySign_bit I Q,?_⟩
  · change Q.qodd≤1; rw [hqo]; exact nativeOdd_bit p.output
  · change Q.nochild≤1; rw [data.nochild]; split <;> omega
  · change Q.podd≤1; rw [hpo]; exact nativeOdd_bit p.source
end ZkFormal.NearV3.Render.UpsGen
