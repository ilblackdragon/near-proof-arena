import ZkFormal.NearV3.Render.Ups.NativeEncodingFacts

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

@[simp] theorem nativeInstance_nQ (recordId : PTrie→Nat) (baseI : UpsInst) (root : PTrie)
    (run : TreeRun) (v : Bytes) (Qs : List UpsPartI) :
    nQ (nativeInstance recordId baseI root run v Qs)=Qs.length := by
  simp [nQ,nativeInstance,signedInstance,positionedInstance]

/-- Adjacent part counters and source IDs are produced by the actual positional encoder. -/
theorem nativeInstance_chain (recordId : PTrie→Nat) (baseI : UpsInst) {root : PTrie}
    {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run) (base : Nat→UpsPartI)
    {Qs : List UpsPartI} (he : encodeNativeParts recordId root run base=some Qs)
    (k : Nat) (hk : k+1<Qs.length) :
    let I := nativeInstance recordId baseI root run v Qs
    (part I (k+1)).rc+(if (part I k).kind=0 ∨ (part I k).kind=1 then 1 else 0)=(part I k).rc ∧
    (part I (k+1)).cN=(part I k).sN := by
  obtain ⟨p,Q,hp,_,hQ,hpart⟩ := nativeInstance_part recordId baseI hr base he k (by omega)
  obtain ⟨next,R,_,_,hR,hnext⟩ := nativeInstance_part recordId baseI hr base he (k+1) hk
  dsimp only
  rw [hpart,hnext]
  change R.rc+(if Q.kind=0 ∨ Q.kind=1 then 1 else 0)=Q.rc ∧ R.cN=Q.sN
  have qm := encodeTreePart_positions hQ
  have rm := encodeTreePart_positions hR
  constructor
  · rw [qm.2.1,rm.2.1,encodeTreePart_kind hQ]
    have hs := remainingDescents_step run.parts k p hp
    change remainingDescents run.parts (k+1)+(if p.kind.ix=0 ∨ p.kind.ix=1 then 1 else 0)=
      remainingDescents run.parts k
    cases hc : p.kind <;> simpa [hc,descendKind,UKind.ix] using hs
  · rw [rm.2.2.2.2.1,qm.2.2.2.1]
    exact positionedPart_chain recordId _ run k p next hp _ _

/-- The final row part has root source, zero depth, and the correct final counter. -/
theorem nativeInstance_root (recordId : PTrie→Nat) (baseI : UpsInst) {root : PTrie}
    {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run) (base : Nat→UpsPartI)
    {Qs : List UpsPartI} (he : encodeNativeParts recordId root run base=some Qs) :
    let I := nativeInstance recordId baseI root run v Qs
    (part I (nQ I-1)).rc=(if (part I (nQ I-1)).kind=0 ∨ (part I (nQ I-1)).kind=1 then 1 else 0) ∧
    (part I (nQ I-1)).pdep=0 ∧ (part I (nQ I-1)).sN=I.rid := by
  have hlen := encodeNativeParts_length recordId hr base he
  have hpos := trace_parts_positive hr
  obtain ⟨p,Q,hp,_,hQ,hpart⟩ := nativeInstance_part recordId baseI hr base he (Qs.length-1) (by omega)
  dsimp only
  rw [nativeInstance_nQ,hpart]
  change Q.rc=(if Q.kind=0 ∨ Q.kind=1 then 1 else 0) ∧ Q.pdep=0 ∧ Q.sN=recordId root
  have qm := encodeTreePart_positions hQ
  refine ⟨?_,?_,?_⟩
  · rw [qm.2.1,encodeTreePart_kind hQ]
    change remainingDescents run.parts (Qs.length-1)=(if p.kind.ix=0 ∨ p.kind.ix=1 then 1 else 0)
    rw [hlen] at hp ⊢
    have hs := remainingDescents_root run.parts p hp
    cases hc : p.kind <;> simpa [hc,descendKind,UKind.ix] using hs
  · rw [qm.1]
    change planDepth (fdepth root [0,15]-1) (termPlan run.terminal run.matched).length (Qs.length-1)=0
    rw [hlen,traceUpsert_nQ hr]
    exact planDepth_root _ _ (termPlan_positive _ _)
  · rw [qm.2.2.2.1]
    change recordId p.source=recordId root
    have hs := traceUpsert_rootSource hr
    rw [List.getLast?_eq_getElem?,←hlen,hp] at hs
    simp only [Option.map_some,Option.some.injEq] at hs
    rw [hs]
end ZkFormal.NearV3.Render.UpsGen
