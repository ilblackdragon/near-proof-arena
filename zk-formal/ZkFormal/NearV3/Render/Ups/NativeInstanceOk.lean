import ZkFormal.NearV3.Render.Ups.NativeInstanceBoundary

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- All non-walk instance conditions follow from actual native execution and encoding.
The remaining walk input is ordinary authenticated lookup semantics, kept explicit here. -/
theorem nativeInstance_ok (recordId : PTrie→Nat) (baseI : UpsInst) {root : PTrie}
    {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (hv : 1≤v.length) (hvsmall : v.length<2^24) (base : Nat→UpsPartI)
    {Qs : List UpsPartI} (he : encodeNativeParts recordId root run base=some Qs)
    (hb : ∀ Q∈Qs,ByteInput (positionedInstance recordId baseI root run v Qs) Q)
    (walk : WalkOkU (nativeInstance recordId baseI root run v Qs)) :
    InstOk (nativeInstance recordId baseI root run v Qs) := by
  have hlen := encodeNativeParts_length recordId hr base he
  have hpositive := trace_parts_positive hr
  have hbounds := traceInstance_bounds hr hw baseI
  have hcases := traceInstance_terminalCases hr baseI
  have hroot := nativeInstance_root recordId baseI hr base he
  refine {
    L1 := ?_
    nQ1 := ?_
    q1 := ?_
    ci := hbounds.1
    D := fixed_trace_descents hr
    ts := ⟨hbounds.2.2.1,hbounds.2.2.2.1⟩
    ti := hbounds.2.1
    x := hbounds.2.2.2.2
    tsEnd := hcases.1
    tsNib := hcases.2
    Lsmall := ?_
    nQ := ?_
    walk := walk
    rcStep := ?_
    cNStep := ?_
    rootRc := hroot.1
    rootDep := hroot.2.1
    rootSN := hroot.2.2
    memEnd := ?_
    bits := ?_ }
  · simpa [L,nativeInstance,signedInstance,positionedInstance,traceInstance] using hv
  · rw [nativeInstance_nQ,hlen]; omega
  · intro k hk
    rw [nativeInstance_nQ] at hk
    obtain ⟨p,Q,_,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr base he k hk
    rw [hpart]
    exact (hb Q (List.mem_of_getElem? hQ)).withMemorySign.fieldsOk.positive
  · simpa [L,nativeInstance,signedInstance,positionedInstance,traceInstance] using hvsmall
  · rw [nativeInstance_nQ]
    change Qs.length=nTof run.terminal.ix run.matched+
      (sourceDepths (fdepth root [0,15]-1) run).getD (descentCount run.parts) 0
    rw [nTof,case_from_index,sourceDepths_terminal,hlen]
    exact traceUpsert_nQ hr
  · intro k hk
    rw [nativeInstance_nQ] at hk
    exact (nativeInstance_chain recordId baseI hr base he k hk).1
  · intro k hk
    rw [nativeInstance_nQ] at hk
    exact (nativeInstance_chain recordId baseI hr base he k hk).2
  · intro k hk p hp
    rw [nativeInstance_nQ] at hk
    obtain ⟨native,Q,_,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr base he k hk
    rw [hpart] at hp ⊢
    exact (hb Q (List.mem_of_getElem? hQ)).withMemorySign.fieldsOk.memEnd hp
  · intro k hk
    rw [nativeInstance_nQ] at hk
    obtain ⟨p,Q,_,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr base he k hk
    rw [hpart]
    exact encoded_signed_bits henc (hb Q (List.mem_of_getElem? hQ))
end ZkFormal.NearV3.Render.UpsGen
