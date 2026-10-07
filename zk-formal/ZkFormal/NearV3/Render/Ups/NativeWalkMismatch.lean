import ZkFormal.NearV3.Render.Ups.NativeByteFamily

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near

/-- A genuine divergent split has distinct old/new nibbles. This reuses the
already constructed ordinary split-node occupancy proof. -/
theorem traceInstance_divergent (baseI : UpsInst) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (hc : run.terminal.ix=6 ∨ run.terminal.ix=9 ∨ run.terminal.ix=10) :
    (traceInstance baseI run v).x≠splitNewSlot (traceInstance baseI run v) := by
  obtain ⟨upper,hplan,_⟩ := traceUpsert_plan root [0,15] v run hr
  have hspb : UKind.SPB∈termPlan run.terminal run.matched := by
    cases hcs : run.terminal <;> simp_all [UCase.ix,termPlan,UCase.split]
  have hparts : UKind.SPB∈run.parts.map TreePart.kind := by rw [hplan]; simp [hspb]
  obtain ⟨p,hp,hkind⟩ := List.mem_map.mp hparts
  obtain ⟨Qs,he,hkinds,_⟩ := encodeNativeParts_total (fun _ => 0) hr (fun _ => default)
  have hten : 10∈Qs.map UpsPartI.kind := by
    rw [hkinds]
    exact List.mem_map.mpr ⟨p,hp,by rw [hkind]; rfl⟩
  obtain ⟨Q,hQ,hQkind⟩ := List.mem_map.mp hten
  obtain ⟨data⟩ := encodedNativeParts_byteInputs (fun _ => 0) baseI hr hw (fun _ => default) he Q hQ
  exact data.splitBitmap.distinct hQkind (by change run.terminal.ix≠4; omega)
    (by change run.terminal.ix=4 ∨ run.terminal.ix=6 ∨ run.terminal.ix=9 ∨ run.terminal.ix=10; omega)

/-- The absent-key edge contains an actual differing symbol, below the field modulus. -/
theorem traceInstance_absentSymbol (baseI : UpsInst) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (hc : 4≤(traceInstance baseI run v).ci) :
    let I := traceInstance baseI run v
    (if I.ci=4 then SYM_END else I.x)≠wsym I.ts ∧
      (if I.ci=4 then SYM_END else I.x)<ZkFormal.Algebra.P := by
  let I := traceInstance baseI run v
  change (if I.ci=4 then SYM_END else I.x)≠wsym I.ts ∧
    (if I.ci=4 then SYM_END else I.x)<ZkFormal.Algebra.P
  have hb := traceInstance_bounds hr hw baseI
  have he := traceInstance_terminalCases hr baseI
  have ht1 : 1≤I.ts := hb.2.2.1
  have ht2 : I.ts≤3 := hb.2.2.2.1
  have ht : I.ts=1 ∨ I.ts=2 ∨ I.ts=3 := by omega
  have hx : I.x<16 := hb.2.2.2.2
  have hp : 16<ZkFormal.Algebra.P := by decide
  by_cases h4 : I.ci=4
  · have hn : I.ts≠3 := by intro h; have := he.1 h; change I.ci=0 ∨ I.ci=1 ∨ I.ci=2 ∨ I.ci=5 ∨ I.ci=7 ∨ I.ci=8 at this; omega
    rcases ht with ht|ht|ht <;> simp_all [wsym,SYM_END]
  · have hbound : I.x<ZkFormal.Algebra.P := by omega
    simp only [h4,ite_false]
    refine ⟨?_,hbound⟩
    rcases ht with ht|ht|ht
    · have hcs := he.2 (by change I.ts≠3; omega)
      have hc' : run.terminal.ix=6 ∨ run.terminal.ix=9 ∨ run.terminal.ix=10 := by
        change I.ci=6 ∨ I.ci=9 ∨ I.ci=10
        change I.ci=3 ∨ I.ci=4 ∨ I.ci=6 ∨ I.ci=9 ∨ I.ci=10 at hcs
        change 4≤I.ci at hc
        omega
      have hn := traceInstance_divergent baseI hr hw hc'
      simpa [I,splitNewSlot,wsym,show (traceInstance baseI run v).ts=1 from ht] using hn
    · have hcs := he.2 (by change I.ts≠3; omega)
      have hc' : run.terminal.ix=6 ∨ run.terminal.ix=9 ∨ run.terminal.ix=10 := by
        change I.ci=6 ∨ I.ci=9 ∨ I.ci=10
        change I.ci=3 ∨ I.ci=4 ∨ I.ci=6 ∨ I.ci=9 ∨ I.ci=10 at hcs
        change 4≤I.ci at hc
        omega
      have hn := traceInstance_divergent baseI hr hw hc'
      simpa [I,splitNewSlot,wsym,show (traceInstance baseI run v).ts=2 from ht] using hn
    · simp [ht,wsym,SYM_END]; omega
end ZkFormal.NearV3.Render.UpsGen
