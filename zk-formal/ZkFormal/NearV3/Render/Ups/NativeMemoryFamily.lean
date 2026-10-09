import ZkFormal.NearV3.Render.Ups.NativeUpperMemory
import ZkFormal.NearV3.Render.Ups.TreeTerminalMemory

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

private theorem termPlan_head_nonupper (cs : UCase) (matched : Nat) (rest : List UKind) :
    ((termPlan cs matched++rest)[0]?).map UKind.upper=some false := by
  cases cs <;> simp [termPlan,UCase.split,UKind.upper]

theorem traceUpsert_first_nonupper {root : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root key v=some run) {p : TreePart} (hp : run.parts[0]?=some p) :
    ¬upperKind p.kind := by
  obtain ⟨upper,hplan,_⟩ := traceUpsert_plan root key v run hr
  have hg := congrArg (fun xs : List UKind => (xs[0]?).map UKind.upper) hplan
  simp only [List.getElem?_map,hp,Option.map_some,termPlan_head_nonupper,Option.some.injEq] at hg
  cases hc : p.kind <;> simp_all [UKind.upper,upperKind]

/-- The entire memory family is constructed from native upsert and executable metadata.
No per-part memory equation or carry constraint is supplied by the caller. -/
theorem nativeInstance_memOk (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hw : root.wf=true) (hv : v.length<2^24) (hd : fdepth root [0,15]≤400)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeMemoryParts recordId root run base=some Qs) (k : Nat) (hk : k<Qs.length)
    (hq : (part (nativeInstance recordId baseI root run v Qs) k).qhk<2^22)
    (hpref : (part (nativeInstance recordId baseI root run v Qs) k).phk<2^22) :
    MemOk (nativeInstance recordId baseI root run v Qs)
      (part (nativeInstance recordId baseI root run v Qs) k) := by
  let I0 := positionedInstance recordId baseI root run v Qs
  let B := nativeMemoryBase run base
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr B he k hk
  by_cases hu : upperKind p.kind
  · have hkpos : 0<k := by
      by_cases heq : k=0
      · subst k; exact (traceUpsert_first_nonupper hr hp hu).elim
      · omega
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
    apply nativeInstance_upperMemOk recordId baseI hr hw hv hd base he j hk _ hq hpref
    rw [hpart]
    change Q.kind=0 ∨ Q.kind=1 ∨ Q.kind=11
    rw [encodeTreePart_kind henc]
    cases hc : p.kind <;> simp_all [upperKind,UKind.ix]
  · have hm : Q.mB=splitChildMemory run.matched p := by
      rw [encodeTreePart_mB henc]
      simp [positionedPart,withPlanPosition,withDescentPosition,B,nativeMemoryBase,hp,
        show ¬(p.kind=.RDB ∨ p.kind=.RDE ∨ p.kind=.PT) from hu]
    have hchild : SourceBytes (child I0 Q) :=
      trace_encoded_child_sourceBytes hr hw (nativePartBase recordId root run B) he I0 rfl Q
    rw [hpart] at hq hpref ⊢
    have hmem := traceUpsert_terminalMemOk root [0,15] v run hr hw (Or.inr (Or.inr rfl)) hv
      I0 p (List.mem_of_getElem? hp) _ Q henc hu hm hq hpref hchild
    exact hmem.signedInstance
end ZkFormal.NearV3.Render.UpsGen
