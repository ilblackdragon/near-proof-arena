import ZkFormal.NearV3.Render.Ups.BytePlanShape
import ZkFormal.NearV3.Render.Ups.PlanInput

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

theorem planned_terminal_kind (run : TreeRun) (hp : run.Planned) (k : Nat) (part : TreePart)
    (hk : run.parts[k]?=some part) (hn : k<(termPlan run.terminal run.matched).length) :
    part.kind=(termPlan run.terminal run.matched).getD k .RLP := by
  obtain ⟨upper,he,_⟩ := hp
  have hm := congrArg (fun kinds : List UKind => kinds[k]?) he
  simp only [List.getElem?_map,hk,Option.map_some] at hm
  rw [List.getElem?_append] at hm
  simp only [hn,ite_true] at hm
  simpa only [Option.getD_some,List.getD_eq_getElem?_getD] using congrArg (fun x => x.getD .RLP) hm

/-- Full PartOk for an encoded actual runtime part. Positional data is constructed;
node type/prefix rules follow from native execution; the ordinary byte constructor
supplies the new-key and occupied-child semantics. No AIR equation is assumed. -/
theorem encoded_nativePart_ok (recordId : PTrie→Nat) (baseI : UpsInst) {root : PTrie}
    {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (parts : List UpsPartI) (k : Nat) (part : TreePart) (hk : run.parts[k]?=some part)
    (base Q : UpsPartI)
    (he : encodeTreePart (positionedPart recordId (fdepth root [0,15]-1) run k part base) part=some Q)
    (bytes : ByteInput (positionedInstance recordId baseI root run v parts) Q) :
    PartOk (positionedInstance recordId baseI root run v parts) k Q := by
  have hp : part∈run.parts := List.mem_of_getElem? hk
  have pos := encoded_positionedPart_facts recordId baseI hr parts k part hk base Q he
  have types := trace_encoded_typeFacts hr hp he
  have shape := trace_nativePrefixFacts hr (positionedInstance recordId baseI root run v parts) hp he
  have hfixed : traceInstance (positionedInstance recordId baseI root run v parts) run v=
      positionedInstance recordId baseI root run v parts := rfl
  rw [hfixed] at shape
  have hkind := encodeTreePart_kind he
  have hplan := traceUpsert_plan root [0,15] v run hr
  have hnt : nTof (positionedInstance recordId baseI root run v parts).ci
      (positionedInstance recordId baseI root run v parts).ti=(termPlan run.terminal run.matched).length :=
    traceInstance_nT baseI run v
  refine {
    kind := bytes.kind
    kindT := ?_
    kindU := ?_
    pdepT := pos.pdepT
    pdepU := pos.pdepU
    rcT := pos.rcT
    sd := pos.sd
    sdRD := pos.sdRD
    sdT := pos.sdT
    sN := pos.sN
    pdepS := pos.pdepS
    ty := types.ty
    tyBr := types.tyBr
    tyBV := types.tyBV
    tyExt := types.tyExt
    tyLeaf := types.tyLeaf
    tySpb := shape.tySpb
    pt := shape.pt
    spbKids := bytes.spb_children
    nlf := bytes.nlf_plan
    wex := bytes.wex_plan types
    mv := shape.mv
    mveOdd := shape.mveOdd
    xcp := shape.xcp
    jmD := pos.jmD
    jmS := pos.jmS }
  · intro h
    rw [hnt] at h
    change Q.kind=((termPlan (UCase.all.getD run.terminal.ix .LP) run.matched).getD k .RLP).ix
    rw [case_from_index,hkind,planned_terminal_kind run hplan k part hk h]
  · intro h
    rw [hnt] at h
    have hu := planned_upper_kind run hplan k part hk h
    cases hc : part.kind <;> simp_all [UKind.upper,UKind.ix]
end ZkFormal.NearV3.Render.UpsGen
