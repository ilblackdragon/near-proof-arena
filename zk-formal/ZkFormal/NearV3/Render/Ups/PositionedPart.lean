import ZkFormal.NearV3.Render.Ups.TreeRootSource

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Fill native positional metadata before byte encoding. Store-specific source cid
and window fields remain in base; IDs are provided by the authenticated store allocator. -/
def positionedPart (recordId : PTrie→Nat) (depth : Nat) (run : TreeRun) (k : Nat)
    (part : TreePart) (base : UpsPartI) : UpsPartI :=
  {withPlanPosition depth (termPlan run.terminal run.matched).length k
      (withDescentPosition run.parts k {base with kind:=part.kind.ix}) with
    sN := recordId part.source
    cN := if k=0 then 0 else ((run.parts[k-1]?).map (fun p => recordId p.source)).getD 0}

/-- Instance path metadata from the actual run, independent of the byte-table allocation. -/
def positionedInstance (recordId : PTrie→Nat) (base : UpsInst) (root : PTrie) (run : TreeRun)
    (v : Bytes) (parts : List UpsPartI) : UpsInst :=
  {traceInstance base run v with
    rid := recordId root
    D := descentCount run.parts
    N := sourceLevelIds recordId run
    dep := sourceDepths (fdepth root [0,15]-1) run
    parts := parts}

/-- Positional obligations proved by the allocator; node-kind/shape obligations are separate. -/
structure PartPositionFacts (I : UpsInst) (k : Nat) (Q : UpsPartI) : Prop where
  pdepT : k<nTof I.ci I.ti → Q.pdep=I.dep.getD I.D 0
  pdepU : nTof I.ci I.ti≤k → Q.pdep+(k+1-nTof I.ci I.ti)=I.dep.getD I.D 0
  rcT : k<nTof I.ci I.ti → Q.rc=I.D
  sd : Q.sd<3
  sdRD : Q.kind=0 ∨ Q.kind=1 → Q.sd+1=Q.rc
  sdT : 2≤Q.kind → Q.kind≠11 → Q.sd=I.D
  sN : Q.kind≠11 → Q.sN=I.N.getD Q.sd 0
  pdepS : Q.kind≠11 → Q.pdep=I.dep.getD Q.sd 0
  jmD : Q.kind=0 ∨ Q.kind=1 ∨ Q.kind=9 ∨ Q.kind=11 → Q.jm=k
  jmS : Q.kind=10 → (I.ci=5 ∨ I.ci=6 ∨ I.ci=7 ∨ I.ci=9) → Q.jm=1

/-- The complete positional field block follows from actual trace execution. -/
theorem positionedPart_facts (recordId : PTrie→Nat) (baseI : UpsInst) {root : PTrie}
    {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (parts : List UpsPartI) (k : Nat) (part : TreePart) (hk : run.parts[k]?=some part) (base : UpsPartI) :
    PartPositionFacts (positionedInstance recordId baseI root run v parts) k
      (positionedPart recordId (fdepth root [0,15]-1) run k part base) := by
  have hplan := traceUpsert_plan root [0,15] v run hr
  have hlen : k<run.parts.length := List.getElem?_eq_some_iff.mp hk |>.1
  have hnt : nTof (positionedInstance recordId baseI root run v parts).ci
      (positionedInstance recordId baseI root run v parts).ti=(termPlan run.terminal run.matched).length :=
    traceInstance_nT baseI run v
  have hdepth : (positionedInstance recordId baseI root run v parts).dep.getD
      (positionedInstance recordId baseI root run v parts).D 0=fdepth root [0,15]-1 :=
    sourceDepths_terminal _ run
  constructor
  · intro h
    rw [hdepth,hnt] at *
    exact planDepth_terminal _ _ k h
  · intro h
    rw [hdepth,hnt] at *
    exact (allocated_plan_depth hr k hlen base).2 h
  · intro h
    rw [hnt] at h
    exact planned_terminal_counter run hplan k (by omega)
  · exact allocated_descent_bound hr k {base with kind:=part.kind.ix}
  · exact allocated_descent_source run.parts k {base with kind:=part.kind.ix} part hk rfl
  · intro h _
    exact allocated_terminal_source run.parts k {base with kind:=part.kind.ix} h
  · intro h
    exact (allocated_sourceLevel_lookup recordId hr k part hk {base with kind:=part.kind.ix} rfl h).symm
  · intro h
    exact (allocated_sourceDepth_lookup hr k part hk {base with kind:=part.kind.ix} rfl h _).symm
  · exact planMemoryIndex_down part.kind.ix k
  · intro h _
    change planMemoryIndex part.kind.ix k=1
    change part.kind.ix=10 at h
    rw [h]
    exact planMemoryIndex_split k

/-- Parent-child source chaining is filled directly from adjacent native parts. -/
theorem positionedPart_chain (recordId : PTrie→Nat) (depth : Nat) (run : TreeRun)
    (k : Nat) (part next : TreePart) (hp : run.parts[k]?=some part) (base nextBase : UpsPartI) :
    (positionedPart recordId depth run (k+1) next nextBase).cN=
      (positionedPart recordId depth run k part base).sN := by simp [positionedPart,hp]

/-- Byte encoding preserves every positional fact from the native allocator. -/
theorem encodeTreePart_positionFacts {I : UpsInst} {k : Nat} {base Q : UpsPartI} {part : TreePart}
    (he : encodeTreePart base part=some Q) (hk : base.kind=part.kind.ix)
    (h : PartPositionFacts I k base) : PartPositionFacts I k Q := by
  unfold encodeTreePart at he
  cases hs : treeNode part.source <;> cases hd : treeNode part.output <;> simp [hs,hd] at he
  subst Q
  constructor
  · simpa only [encodePart,hk] using h.pdepT
  · simpa only [encodePart,hk] using h.pdepU
  · simpa only [encodePart,hk] using h.rcT
  · simpa only [encodePart,hk] using h.sd
  · simpa only [encodePart,hk] using h.sdRD
  · simpa only [encodePart,hk] using h.sdT
  · simpa only [encodePart,hk] using h.sN
  · simpa only [encodePart,hk] using h.pdepS
  · simpa only [encodePart,hk] using h.jmD
  · simpa only [encodePart,hk] using h.jmS

theorem encoded_positionedPart_facts (recordId : PTrie→Nat) (baseI : UpsInst) {root : PTrie}
    {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (parts : List UpsPartI) (k : Nat) (part : TreePart) (hk : run.parts[k]?=some part)
    (base Q : UpsPartI)
    (he : encodeTreePart (positionedPart recordId (fdepth root [0,15]-1) run k part base) part=some Q) :
    PartPositionFacts (positionedInstance recordId baseI root run v parts) k Q :=
  encodeTreePart_positionFacts he rfl (positionedPart_facts recordId baseI hr parts k part hk base)
end ZkFormal.NearV3.Render.UpsGen
