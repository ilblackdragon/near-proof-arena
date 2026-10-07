import ZkFormal.NearV3.Render.Ups.TreePlanDepth
import ZkFormal.NearV3.Render.Ups.TreeMetadata

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

@[simp] theorem case_from_index (cs : UCase) : UCase.all.getD cs.ix .LP=cs := by cases cs <;> rfl

@[simp] theorem traceInstance_nT (base : UpsInst) (run : TreeRun) (v : Bytes) :
    nTof (traceInstance base run v).ci (traceInstance base run v).ti=
      (termPlan run.terminal run.matched).length := by simp only [traceInstance,nTof,case_from_index]

private theorem mapped_getD {α β : Type} (xs : List α) (f : α→β) (d : α) (e : β)
    (k : Nat) (hk : k<xs.length) : (xs.map f).getD k e=f (xs.getD k d) := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hk]

/-- The actual encoded sequence obeys both terminal and upper-kind parts of PartOk. -/
theorem encoded_plan_kinds (run : TreeRun) (Qs : List UpsPartI)
    (hp : run.Planned) (he : Qs.map UpsPartI.kind=run.parts.map (fun p => p.kind.ix))
    (hl : Qs.length=run.parts.length) (k : Nat) (hk : k<Qs.length) :
    ((k<(termPlan run.terminal run.matched).length) →
      (Qs.getD k default).kind=((termPlan run.terminal run.matched).getD k .RLP).ix) ∧
    (((termPlan run.terminal run.matched).length≤k) →
      (Qs.getD k default).kind=0 ∨ (Qs.getD k default).kind=1 ∨ (Qs.getD k default).kind=11) := by
  obtain ⟨upper,hu,hupper⟩ := hp
  have hm : Qs.map UpsPartI.kind=(termPlan run.terminal run.matched++upper).map UKind.ix := by
    rw [he,←hu,List.map_map]
    rfl
  have hlen : Qs.length=(termPlan run.terminal run.matched++upper).length := by
    have h := congrArg List.length hu
    simpa [hl] using h
  have hg := congrArg (fun xs : List Nat => xs.getD k 0) hm
  rw [mapped_getD Qs _ default _ k hk,
    mapped_getD _ UKind.ix .RLP _ k (by omega)] at hg
  constructor
  · intro ht
    rw [hg]
    simp [List.getD_eq_getElem?_getD,List.getElem?_append,ht]
  · intro ht
    have hk' : k-(termPlan run.terminal run.matched).length<upper.length := by
      simp only [List.length_append] at hlen; omega
    have hget : (termPlan run.terminal run.matched++upper).getD k .RLP=
        upper.getD (k-(termPlan run.terminal run.matched).length) .RLP := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_append,show ¬k<(termPlan run.terminal run.matched).length by omega]
    rw [hg,hget]
    have hupp : (upper.getD (k-(termPlan run.terminal run.matched).length) .RLP).upper=true := by
      apply hupper
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk',Option.getD_some]
      exact List.getElem_mem hk'
    generalize upper.getD (k-(termPlan run.terminal run.matched).length) .RLP=c at hupp ⊢
    cases c <;> simp [UKind.upper,UKind.ix] at hupp ⊢
end ZkFormal.NearV3.Render.UpsGen
