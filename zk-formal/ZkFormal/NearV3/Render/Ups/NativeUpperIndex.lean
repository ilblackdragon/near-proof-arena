import ZkFormal.NearV3.Render.Ups.NativeChildId

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- A native ancestor always has a preceding bottom-up output part. -/
theorem traceUpsert_upper_index {root : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root key value=some run) {k : Nat} {p : TreePart}
    (hp : run.parts[k]?=some p) (hu : upperKind p.kind) : 0<k := by
  by_cases hk : k=0
  · subst k
    obtain ⟨upper,he,_⟩ := traceUpsert_plan root key value run hr
    have hh := congrArg (fun xs : List UKind=>xs[0]?) he
    rw [List.getElem?_map,hp] at hh
    cases hc : run.terminal <;> simp [hc,termPlan] at hh <;> simp_all [upperKind]
  · omega
end ZkFormal.NearV3.Render.UpsGen
