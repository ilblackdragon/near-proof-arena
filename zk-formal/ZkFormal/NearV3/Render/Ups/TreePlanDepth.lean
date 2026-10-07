import ZkFormal.NearV3.Render.Ups.TreePartCount

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 UpsRows UpsSpec

mutual
/-- Exact plan length: one ancestor part per revealed node above the terminal. -/
theorem traceUpsert_plan_depth : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run →
    run.parts.length+1=(termPlan run.terminal run.matched).length+fdepth t key
  | .hash _, _, _, _, h => by simp [traceUpsert] at h
  | .leaf k s m, key, v, run, h => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run; simp [terminalRun,fdepth,termPlan,UCase.split]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run
      have ht := congrArg List.length (leafSplitRun_plan k s m key v)
      simpa only [List.length_map,fdepth] using congrArg (·+1) ht
  | .ext k c m, key, v, run, h => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run
      have ht := congrArg List.length (extSplitRun_plan k c m key v hp)
      simpa only [List.length_map,fdepth,hp,Bool.false_eq_true,ite_false] using congrArg (·+1) ht
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at h
      | some cm =>
        cases hr : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hr] at h
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst run
          have ih := traceUpsert_plan_depth c (key.drop k.length) v inner hr
          simp [pushPart,fdepth,hp]; omega
  | .branch bv cs m, [], v, run, h => by
    simp only [traceUpsert,Option.some.injEq] at h
    subst run
    cases bv <;> simp [terminalRun,fdepth,termPlan,UCase.split]
  | .branch bv cs m, n::key, v, run, h => by
    cases hr : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hr] at h
    | some inner =>
      simp only [traceUpsert,hr,Option.map_some,Option.some.injEq] at h
      subst run
      have ih := traceKids_plan_depth (.branch bv cs m) (n::key) cs n key v inner hr
      simp [pushPart,fdepth]; omega
/-- A missing child already accounts for the RBI part that its parent emits. -/
theorem traceKids_plan_depth : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v=some run →
    run.inner.parts.length+1=(termPlan run.inner.terminal run.inner.matched).length+kfdepth cs n key
  | _, _, .nil, _, _, _, _, h => by simp [traceKids] at h
  | source, wholeKey, .none rest, 0, key, v, run, h => by
    simp only [traceKids,Option.some.injEq] at h
    subst run; simp [terminalRun,kfdepth,termPlan]
  | source, wholeKey, .some c rest, 0, key, v, run, h => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        exact traceUpsert_plan_depth c key v inner hr
  | source, wholeKey, .none rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_plan_depth source wholeKey rest n key v inner hr
  | source, wholeKey, .some c rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_plan_depth source wholeKey rest n key v inner hr
end

/-- The native depth fixes the renderer's part-count equation exactly. -/
theorem traceUpsert_nQ {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (h : traceUpsert t key v=some run) :
    run.parts.length=(termPlan run.terminal run.matched).length+(fdepth t key-1) := by
  have he := traceUpsert_plan_depth t key v run h
  have hd : 1≤fdepth t key := by
    cases t with
    | hash hash => simp [traceUpsert] at h
    | leaf => simp [fdepth]
    | ext k c m => simp [fdepth]; split <;> omega
    | branch value kids mem => cases key <;> simp [fdepth]
  omega
end ZkFormal.NearV3.Render.UpsGen
