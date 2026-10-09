import ZkFormal.NearV3.Render.Ups.TreeBranchInput

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Missing-child recursion emits exactly the fresh leaf, with zero old usage. -/
theorem traceKids_inserted : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v=some run → run.inserted=true →
    run.oldMem=0 ∧ run.newMem=leafMem key v.length ∧
    run.inner=terminalRun source wholeKey .BI 0 (newLeaf key v) [⟨.NLF,source,newLeaf key v,0⟩]
  | _, _, .nil, _, _, _, _, h, _ => by simp [traceKids] at h
  | source, wholeKey, .none rest, 0, key, v, run, h, _ => by
    simp only [traceKids,Option.some.injEq] at h
    subst run; exact ⟨rfl,rfl,rfl⟩
  | source, wholeKey, .some c rest, 0, key, v, run, h, hi => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        cases hi
  | source, wholeKey, .none rest, n+1, key, v, run, h, hi => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_inserted source wholeKey rest n key v inner hr hi
  | source, wholeKey, .some c rest, n+1, key, v, run, h, hi => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_inserted source wholeKey rest n key v inner hr hi
end ZkFormal.NearV3.Render.UpsGen
