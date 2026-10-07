import ZkFormal.NearV3.Render.Ups.TreeExtInput

/-! The actual child recursion updates exactly one branch slot. These are ordinary
runtime/list facts, independent of the update-table constraints. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near ZkFormal.Near.Render

def KidsRun.Effect (cs : Kids) (n : Nat) (run : KidsRun) : Prop :=
  n < (treeKids cs).length ∧
  treeKids run.output = (treeKids cs).set n (treeKid run.inner.output) ∧
  (run.inserted=true ↔ (treeKids cs).getD n .none=.none) ∧
  isNode run.inner.output=true

theorem traceKids_effect : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v=some run → run.Effect cs n
  | _, _, .nil, _, _, _, _, h => by simp [traceKids] at h
  | source, wholeKey, .none rest, 0, key, v, run, h => by
    simp only [traceKids,Option.some.injEq] at h
    subst run
    simp [KidsRun.Effect,treeKids,terminalRun,newLeaf,isNode]
  | source, wholeKey, .some c rest, 0, key, v, run, h => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        have hu : c.upsert key v=some inner.output := by
          have he := traceUpsert_output c key v
          simpa [hr] using he.symm
        simp [KidsRun.Effect,treeKids,treeKid,upsert_isNode c key v inner.output hu]
  | source, wholeKey, .none rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      have ih := traceKids_effect source wholeKey rest n key v inner hr
      simpa [KidsRun.Effect,treeKids,List.set] using ih
  | source, wholeKey, .some c rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      have ih := traceKids_effect source wholeKey rest n key v inner hr
      simpa [KidsRun.Effect,treeKids,List.set] using ih

end ZkFormal.NearV3.Render.UpsGen
