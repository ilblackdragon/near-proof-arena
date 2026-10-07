import ZkFormal.NearV3.Render.Ups.TreeInsertTrace

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec

/-- The existing child reached by ordinary branch recursion. -/
structure ExistingChild (run : KidsRun) (key : List Nat) (v : Bytes) where
  node : PTrie
  wf : node.wf=true
  trace : traceUpsert node key v=some run.inner
  oldMem : run.oldMem=node.memD
  newMem : run.newMem=run.inner.output.memD

/-- Recover the actual existing-child witness directly from executable recursion. -/
def traceKids_existing : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (width n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun),
    Kids.wf cs width=true → traceKids source wholeKey cs n key v=some run → run.inserted=false →
    ExistingChild run key v
  | _, _, .nil, _, _, _, _, _, _, h, _ => by simp [traceKids] at h
  | source, wholeKey, .none rest, _, 0, key, v, run, _, h, hi => by
    simp only [traceKids,Option.some.injEq] at h
    subst run; cases hi
  | source, wholeKey, .some c rest, width, 0, key, v, run, hw, h, hi => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        exact ⟨c,hw.1.2,hr,by simp [PTrie.memD,hm],rfl⟩
  | source, wholeKey, .none rest, width, n+1, key, v, run, hw, h, hi => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      let e := traceKids_existing source wholeKey rest (width-1) n key v inner hw.2 hr hi
      exact ⟨e.node,e.wf,e.trace,e.oldMem,e.newMem⟩
  | source, wholeKey, .some c rest, width, n+1, key, v, run, hw, h, hi => by
    simp only [Kids.wf,Bool.and_eq_true,bne_iff_ne] at hw
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      let e := traceKids_existing source wholeKey rest (width-1) n key v inner hw.2 hr hi
      exact ⟨e.node,e.wf,e.trace,e.oldMem,e.newMem⟩
end ZkFormal.NearV3.Render.UpsGen
