import ZkFormal.NearV3.Render.Ups.TreeWalkShape
import ZkFormal.NearV3.Render.Ups.TreeSourceChain

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near ZkFormal.Near.Render

theorem nativeChildAt_none_iff : ∀ (kids : Kids) (n : Nat),
    (treeKids kids).getD n .none=.none ↔ nativeChildAt kids n=none
  | .nil, n => by simp [treeKids,nativeChildAt]
  | .none rest, 0 => by simp [treeKids,nativeChildAt]
  | .some c rest, 0 => by simp [treeKids,treeKid,nativeChildAt]
  | .none rest, n+1 => by simpa [treeKids,nativeChildAt] using nativeChildAt_none_iff rest n
  | .some c rest, n+1 => by simpa [treeKids,nativeChildAt] using nativeChildAt_none_iff rest n

/-- Native evidence for a terminal branch lookup; the actual bitmap is reconstructed
from these children later, not replaced with a convenient all-zero bitmap. -/
def BranchTerminal (run : TreeRun) : Prop :=
  (run.terminal=.BV → ∃ kids mem,run.terminalSource=.branch none kids mem ∧ run.matched=0) ∧
  (run.terminal=.BI → ∃ value kids mem slot rest,
    run.terminalSource=.branch value kids mem ∧ run.terminalKey=slot::rest ∧
    nativeChildAt kids slot=none ∧ run.matched=0)

theorem leafSplitRun_branchTerminal (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    BranchTerminal (leafSplitRun k s m key v) := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;> simp [BranchTerminal,terminalRun,wrapRun,pushPart]

theorem extSplitRun_branchTerminal (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    BranchTerminal (extSplitRun k c m key v) := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,BranchTerminal,terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [BranchTerminal,terminalRun,wrapRun,pushPart]

mutual
/-- Every native branch terminal retains the exact absent value/child witness. -/
theorem traceUpsert_branchTerminal : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → BranchTerminal run
  | .hash _, _, _, _, hr => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run; simp [BranchTerminal,terminalRun]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run; exact leafSplitRun_branchTerminal k s m key v
  | .ext k c m, key, v, run, hr => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run; exact extSplitRun_branchTerminal k c m key v
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hc] at hr
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          exact traceUpsert_branchTerminal c _ v inner hc
  | .branch bv cs m, [], v, run, hr => by
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run
    cases bv <;> simp [BranchTerminal,terminalRun]
  | .branch bv cs m, n::key, v, run, hr => by
    cases hc : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hc] at hr
    | some inner =>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      cases hi : inner.inserted with
      | true =>
        have hin := (traceKids_inserted _ _ _ _ _ _ _ hc hi).2.2
        have habs := (traceKids_effect _ _ _ _ _ _ _ hc).2.2.1.mp hi
        have hnone := (nativeChildAt_none_iff cs n).mp habs
        simp only [BranchTerminal,pushPart,hin,terminalRun,reduceCtorEq,false_implies,true_implies,true_and]
        exact ⟨bv,cs,m,n,key,rfl,rfl,hnone,trivial⟩
      | false => exact traceKids_branchTerminal (.branch bv cs m) (n::key) cs n key v inner hc hi

theorem traceKids_branchTerminal : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), traceKids source wholeKey cs n key v=some run →
    run.inserted=false → BranchTerminal run.inner
  | _, _, .nil, _, _, _, _, hr, _ => by simp [traceKids] at hr
  | source, wholeKey, .none rest, 0, key, v, run, hr, hi => by
    simp only [traceKids,Option.some.injEq] at hr
    subst run; cases hi
  | source, wholeKey, .some child rest, 0, key, v, run, hr, hi => by
    cases hm : child.mem? with
    | none => simp [traceKids,hm] at hr
    | some cm =>
      cases hc : traceUpsert child key v with
      | none => simp [traceKids,hm,hc] at hr
      | some inner =>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        exact traceUpsert_branchTerminal child key v inner hc
  | source, wholeKey, .none rest, n+1, key, v, run, hr, hi => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_branchTerminal source wholeKey rest n key v inner hc hi
  | source, wholeKey, .some child rest, n+1, key, v, run, hr, hi => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_branchTerminal source wholeKey rest n key v inner hc hi
end
end ZkFormal.NearV3.Render.UpsGen
