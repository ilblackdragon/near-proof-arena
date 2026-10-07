import ZkFormal.NearV3.Render.Ups.BranchSideAllocation

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

def WalkShape (key : List Nat) (run : TreeRun) : Prop :=
  run.terminalKey.length≤key.length ∧
  descentCount run.parts≤key.length-run.terminalKey.length ∧
  (descentCount run.parts=0 → run.terminalKey.length=key.length)

theorem leafSplitRun_terminalKey (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    (leafSplitRun k s m key v).terminalKey=key := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp [h1,h2,wrapRun_terminalKey,terminalRun]

theorem extSplitRun_terminalKey (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    (extSplitRun k c m key v).terminalKey=key := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,terminalRun]
  | cons x xs => cases h2 : key.drop p.length <;> simp [h1,h2,wrapRun_terminalKey,terminalRun]

mutual
/-- Proper source-level entries consume at least one key nibble; consuming none
is exactly the case with no proper source-level entry. Empty extensions are skipped. -/
theorem traceUpsert_walkShape : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → WalkShape key run
  | .hash _, _, _, _, hr => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run; simp [WalkShape,terminalRun,descentCount,descendKind]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run; simp [WalkShape,leafSplitRun_terminalKey,leafSplitRun_descents]
  | .ext k c m, key, v, run, hr => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run; simp [WalkShape,extSplitRun_terminalKey,extSplitRun_descents]
    | true =>
      obtain ⟨suffix,hsuffix⟩ := (isPrefix_iff k key).mp hp
      have hlen := congrArg List.length hsuffix
      simp only [List.length_append] at hlen
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hc] at hr
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          have ih := traceUpsert_walkShape c (key.drop k.length) v inner hc
          unfold WalkShape at ih ⊢
          cases k <;> simp [pushPart,descendKind] <;>
            simp only [List.length_drop,List.length_nil,List.length_cons] at ih hlen <;> omega
  | .branch bv cs m, [], v, run, hr => by
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run; cases bv <;> simp [WalkShape,terminalRun,descentCount,descendKind]
  | .branch bv cs m, n::key, v, run, hr => by
    cases hc : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hc] at hr
    | some inner =>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      cases hi : inner.inserted with
      | true =>
        have hin := (traceKids_inserted _ _ _ _ _ _ _ hc hi).2.2
        simp [WalkShape,pushPart,hin,terminalRun,descentCount,descendKind,hi]
      | false =>
        have ih := traceKids_walkShape (.branch bv cs m) (n::key) cs n key v inner hc hi
        unfold WalkShape at ih ⊢
        simp [pushPart,hi,descendKind]
        omega

theorem traceKids_walkShape : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), traceKids source wholeKey cs n key v=some run →
    run.inserted=false → WalkShape key run.inner
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
        exact traceUpsert_walkShape child key v inner hc
  | source, wholeKey, .none rest, n+1, key, v, run, hr, hi => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_walkShape source wholeKey rest n key v inner hc hi
  | source, wholeKey, .some child rest, n+1, key, v, run, hr, hi => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_walkShape source wholeKey rest n key v inner hc hi
end
/-- The seven possible four-row walk geometries, derived from native traversal. -/
theorem traceUpsert_walk_geometry {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) :
    (descentCount run.parts=0 ∧ run.splitCursor [0,15]=run.matched+1) ∨
    (descentCount run.parts=1 ∧ run.splitCursor [0,15]=2 ∧ run.matched=0) ∨
    (descentCount run.parts=1 ∧ run.splitCursor [0,15]=3 ∧ run.matched≤1) ∨
    (descentCount run.parts=2 ∧ run.splitCursor [0,15]=3 ∧ run.matched=0) := by
  have hg := traceUpsert_walkShape root [0,15] v run hr
  obtain ⟨_,_,_,hmatched⟩ := traceUpsert_keys root [0,15] v run hr
  simp only [WalkShape,List.length_cons,List.length_nil] at hg
  simp only [TreeRun.splitCursor,TreeRun.consumed,List.length_cons,List.length_nil]
  omega
end ZkFormal.NearV3.Render.UpsGen
