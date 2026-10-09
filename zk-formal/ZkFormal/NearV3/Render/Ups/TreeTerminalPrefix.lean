import ZkFormal.NearV3.Render.Ups.TreeWalkKeys
import ZkFormal.NearV3.Render.Ups.SplitMatched

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

def nativeNodeKey : PTrie→List Nat
  | .leaf key _ _ | .ext key _ _ => key
  | _ => []

def TerminalPrefix (run : TreeRun) : Prop :=
  run.matched≤(nativeNodeKey run.terminalSource).length ∧
    run.terminalKey.take run.matched=(nativeNodeKey run.terminalSource).take run.matched

theorem commonPrefix_take_both (a b : List Nat) :
    (commonPrefix a b).length≤a.length ∧
    b.take (commonPrefix a b).length=a.take (commonPrefix a b).length := by
  have ha := commonPrefix_left a b
  have hb := commonPrefix_right a b
  generalize commonPrefix a b=p at *
  constructor
  · have h := congrArg List.length ha
    simp only [List.length_append] at h
    omega
  · have hat : a.take p.length=p := by rw [ha,List.take_left]
    have hbt : b.take p.length=p := by rw [hb,List.take_left]
    exact hbt.trans hat.symm

theorem leafSplitRun_terminalSource (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    (leafSplitRun k s m key v).terminalSource=.leaf k s m := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;> simp [wrapRun,terminalRun,pushPart]

theorem extSplitRun_terminalSource (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    (extSplitRun k c m key v).terminalSource=.ext k c m := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,terminalRun]
  | cons x xs => cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [wrapRun,terminalRun,pushPart]

theorem leafSplitRun_terminalPrefix (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes)
    (hne : k≠key) : TerminalPrefix (leafSplitRun k s m key v) := by
  simpa only [TerminalPrefix,leafSplitRun_terminalSource,leafSplitRun_terminalKey,
    leafSplitRun_matched k s m key v hne,nativeNodeKey] using commonPrefix_take_both k key

theorem extSplitRun_terminalPrefix (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    TerminalPrefix (extSplitRun k c m key v) := by
  simpa only [TerminalPrefix,extSplitRun_terminalSource,extSplitRun_terminalKey,
    extSplitRun_matched,nativeNodeKey] using commonPrefix_take_both k key

mutual
/-- Before its terminal lookup, the native source key agrees with every consumed query nibble. -/
theorem traceUpsert_terminalPrefix : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → TerminalPrefix run
  | .hash _, _, _, _, hr => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run; simp [TerminalPrefix,terminalRun,nativeNodeKey,he]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run; exact leafSplitRun_terminalPrefix k s m key v he
  | .ext k c m, key, v, run, hr => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run; exact extSplitRun_terminalPrefix k c m key v
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hc] at hr
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          exact traceUpsert_terminalPrefix c _ v inner hc
  | .branch bv cs m, [], v, run, hr => by
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run
    cases bv <;> simp [TerminalPrefix,terminalRun,nativeNodeKey]
  | .branch bv cs m, n::key, v, run, hr => by
    cases hc : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hc] at hr
    | some inner =>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_terminalPrefix (.branch bv cs m) (n::key) cs n key v inner hc

theorem traceKids_terminalPrefix : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), traceKids source wholeKey cs n key v=some run →
    TerminalPrefix run.inner
  | _, _, .nil, _, _, _, _, hr => by simp [traceKids] at hr
  | source, wholeKey, .none rest, 0, key, v, run, hr => by
    simp only [traceKids,Option.some.injEq] at hr
    subst run; simp [TerminalPrefix,terminalRun]
  | source, wholeKey, .some child rest, 0, key, v, run, hr => by
    cases hm : child.mem? with
    | none => simp [traceKids,hm] at hr
    | some cm =>
      cases hc : traceUpsert child key v with
      | none => simp [traceKids,hm,hc] at hr
      | some inner =>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        exact traceUpsert_terminalPrefix child key v inner hc
  | source, wholeKey, .none rest, n+1, key, v, run, hr => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_terminalPrefix source wholeKey rest n key v inner hc
  | source, wholeKey, .some child rest, n+1, key, v, run, hr => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_terminalPrefix source wholeKey rest n key v inner hc
end
end ZkFormal.NearV3.Render.UpsGen
