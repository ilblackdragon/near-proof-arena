import ZkFormal.NearV3.Render.Ups.TreeResolvePath

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

def properPath (run : TreeRun) : List TreePart :=
  (run.parts.filter (fun p => descendKind p.kind)).reverse

def PathChain (run : TreeRun) : Prop :=
  ∀ i p,(properPath run)[i]?=some p →
    (sourcePathChild p).map resolveNative=(nativePathNodes run)[i+1]?

theorem properPath_push (run : TreeRun) (p : TreePart) :
    properPath (pushPart run p)=(if descendKind p.kind then [p] else [])++properPath run := by
  by_cases h : descendKind p.kind=true <;>
    simp [properPath,pushPart,List.filter_append,List.reverse_append,h]

theorem pathChain_push {run : TreeRun} (hc : PathChain run) (p : TreePart)
    (hl : descendKind p.kind=true →
      (sourcePathChild p).map resolveNative=(nativePathNodes run).head?) : PathChain (pushPart run p) := by
  intro i q hq
  rw [properPath_push] at hq
  rw [nativePathNodes_push]
  cases hd : descendKind p.kind with
  | false => simpa [hd] using hc i q (by simpa [hd] using hq)
  | true =>
    cases i with
    | zero =>
      simp only [hd,ite_true,List.singleton_append,List.getElem?_cons_zero,Option.some.injEq] at hq
      subst q
      simpa [hd,List.head?_eq_getElem?] using hl hd
    | succ i =>
      have hq' : (properPath run)[i]?=some q := by simpa [hd] using hq
      simpa [hd,Nat.add_assoc] using hc i q hq'

theorem leafSplitRun_pathChain (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    PathChain (leafSplitRun k s m key v) := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;>
    simp [PathChain,properPath,wrapRun,terminalRun,pushPart,descendKind]

theorem extSplitRun_pathChain (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    PathChain (extSplitRun k c m key v) := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,PathChain,properPath,terminalRun,descendKind]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [PathChain,properPath,terminalRun,wrapRun,pushPart,descendKind]

theorem traceKids_pathHead (source : PTrie) (wholeKey : List Nat) (cs : Kids)
    (n : Nat) (key : List Nat) (v : Bytes) (run : KidsRun)
    (hr : traceKids source wholeKey cs n key v=some run) (hi : run.inserted=false) :
    (nativePathNodes run.inner).head?=(nativeChildAt cs n).map resolveNative := by
  cases cs with
  | nil => simp [traceKids] at hr
  | none rest =>
    cases n with
    | zero => simp only [traceKids,Option.some.injEq] at hr; subst run; cases hi
    | succ n =>
      cases hc : traceKids source wholeKey rest n key v with
      | none => simp [traceKids,hc] at hr
      | some inner =>
        simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
        subst run
        exact traceKids_pathHead source wholeKey rest n key v inner hc hi
  | some child rest =>
    cases n with
    | zero =>
      cases hm : child.mem? with
      | none => simp [traceKids,hm] at hr
      | some cm =>
        cases hc : traceUpsert child key v with
        | none => simp [traceKids,hm,hc] at hr
        | some inner =>
          simp only [traceKids,hm,hc,Option.some.injEq] at hr
          subst run
          exact traceUpsert_pathHead child key v inner hc
    | succ n =>
      cases hc : traceKids source wholeKey rest n key v with
      | none => simp [traceKids,hc] at hr
      | some inner =>
        simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
        subst run
        exact traceKids_pathHead source wholeKey rest n key v inner hc hi
termination_by cs

mutual
/-- Adjacent proper source levels are exactly related by resolved native child descent. -/
theorem traceUpsert_pathChain : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → PathChain run
  | .hash _, _, _, _, hr => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run; simp [PathChain,properPath,terminalRun,descendKind]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run; exact leafSplitRun_pathChain k s m key v
  | .ext k c m, key, v, run, hr => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run; exact extSplitRun_pathChain k c m key v
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hc] at hr
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          apply pathChain_push (traceUpsert_pathChain c _ v inner hc)
          intro _
          exact (traceUpsert_pathHead c _ v inner hc).symm
  | .branch bv cs m, [], v, run, hr => by
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run
    cases bv <;> simp [PathChain,properPath,terminalRun,descendKind]
  | .branch bv cs m, n::key, v, run, hr => by
    cases hc : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hc] at hr
    | some inner =>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      apply pathChain_push (traceKids_pathChain (.branch bv cs m) (n::key) cs n key v inner hc)
      intro hd
      cases hi : inner.inserted with
      | true => simp [hi,descendKind] at hd
      | false => exact (traceKids_pathHead (.branch bv cs m) (n::key) cs n key v inner hc hi).symm

theorem traceKids_pathChain : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), traceKids source wholeKey cs n key v=some run →
    PathChain run.inner
  | _, _, .nil, _, _, _, _, hr => by simp [traceKids] at hr
  | source, wholeKey, .none rest, 0, key, v, run, hr => by
    simp only [traceKids,Option.some.injEq] at hr
    subst run; simp [PathChain,properPath,terminalRun,descendKind]
  | source, wholeKey, .some child rest, 0, key, v, run, hr => by
    cases hm : child.mem? with
    | none => simp [traceKids,hm] at hr
    | some cm =>
      cases hc : traceUpsert child key v with
      | none => simp [traceKids,hm,hc] at hr
      | some inner =>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        exact traceUpsert_pathChain child key v inner hc
  | source, wholeKey, .none rest, n+1, key, v, run, hr => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_pathChain source wholeKey rest n key v inner hc
  | source, wholeKey, .some child rest, n+1, key, v, run, hr => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_pathChain source wholeKey rest n key v inner hc
end
end ZkFormal.NearV3.Render.UpsGen
