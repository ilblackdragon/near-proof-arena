import ZkFormal.NearV3.Render.Ups.NativeTerminalPrefixEdge

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- An existing branch descent reaches an actual revealed native child. -/
theorem traceKids_child_revealed (source : PTrie) (wholeKey : List Nat) (cs : Kids)
    (n : Nat) (key : List Nat) (v : Bytes) (run : KidsRun)
    (hr : traceKids source wholeKey cs n key v=some run) (hi : run.inserted=false) :
    ∃ child cm,nativeChildAt cs n=some child ∧ child.mem?=some cm := by
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
        exact traceKids_child_revealed source wholeKey rest n key v inner hc hi
  | some child rest =>
    cases n with
    | zero =>
      cases hm : child.mem? with
      | none => simp [traceKids,hm] at hr
      | some cm => exact ⟨child,cm,rfl,hm⟩
    | succ n =>
      cases hc : traceKids source wholeKey rest n key v with
      | none => simp [traceKids,hc] at hr
      | some inner =>
        simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
        subst run
        exact traceKids_child_revealed source wholeKey rest n key v inner hc hi
termination_by cs

/-- Ordinary source geometry of a proper native ancestor. -/
def ProperSource (part : TreePart) : Prop :=
  match part.kind with
  | .RDB => ∃ value kids mem child cm,part.source=.branch value kids mem ∧
      nativeChildAt kids part.slot=some child ∧ child.mem?=some cm
  | .RDE => ∃ key child mem cm,part.source=.ext key child mem ∧ key≠[] ∧ child.mem?=some cm
  | _ => True

def TreeRun.ProperSources (run : TreeRun) : Prop := ∀ p∈run.parts,ProperSource p

theorem properSources_push {run : TreeRun} (h : run.ProperSources) (p : TreePart)
    (hp : ProperSource p) : (pushPart run p).ProperSources := by
  intro q hq
  simp only [pushPart,List.mem_append,List.mem_singleton] at hq
  rcases hq with hq|rfl
  exact h q hq
  exact hp

theorem leafSplitRun_properSources (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    (leafSplitRun k s m key v).ProperSources := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;>
    simp [TreeRun.ProperSources,ProperSource,wrapRun,terminalRun,pushPart]

theorem extSplitRun_properSources (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    (extSplitRun k c m key v).ProperSources := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,TreeRun.ProperSources,ProperSource,terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [TreeRun.ProperSources,ProperSource,terminalRun,wrapRun,pushPart]

mutual
/-- Proper ancestor source shapes and revealed-child facts follow from actual execution. -/
theorem traceUpsert_properSources : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → run.ProperSources
  | .hash _, _, _, _, hr => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run; simp [TreeRun.ProperSources,ProperSource,terminalRun]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run; exact leafSplitRun_properSources k s m key v
  | .ext k c m, key, v, run, hr => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run; exact extSplitRun_properSources k c m key v
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hc] at hr
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          apply properSources_push (traceUpsert_properSources c _ v inner hc)
          cases k with
          | nil => trivial
          | cons x xs => exact ⟨x::xs,c,m,cm,rfl,by simp,hm⟩
  | .branch bv cs m, [], v, run, hr => by
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run
    cases bv <;> simp [TreeRun.ProperSources,ProperSource,terminalRun]
  | .branch bv cs m, n::key, v, run, hr => by
    cases hc : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hc] at hr
    | some inner =>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      apply properSources_push (traceKids_properSources (.branch bv cs m) (n::key) cs n key v inner hc)
      cases hi : inner.inserted with
      | true => simp [hi,ProperSource]
      | false =>
        obtain ⟨child,cm,hchild,hmem⟩ := traceKids_child_revealed (.branch bv cs m) (n::key) cs n key v inner hc hi
        simp only [hi,Bool.false_eq_true,ite_false,ProperSource]
        exact ⟨bv,cs,m,child,cm,rfl,hchild,hmem⟩

theorem traceKids_properSources : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), traceKids source wholeKey cs n key v=some run →
    run.inner.ProperSources
  | _, _, .nil, _, _, _, _, hr => by simp [traceKids] at hr
  | source, wholeKey, .none rest, 0, key, v, run, hr => by
    simp only [traceKids,Option.some.injEq] at hr
    subst run; simp [TreeRun.ProperSources,ProperSource,terminalRun]
  | source, wholeKey, .some child rest, 0, key, v, run, hr => by
    cases hm : child.mem? with
    | none => simp [traceKids,hm] at hr
    | some cm =>
      cases hc : traceUpsert child key v with
      | none => simp [traceKids,hm,hc] at hr
      | some inner =>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        exact traceUpsert_properSources child key v inner hc
  | source, wholeKey, .none rest, n+1, key, v, run, hr => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_properSources source wholeKey rest n key v inner hc
  | source, wholeKey, .some child rest, n+1, key, v, run, hr => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_properSources source wholeKey rest n key v inner hc
end
end ZkFormal.NearV3.Render.UpsGen
