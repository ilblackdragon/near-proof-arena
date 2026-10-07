import ZkFormal.NearV3.Render.Ups.TreeValueTerminal

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Absent-key terminals point to an actual source key symbol or the leaf end. -/
def KeyTerminal (run : TreeRun) : Prop :=
  match run.terminal with
  | .LSa => ∃ key slot mem,run.terminalSource=.leaf key slot mem ∧ run.matched=key.length
  | .LSb | .LSc => ∃ key slot mem,run.terminalSource=.leaf key slot mem ∧ run.matched<key.length
  | .ESl0 | .ESl1 | .ESn0 | .ESn1 =>
    ∃ key child mem,run.terminalSource=.ext key child mem ∧ run.matched<key.length
  | _ => True

theorem leafSplitRun_keyTerminal (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    KeyTerminal (leafSplitRun k s m key v) := by
  have hl := congrArg List.length (commonPrefix_left k key)
  simp only [List.length_append] at hl
  unfold leafSplitRun
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;> simp only [h1,h2]
  all_goals simp only [h1,List.length_cons,List.length_nil] at hl
  all_goals cases p <;> simp [KeyTerminal,terminalRun,wrapRun,pushPart] <;> simp only [List.length_cons,List.length_nil] at hl <;> omega

theorem extSplitRun_keyTerminal (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes)
    (hprefix : isPrefix k key=false) : KeyTerminal (extSplitRun k c m key v) := by
  have hnon : k.drop (commonPrefix k key).length≠[] := by
    intro h
    have ho := commonPrefix_left k key
    rw [h,List.append_nil] at ho
    have hp := commonPrefix_right k key
    have hpre := (isPrefix_iff k key).mpr ⟨_,by simpa only [←ho] using hp⟩
    simp [hprefix] at hpre
  have hl := congrArg List.length (commonPrefix_left k key)
  simp only [List.length_append] at hl
  unfold extSplitRun
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length with
  | nil => exact (hnon h1).elim
  | cons x xs =>
    simp only [h1,List.length_cons] at hl
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [KeyTerminal,terminalRun,wrapRun,pushPart] <;>
      simp only [List.length_cons,List.length_nil] at hl <;> omega

mutual
/-- Native absent-key cases retain their actual source-key position. -/
theorem traceUpsert_keyTerminal : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → KeyTerminal run
  | .hash _, _, _, _, hr => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run
      trivial
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run; exact leafSplitRun_keyTerminal k s m key v
  | .ext k c m, key, v, run, hr => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run; exact extSplitRun_keyTerminal k c m key v hp
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hc] at hr
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          exact traceUpsert_keyTerminal c _ v inner hc
  | .branch bv cs m, [], v, run, hr => by
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run
    cases bv <;> trivial
  | .branch bv cs m, n::key, v, run, hr => by
    cases hc : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hc] at hr
    | some inner =>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_keyTerminal (.branch bv cs m) (n::key) cs n key v inner hc

theorem traceKids_keyTerminal : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), traceKids source wholeKey cs n key v=some run →
    KeyTerminal run.inner
  | _, _, .nil, _, _, _, _, hr => by simp [traceKids] at hr
  | source, wholeKey, .none rest, 0, key, v, run, hr => by
    simp only [traceKids,Option.some.injEq] at hr
    subst run; simp [KeyTerminal,terminalRun]
  | source, wholeKey, .some child rest, 0, key, v, run, hr => by
    cases hm : child.mem? with
    | none => simp [traceKids,hm] at hr
    | some cm =>
      cases hc : traceUpsert child key v with
      | none => simp [traceKids,hm,hc] at hr
      | some inner =>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        exact traceUpsert_keyTerminal child key v inner hc
  | source, wholeKey, .none rest, n+1, key, v, run, hr => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_keyTerminal source wholeKey rest n key v inner hc
  | source, wholeKey, .some child rest, n+1, key, v, run, hr => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_keyTerminal source wholeKey rest n key v inner hc
end
end ZkFormal.NearV3.Render.UpsGen
