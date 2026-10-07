import ZkFormal.NearV3.Render.Ups.TreeBranchTerminal

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Present-value terminals expose ordinary revealed native slots and their cursor. -/
def ValueTerminal (run : TreeRun) : Prop :=
  (run.terminal=.LP → ∃ key bytes mem,run.terminalSource=.leaf key (.val bytes) mem ∧
    run.matched=key.length) ∧
  (run.terminal=.BR → ∃ bytes kids mem,run.terminalSource=.branch (some (.val bytes)) kids mem ∧
    run.matched=0)

theorem leafSplitRun_valueTerminal (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes)
    (hne : k≠key) : ValueTerminal (leafSplitRun k s m key v) := by
  have hleft := commonPrefix_left k key
  have hright := commonPrefix_right k key
  unfold leafSplitRun
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;> simp only [h1,h2]
  · simp only [h1,h2,List.append_nil] at hleft hright
    exact (hne (hleft.trans hright.symm)).elim
  all_goals cases p <;> simp [ValueTerminal,terminalRun,wrapRun,pushPart]

theorem extSplitRun_valueTerminal (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    ValueTerminal (extSplitRun k c m key v) := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,ValueTerminal,terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [ValueTerminal,terminalRun,wrapRun,pushPart]

mutual
/-- A determinate native read guarantees that LP/BR source values are revealed.
The read premise is ordinary runtime semantics, not an edge or AIR assumption. -/
theorem traceUpsert_valueTerminal : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → t.find key≠none → ValueTerminal run
  | .hash _, _, _, _, hr, _ => by simp [traceUpsert] at hr
  | .leaf k s m, key, v, run, hr, hfind => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run
      cases s with
      | ref len hash => simp [PTrie.find,he,Slot.get] at hfind
      | val bytes => simp [ValueTerminal,terminalRun]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run; exact leafSplitRun_valueTerminal k s m key v he
  | .ext k c m, key, v, run, hr, hfind => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run; exact extSplitRun_valueTerminal k c m key v
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hc] at hr
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          exact traceUpsert_valueTerminal c _ v inner hc (by simpa [PTrie.find,hp] using hfind)
  | .branch bv cs m, [], v, run, hr, hfind => by
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run
    cases bv with
    | none => simp [ValueTerminal,terminalRun]
    | some slot =>
      cases slot with
      | ref len hash => simp [PTrie.find,Slot.get] at hfind
      | val bytes => simp [ValueTerminal,terminalRun]
  | .branch bv cs m, n::key, v, run, hr, hfind => by
    cases hc : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hc] at hr
    | some inner =>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_valueTerminal (.branch bv cs m) (n::key) cs n key v inner hc hfind

theorem traceKids_valueTerminal : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), traceKids source wholeKey cs n key v=some run →
    cs.find n key≠none → ValueTerminal run.inner
  | _, _, .nil, _, _, _, _, hr, _ => by simp [traceKids] at hr
  | source, wholeKey, .none rest, 0, key, v, run, hr, _ => by
    simp only [traceKids,Option.some.injEq] at hr
    subst run; simp [ValueTerminal,terminalRun]
  | source, wholeKey, .some child rest, 0, key, v, run, hr, hfind => by
    cases hm : child.mem? with
    | none => simp [traceKids,hm] at hr
    | some cm =>
      cases hc : traceUpsert child key v with
      | none => simp [traceKids,hm,hc] at hr
      | some inner =>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        exact traceUpsert_valueTerminal child key v inner hc hfind
  | source, wholeKey, .none rest, n+1, key, v, run, hr, hfind => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_valueTerminal source wholeKey rest n key v inner hc hfind
  | source, wholeKey, .some child rest, n+1, key, v, run, hr, hfind => by
    cases hc : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_valueTerminal source wholeKey rest n key v inner hc hfind
end
end ZkFormal.NearV3.Render.UpsGen
