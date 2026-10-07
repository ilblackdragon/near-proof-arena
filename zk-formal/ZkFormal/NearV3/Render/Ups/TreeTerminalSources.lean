import ZkFormal.NearV3.Render.Ups.SourceLevelAllocation
import ZkFormal.NearV3.Render.Ups.TreeInsertTrace

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

def TreeRun.TerminalSources (run : TreeRun) : Prop :=
  ∀ part∈run.parts.take (termPlan run.terminal run.matched).length,part.source=run.terminalSource

theorem terminalSources_push {run : TreeRun} (hs : run.TerminalSources) (hp : run.Planned)
    (part : TreePart) : (pushPart run part).TerminalSources := by
  obtain ⟨upper,he,_⟩ := hp
  have hl := congrArg List.length he
  simp only [List.length_map,List.length_append] at hl
  simpa only [TreeRun.TerminalSources,pushPart,List.take_append_of_le_length (by omega :
    (termPlan run.terminal run.matched).length≤run.parts.length)] using hs

theorem leafSplitRun_terminalSources (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    (leafSplitRun k s m key v).TerminalSources := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;>
    simp [TreeRun.TerminalSources,terminalRun,wrapRun,pushPart,termPlan,UCase.split]

theorem extSplitRun_terminalSources (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    (extSplitRun k c m key v).TerminalSources := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,TreeRun.TerminalSources,terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [TreeRun.TerminalSources,terminalRun,wrapRun,pushPart,termPlan,UCase.split]

mutual
/-- All terminal parts read the same actual native source node. -/
theorem traceUpsert_terminalSources : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → run.TerminalSources
  | .hash _, _, _, _, h => by simp [traceUpsert] at h
  | .leaf k s m, key, v, run, h => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run; simp [TreeRun.TerminalSources,terminalRun,termPlan,UCase.split]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run; exact leafSplitRun_terminalSources k s m key v
  | .ext k c m, key, v, run, h => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run; exact extSplitRun_terminalSources k c m key v
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at h
      | some cm =>
        cases hr : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hr] at h
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst run
          exact terminalSources_push (traceUpsert_terminalSources c _ v inner hr)
            (traceUpsert_plan c _ v inner hr) _
  | .branch bv cs m, [], v, run, h => by
    simp only [traceUpsert,Option.some.injEq] at h
    subst run
    cases bv <;> simp [TreeRun.TerminalSources,terminalRun,termPlan,UCase.split]
  | .branch bv cs m, n::key, v, run, h => by
    cases hr : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hr] at h
    | some inner =>
      simp only [traceUpsert,hr,Option.map_some,Option.some.injEq] at h
      subst run
      cases hi : inner.inserted with
      | false =>
        have hp := traceKids_plan (.branch bv cs m) (n::key) cs n key v inner hr
        simp only [KidsRun.Planned,hi,Bool.false_eq_true,ite_false] at hp
        exact terminalSources_push (traceKids_terminalSources _ _ cs n key v inner hr) hp _
      | true =>
        have he := (traceKids_inserted (.branch bv cs m) (n::key) cs n key v inner hr hi).2.2
        simp [he,hi,TreeRun.TerminalSources,pushPart,terminalRun,termPlan,UCase.split]

theorem traceKids_terminalSources : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v=some run → run.inner.TerminalSources
  | _, _, .nil, _, _, _, _, h => by simp [traceKids] at h
  | source, wholeKey, .none rest, 0, key, v, run, h => by
    simp only [traceKids,Option.some.injEq] at h
    subst run; simp [TreeRun.TerminalSources,terminalRun,termPlan,UCase.split]
  | source, wholeKey, .some c rest, 0, key, v, run, h => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        exact traceUpsert_terminalSources c key v inner hr
  | source, wholeKey, .none rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_terminalSources source wholeKey rest n key v inner hr
  | source, wholeKey, .some c rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_terminalSources source wholeKey rest n key v inner hr
end
end ZkFormal.NearV3.Render.UpsGen
