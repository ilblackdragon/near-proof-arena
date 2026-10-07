import ZkFormal.NearV3.Render.Ups.TreeTrace

/-! Every source node emitted by the executable trace inherits runtime trie
well-formedness from the input. No per-part source-wf assumption is needed. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows UpsSpec

def TreeRun.SourcesWf (run : TreeRun) : Prop :=
  run.terminalSource.wf=true ∧ ∀ part∈run.parts,part.source.wf=true

theorem sources_push {run : TreeRun} (h : run.SourcesWf) (part : TreePart)
    (hs : part.source.wf=true) : (pushPart run part).SourcesWf := by
  refine ⟨h.1,?_⟩
  intro p hp
  simp only [pushPart,List.mem_append,List.mem_singleton] at hp
  rcases hp with hp|rfl
  exact h.2 p hp
  exact hs

theorem leafSplitRun_sources (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes)
    (hs : (PTrie.leaf k s m).wf=true) : (leafSplitRun k s m key v).SourcesWf := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;>
    simp [TreeRun.SourcesWf,terminalRun,wrapRun,pushPart,hs]

theorem extSplitRun_sources (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes)
    (hs : (PTrie.ext k c m).wf=true) : (extSplitRun k c m key v).SourcesWf := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,TreeRun.SourcesWf,terminalRun,hs]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [TreeRun.SourcesWf,terminalRun,wrapRun,pushPart,hs]

mutual
theorem traceUpsert_sources : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    t.wf=true → traceUpsert t key v=some run → run.SourcesWf
  | .hash _, _, _, _, _, h => by simp [traceUpsert] at h
  | .leaf k s m, key, v, run, hw, h => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run; simpa [TreeRun.SourcesWf,terminalRun,he] using hw
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run; exact leafSplitRun_sources k s m key v hw
  | .ext k c m, key, v, run, hw, h => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run; exact extSplitRun_sources k c m key v hw
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at h
      | some cm =>
        cases hr : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hr] at h
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst run
          have hc : c.wf=true := by
            simp only [PTrie.wf,Bool.and_eq_true] at hw
            exact hw.1.1.2
          exact sources_push (traceUpsert_sources c (key.drop k.length) v inner hc hr) _ hw
  | .branch bv cs m, [], v, run, hw, h => by
    simp only [traceUpsert,Option.some.injEq] at h
    subst run; simpa [TreeRun.SourcesWf,terminalRun] using hw
  | .branch bv cs m, n::key, v, run, hw, h => by
    cases hr : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hr] at h
    | some inner =>
      simp only [traceUpsert,hr,Option.map_some,Option.some.injEq] at h
      subst run
      have hc : Kids.wf cs 16=true := by
        simp only [PTrie.wf,Bool.and_eq_true] at hw
        exact hw.1.2
      exact sources_push (traceKids_sources (.branch bv cs m) (n::key) cs 16 n key v inner hw hc hr) _ hw
theorem traceKids_sources : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (width n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), source.wf=true → Kids.wf cs width=true →
    traceKids source wholeKey cs n key v=some run → run.inner.SourcesWf
  | _, _, .nil, _, _, _, _, _, _, _, h => by simp [traceKids] at h
  | source, wholeKey, .none rest, width, 0, key, v, run, hs, _, h => by
    simp only [traceKids,Option.some.injEq] at h
    subst run; simpa [TreeRun.SourcesWf,terminalRun] using hs
  | source, wholeKey, .some c rest, width, 0, key, v, run, hs, hw, h => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        simp only [Kids.wf,Bool.and_eq_true] at hw
        exact traceUpsert_sources c key v inner hw.1.2 hr
  | source, wholeKey, .none rest, width, n+1, key, v, run, hs, hw, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      simp only [Kids.wf,Bool.and_eq_true] at hw
      exact traceKids_sources source wholeKey rest (width-1) n key v inner hs hw.2 hr
  | source, wholeKey, .some c rest, width, n+1, key, v, run, hs, hw, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      simp only [Kids.wf,Bool.and_eq_true] at hw
      exact traceKids_sources source wholeKey rest (width-1) n key v inner hs hw.2 hr
end

end ZkFormal.NearV3.Render.UpsGen
