import ZkFormal.NearV3.Render.Ups.TreePrefixShapes

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- The actual existing-child recursion that produced a branch ancestor. -/
def nativeRdbContext (part : TreePart) : Prop :=
  part.kind=.RDB → ∃ value kids mem key v inner,
    part.source=.branch value kids mem ∧
    part.output=.branch value inner.output (mem+inner.newMem-inner.oldMem) ∧
    traceKids (.branch value kids mem) (part.slot::key) kids part.slot key v=some inner ∧
    inner.inserted=false

def TreeRun.RdbContexts (run : TreeRun) : Prop :=
  ∀ part∈run.parts,nativeRdbContext part

theorem rdbContexts_push {run : TreeRun} (h : run.RdbContexts) (part : TreePart)
    (hp : nativeRdbContext part) : (pushPart run part).RdbContexts := by
  intro p hm
  simp only [pushPart,List.mem_append,List.mem_singleton] at hm
  rcases hm with hm|rfl
  exact h p hm
  exact hp

theorem leafSplitRun_rdbContexts (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    (leafSplitRun k s m key v).RdbContexts := by
  have hl := congrArg List.length (commonPrefix_left k key)
  simp only [List.length_append] at hl
  unfold leafSplitRun
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,List.length_cons,List.length_nil] at hl <;>
    simp only [h1,h2] <;> cases p <;>
    simp_all [TreeRun.RdbContexts,nativeRdbContext,terminalRun,wrapRun,pushPart,wrapExt,newLeaf,nativeNodeType,nativeKey] <;>
    (repeat' (apply And.intro)) <;> omega

theorem extSplitRun_rdbContexts (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    (extSplitRun k c m key v).RdbContexts := by
  have hl := congrArg List.length (commonPrefix_left k key)
  simp only [List.length_append] at hl
  unfold extSplitRun
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length with
  | nil => simp [h1,TreeRun.RdbContexts,terminalRun]
  | cons x xs =>
    simp only [h1,List.length_cons] at hl
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp_all [TreeRun.RdbContexts,nativeRdbContext,terminalRun,wrapRun,pushPart,wrapExt,newLeaf,nativeNodeType,nativeKey] <;>
      (repeat' (apply And.intro)) <;> omega

mutual
/-- Actual runtime key and value relationships are preserved through ancestor propagation. -/
theorem traceUpsert_rdbContexts : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → run.RdbContexts
  | .hash _, _, _, _, h => by simp [traceUpsert] at h
  | .leaf k s m, key, v, run, h => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run; simp [TreeRun.RdbContexts,terminalRun,nativeRdbContext,nativeKey,nativeNodeType,newLeaf]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run; exact leafSplitRun_rdbContexts k s m key v
  | .ext k c m, key, v, run, h => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run; exact extSplitRun_rdbContexts k c m key v
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at h
      | some cm =>
        cases hr : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hr] at h
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst run
          apply rdbContexts_push (traceUpsert_rdbContexts c _ v inner hr)
          cases k <;> simp [nativeRdbContext]
  | .branch bv cs m, [], v, run, h => by
    simp only [traceUpsert,Option.some.injEq] at h
    subst run
    cases bv <;> simp [TreeRun.RdbContexts,terminalRun,nativeNodeType,nativeRdbContext,nativeKey]
  | .branch bv cs m, n::key, v, run, h => by
    cases hr : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hr] at h
    | some inner =>
      simp only [traceUpsert,hr,Option.map_some,Option.some.injEq] at h
      subst run
      apply rdbContexts_push (traceKids_rdbContexts _ _ cs n key v inner hr)
      intro hk
      cases hi : inner.inserted with
      | true => simp [hi] at hk
      | false => exact ⟨bv,cs,m,key,v,inner,rfl,rfl,hr,hi⟩

theorem traceKids_rdbContexts : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v=some run → run.inner.RdbContexts
  | _, _, .nil, _, _, _, _, h => by simp [traceKids] at h
  | source, wholeKey, .none rest, 0, key, v, run, h => by
    simp only [traceKids,Option.some.injEq] at h
    subst run; simp [TreeRun.RdbContexts,terminalRun,nativeNodeType,nativeRdbContext,nativeKey,newLeaf]
  | source, wholeKey, .some c rest, 0, key, v, run, h => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        exact traceUpsert_rdbContexts c key v inner hr
  | source, wholeKey, .none rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_rdbContexts source wholeKey rest n key v inner hr
  | source, wholeKey, .some c rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_rdbContexts source wholeKey rest n key v inner hr
end
end ZkFormal.NearV3.Render.UpsGen
