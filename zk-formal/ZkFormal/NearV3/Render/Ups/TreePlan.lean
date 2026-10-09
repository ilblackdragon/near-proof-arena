import ZkFormal.NearV3.Render.Ups.TreeTraceCorrect
import NearSpec.TrieUpsertProofs

/-! The actual runtime emits the terminal case plan followed only by ancestor parts.
The statement has no cap, polynomial, or witness-plan assumption. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows UpsSpec

def TreeRun.Planned (run : TreeRun) : Prop :=
  ∃ upper : List UKind, run.parts.map TreePart.kind = termPlan run.terminal run.matched ++ upper ∧
    ∀ k ∈ upper, k.upper = true

theorem planned_of_terminal {run : TreeRun}
    (h : run.parts.map TreePart.kind = termPlan run.terminal run.matched) : run.Planned :=
  ⟨[],by simpa using h,by simp⟩

theorem planned_push {run : TreeRun} (h : run.Planned) (part : TreePart)
    (hu : part.kind.upper=true) : (pushPart run part).Planned := by
  obtain ⟨upper,he,huppers⟩ := h
  refine ⟨upper++[part.kind],?_,?_⟩
  · simpa [pushPart,List.map_append,List.append_assoc] using congrArg (· ++ [part.kind]) he
  · intro k hk
    simp only [List.mem_append,List.mem_singleton] at hk
    rcases hk with hk|rfl
    exact huppers k hk
    exact hu

theorem leafSplitRun_plan (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    (leafSplitRun k s m key v).parts.map TreePart.kind =
      termPlan (leafSplitRun k s m key v).terminal (leafSplitRun k s m key v).matched := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;>
    simp [terminalRun,wrapRun,pushPart,termPlan,UCase.split]

theorem extSplitRun_plan (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes)
    (hp : isPrefix k key=false) :
    (extSplitRun k c m key v).parts.map TreePart.kind =
      termPlan (extSplitRun k c m key v).terminal (extSplitRun k c m key v).matched := by
  have hn : k.drop (commonPrefix k key).length ≠ [] := by
    intro h
    have hl := commonPrefix_left k key
    rw [h,List.append_nil] at hl
    have hr := commonPrefix_right k key
    rw [←hl] at hr
    have ht := (isPrefix_iff k key).mpr ⟨_,hr⟩
    simp [hp] at ht
  unfold extSplitRun
  cases h1 : k.drop (commonPrefix k key).length with
  | nil => exact False.elim (hn h1)
  | cons x xs =>
    cases h2 : key.drop (commonPrefix k key).length <;> simp only [h1,h2] <;> cases xs <;>
      cases commonPrefix k key <;>
      simp [terminalRun,wrapRun,pushPart,termPlan,UCase.split]

/-- Insertion into a missing child has one pending RBI parent part. Otherwise the
recursive child has already emitted a complete terminal plan. -/
def KidsRun.Planned (run : KidsRun) : Prop :=
  if run.inserted then run.inner.terminal=.BI ∧ run.inner.matched=0 ∧
    run.inner.parts.map TreePart.kind=[.NLF]
  else run.inner.Planned

theorem kidsPlan_close {run : KidsRun} (h : run.Planned) (source output : PTrie) (slot : Nat) :
    (pushPart run.inner ⟨if run.inserted then .RBI else .RDB,source,output,slot⟩).Planned := by
  cases hb : run.inserted with
  | false =>
    simp only [KidsRun.Planned,hb,Bool.false_eq_true,ite_false] at h
    exact planned_push h _ (by simp [hb,UKind.upper])
  | true =>
    simp only [KidsRun.Planned,hb,ite_true] at h
    apply planned_of_terminal
    simp [pushPart,hb,h.1,h.2.1,h.2.2,termPlan,UCase.split]

mutual
/-- Every successful executable trace has the AIR's terminal/ancestor kind plan. -/
theorem traceUpsert_plan : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → run.Planned
  | .hash _, _, _, _, h => by simp [traceUpsert] at h
  | .leaf k s m, key, v, run, h => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run
      apply planned_of_terminal
      simp [terminalRun,termPlan,UCase.split]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run
      exact planned_of_terminal (leafSplitRun_plan k s m key v)
  | .ext k c m, key, v, run, h => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run
      exact planned_of_terminal (extSplitRun_plan k c m key v hp)
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at h
      | some cm =>
        cases hr : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hr] at h
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst run
          apply planned_push (traceUpsert_plan c (key.drop k.length) v inner hr)
          cases k <;> rfl
  | .branch bv cs m, [], v, run, h => by
    cases bv <;> simp only [traceUpsert,Option.isSome_none,Option.isSome_some,
      Bool.false_eq_true,ite_false,ite_true,Option.some.injEq] at h <;> subst run <;>
      apply planned_of_terminal <;> simp [terminalRun,termPlan,UCase.split]
  | .branch bv cs m, n::key, v, run, h => by
    cases hr : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hr] at h
    | some inner =>
      simp only [traceUpsert,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact kidsPlan_close (traceKids_plan (.branch bv cs m) (n::key) cs n key v inner hr) _ _ _
theorem traceKids_plan : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids) (n : Nat)
    (key : List Nat) (v : Bytes) (run : KidsRun), traceKids source wholeKey cs n key v=some run → run.Planned
  | _, _, .nil, _, _, _, _, h => by simp [traceKids] at h
  | source, wholeKey, .none rest, 0, key, v, run, h => by
    simp only [traceKids,Option.some.injEq] at h
    subst run
    simp [KidsRun.Planned,terminalRun]
  | source, wholeKey, .some c rest, 0, key, v, run, h => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key v with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        exact traceUpsert_plan c key v inner hr
  | source, wholeKey, .none rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_plan source wholeKey rest n key v inner hr
  | source, wholeKey, .some c rest, n+1, key, v, run, h => by
    cases hr : traceKids source wholeKey rest n key v with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_plan source wholeKey rest n key v inner hr
end

/-- Runtime success supplies both the exact output and the derived kind plan. -/
theorem upsert_planned_witness {t result : PTrie} {key : List Nat} {v : Bytes}
    (h : t.upsert key v=some result) :
    ∃ run,traceUpsert t key v=some run ∧ run.output=result ∧ run.Planned := by
  obtain ⟨run,hr,ho⟩ := traceUpsert_complete h
  exact ⟨run,hr,ho,traceUpsert_plan t key v run hr⟩

end ZkFormal.NearV3.Render.UpsGen
