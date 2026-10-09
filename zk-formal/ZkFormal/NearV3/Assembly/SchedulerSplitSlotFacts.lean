import ZkFormal.NearV3.Assembly.SchedulerSplitSlots
import ZkFormal.NearV3.Render.Ups.SplitInstance

namespace ZkFormal.NearV3.Assembly
open NearSpec UpsRows Render.UpsGen

def SplitSlotFacts (run : TreeRun) : Prop :=
  (run.terminal=.LSa ∨ run.terminal=.LSc ∨ run.terminal=.ESn0 ∨ run.terminal=.ESn1 →
    run.terminalKey.drop run.matched≠[]) ∧
  (run.terminal=.LSc ∨ run.terminal=.ESn0 ∨ run.terminal=.ESn1 →
    splitOldSlot run≠splitNewSlotNative run)

private theorem push_facts {run : TreeRun} (h : SplitSlotFacts run) (p : TreePart) :
    SplitSlotFacts (pushPart run p) := h

private theorem wrap_facts {run : TreeRun} (h : SplitSlotFacts run) (src : PTrie) (key : List Nat) :
    SplitSlotFacts (wrapRun src key run) := by cases key <;> exact h

private theorem leaf_facts (key : List Nat) (s : Slot) (m : Nat) (target : List Nat) (v : Bytes) :
    SplitSlotFacts (leafSplitRun key s m target v) := by
  have hdiv : ∀x xs y ys,key.drop (commonPrefix key target).length=x::xs →
      target.drop (commonPrefix key target).length=y::ys → x≠y := by
    intro x xs y ys hx hy
    exact commonPrefix_diverge key target hx hy
  unfold leafSplitRun
  generalize commonPrefix key target=p at *
  cases h1:key.drop p.length <;> cases h2:target.drop p.length <;> simp only [h1,h2]
  all_goals try apply wrap_facts
  all_goals simp [SplitSlotFacts,terminalRun,splitOldSlot,splitNewSlotNative,nativeKey,h1,h2]
  all_goals exact hdiv _ _ _ _ h1 h2

private theorem ext_facts (key : List Nat) (c : PTrie) (m : Nat) (target : List Nat) (v : Bytes) :
    SplitSlotFacts (extSplitRun key c m target v) := by
  have hdiv : ∀x xs y ys,key.drop (commonPrefix key target).length=x::xs →
      target.drop (commonPrefix key target).length=y::ys → x≠y := by
    intro x xs y ys hx hy
    exact commonPrefix_diverge key target hx hy
  unfold extSplitRun
  generalize commonPrefix key target=p at *
  cases h1:key.drop p.length with
  | nil=>simp [h1,SplitSlotFacts,terminalRun]
  | cons x xs=>
    cases h2:target.drop p.length <;> cases xs <;> simp only [h1,h2,List.isEmpty_nil,List.isEmpty_cons,Bool.false_eq_true,ite_false,ite_true]
    all_goals apply wrap_facts
    all_goals simp [SplitSlotFacts,terminalRun,splitOldSlot,splitNewSlotNative,nativeKey,h1,h2]
    all_goals exact hdiv _ _ _ _ h1 h2
mutual
/-- Every native fresh-value part embeds the actual inserted value, including
all leaf/extension splits and branch insertion cases. -/
theorem traceUpsert_split_slot_facts : ∀(root : PTrie)(key : List Nat)(v : Bytes)(run : TreeRun),
    traceUpsert root key v=some run→SplitSlotFacts run
  | .hash h,key,v,run,hr=>by simp [traceUpsert] at hr
  | .leaf old s mem,key,v,run,hr=>by
    by_cases he:old=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run
      simp [SplitSlotFacts,terminalRun,newLeaf]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run
      exact leaf_facts old s mem key v
  | .ext old c mem,key,v,run,hr=>by
    cases hp:isPrefix old key with
    | false=>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run
      exact ext_facts old c mem key v
    | true=>
      cases hm:c.mem? with
      | none=>simp [traceUpsert,hp,hm] at hr
      | some cm=>
        cases hc:traceUpsert c (key.drop old.length) v with
        | none=>simp [traceUpsert,hp,hm,hc] at hr
        | some inner=>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          exact push_facts (traceUpsert_split_slot_facts c _ v inner hc) _

  | .branch sv kids mem,[],v,run,hr=>by
    cases sv <;> simp only [traceUpsert,Option.isSome_none,Option.isSome_some,Bool.false_eq_true,
      ite_false,ite_true,Option.some.injEq] at hr <;> subst run <;>
      simp [SplitSlotFacts,terminalRun]
  | .branch sv kids mem,n::key,v,run,hr=>by
    cases hc:traceKids (.branch sv kids mem) (n::key) kids n key v with
    | none=>simp [traceUpsert,hc] at hr
    | some kr=>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact push_facts (traceKids_split_slot_facts _ _ kids n key v kr hc) _


theorem traceKids_split_slot_facts : ∀(source : PTrie)(whole : List Nat)(kids : Kids)(n : Nat)
    (key : List Nat)(v : Bytes)(run : KidsRun),
    traceKids source whole kids n key v=some run→SplitSlotFacts run.inner
  | source,whole,.nil,n,key,v,run,hr=>by simp [traceKids] at hr
  | source,whole,.none rest,0,key,v,run,hr=>by
    simp only [traceKids,Option.some.injEq] at hr
    subst run
    simp [SplitSlotFacts,terminalRun,newLeaf]
  | source,whole,.some c rest,0,key,v,run,hr=>by
    cases hm:c.mem? with
    | none=>simp [traceKids,hm] at hr
    | some cm=>
      cases hc:traceUpsert c key v with
      | none=>simp [traceKids,hm,hc] at hr
      | some inner=>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        exact traceUpsert_split_slot_facts c key v inner hc
  | source,whole,.none rest,n+1,key,v,run,hr=>by
    cases hc:traceKids source whole rest n key v with
    | none=>simp [traceKids,hc] at hr
    | some inner=>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_split_slot_facts source whole rest n key v inner hc
  | source,whole,.some c rest,n+1,key,v,run,hr=>by
    cases hc:traceKids source whole rest n key v with
    | none=>simp [traceKids,hc] at hr
    | some inner=>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_split_slot_facts source whole rest n key v inner hc
end


end ZkFormal.NearV3.Assembly
