import ZkFormal.NearV3.Assembly.NativeSerializedDigests

namespace ZkFormal.NearV3.Assembly
open NearSpec UpsRows Render.UpsGen

def freshDigestKind (cs : UCase) : UKind→Bool
  | .RLP | .RBR | .RBV | .NLF=>true
  | .SPB=>match cs with | .LSb | .ESl0 | .ESl1=>true | _=>false
  | _=>false

def outputValue : PTrie→Option Slot
  | .leaf _ s _=>some s
  | .branch s _ _=>s
  | _=>none

def FreshSlots (run : TreeRun) (value : Bytes) : Prop :=
  ∀p∈run.parts,freshDigestKind run.terminal p.kind=true→outputValue p.output=some (.val value)

private theorem fresh_push {run : TreeRun} {v : Bytes} (h : FreshSlots run v) (p : TreePart)
    (hp : freshDigestKind run.terminal p.kind=false) : FreshSlots (pushPart run p) v := by
  intro q hq hf
  simp only [pushPart,List.mem_append,List.mem_singleton] at hq
  rcases hq with hq|rfl
  · exact h q hq hf
  · simp only [pushPart,hp,Bool.false_eq_true] at hf

private theorem fresh_wrap {run : TreeRun} {v : Bytes} (h : FreshSlots run v) (src : PTrie) (key : List Nat) :
    FreshSlots (wrapRun src key run) v := by
  cases key with
  | nil=>exact h
  | cons n ns=>exact fresh_push h _ rfl

private theorem leaf_fresh (key : List Nat) (s : Slot) (m : Nat) (target : List Nat) (v : Bytes) :
    FreshSlots (leafSplitRun key s m target v) v := by
  unfold leafSplitRun
  generalize commonPrefix key target=p
  cases h1:key.drop p.length <;> cases h2:target.drop p.length <;> simp only [h1,h2]
  all_goals try apply fresh_wrap
  all_goals simp [FreshSlots,terminalRun,freshDigestKind,outputValue,newLeaf]

private theorem ext_fresh (key : List Nat) (c : PTrie) (m : Nat) (target : List Nat) (v : Bytes) :
    FreshSlots (extSplitRun key c m target v) v := by
  unfold extSplitRun
  generalize commonPrefix key target=p
  cases h1:key.drop p.length with
  | nil=>simp [h1,FreshSlots,terminalRun]
  | cons x xs=>
    cases h2:target.drop p.length <;> cases xs <;> simp only [h1,h2,List.isEmpty_nil,List.isEmpty_cons,Bool.false_eq_true,ite_false,ite_true]
    all_goals apply fresh_wrap
    all_goals simp [FreshSlots,terminalRun,freshDigestKind,outputValue,newLeaf]

mutual
/-- Every native fresh-value part embeds the actual inserted value, including
all leaf/extension splits and branch insertion cases. -/
theorem traceUpsert_fresh_slots : ∀(root : PTrie)(key : List Nat)(v : Bytes)(run : TreeRun),
    traceUpsert root key v=some run→FreshSlots run v
  | .hash h,key,v,run,hr=>by simp [traceUpsert] at hr
  | .leaf old s mem,key,v,run,hr=>by
    by_cases he:old=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run
      simp [FreshSlots,terminalRun,freshDigestKind,outputValue,newLeaf]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run
      exact leaf_fresh old s mem key v
  | .ext old c mem,key,v,run,hr=>by
    cases hp:isPrefix old key with
    | false=>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run
      exact ext_fresh old c mem key v
    | true=>
      cases hm:c.mem? with
      | none=>simp [traceUpsert,hp,hm] at hr
      | some cm=>
        cases hc:traceUpsert c (key.drop old.length) v with
        | none=>simp [traceUpsert,hp,hm,hc] at hr
        | some inner=>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          apply fresh_push (traceUpsert_fresh_slots c _ v inner hc)
          cases old <;> rfl
  | .branch sv kids mem,[],v,run,hr=>by
    cases sv <;> simp only [traceUpsert,Option.isSome_none,Option.isSome_some,Bool.false_eq_true,
      ite_false,ite_true,Option.some.injEq] at hr <;> subst run <;>
      simp [FreshSlots,terminalRun,freshDigestKind,outputValue]
  | .branch sv kids mem,n::key,v,run,hr=>by
    cases hc:traceKids (.branch sv kids mem) (n::key) kids n key v with
    | none=>simp [traceUpsert,hc] at hr
    | some kr=>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      apply fresh_push (traceKids_fresh_slots _ _ kids n key v kr hc)
      cases kr.inserted <;> rfl

theorem traceKids_fresh_slots : ∀(source : PTrie)(whole : List Nat)(kids : Kids)(n : Nat)
    (key : List Nat)(v : Bytes)(run : KidsRun),
    traceKids source whole kids n key v=some run→FreshSlots run.inner v
  | source,whole,.nil,n,key,v,run,hr=>by simp [traceKids] at hr
  | source,whole,.none rest,0,key,v,run,hr=>by
    simp only [traceKids,Option.some.injEq] at hr
    subst run
    simp [FreshSlots,terminalRun,freshDigestKind,outputValue,newLeaf]
  | source,whole,.some c rest,0,key,v,run,hr=>by
    cases hm:c.mem? with
    | none=>simp [traceKids,hm] at hr
    | some cm=>
      cases hc:traceUpsert c key v with
      | none=>simp [traceKids,hm,hc] at hr
      | some inner=>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        exact traceUpsert_fresh_slots c key v inner hc
  | source,whole,.none rest,n+1,key,v,run,hr=>by
    cases hc:traceKids source whole rest n key v with
    | none=>simp [traceKids,hc] at hr
    | some inner=>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_fresh_slots source whole rest n key v inner hc
  | source,whole,.some c rest,n+1,key,v,run,hr=>by
    cases hc:traceKids source whole rest n key v with
    | none=>simp [traceKids,hc] at hr
    | some inner=>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_fresh_slots source whole rest n key v inner hc
end

end ZkFormal.NearV3.Assembly
