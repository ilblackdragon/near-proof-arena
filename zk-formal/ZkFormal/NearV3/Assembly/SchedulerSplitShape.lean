import ZkFormal.NearV3.Render.Ups.TreeMetadata
import ZkFormal.NearV3.Render.Ups.TreePrefixShapes

namespace ZkFormal.NearV3.Assembly
open NearSpec UpsRows Render.UpsGen

def splitOldSlot (run : TreeRun) : Nat :=
  ((nativeKey run.terminalSource).drop run.matched).headD 0

def splitNewSlotNative (run : TreeRun) : Nat :=
  (run.terminalKey.drop run.matched).headD 0

def nativePartOutput (run : TreeRun) (k : Nat) : Option PTrie :=
  (run.parts[k]?).map TreePart.output

/-- Split branches retain the actual earlier output occurrences. Copied
children remain separate from outputs requiring a new digest request. -/
def SplitShape (run : TreeRun) (p : TreePart) : Prop :=
  p.kind=.SPB →
  match run.terminal with
  | .LSa => ∃s c m,p.output=.branch (some s) (kids1 (splitNewSlotNative run) c) m ∧ nativePartOutput run 0=some c
  | .LSb | .ESl0 => ∃s c m,p.output=.branch (some s) (kids1 (splitOldSlot run) c) m ∧ nativePartOutput run 0=some c
  | .LSc | .ESn0 => ∃a b m,p.output=.branch none (kids2 (splitOldSlot run) a (splitNewSlotNative run) b) m ∧
      nativePartOutput run 0=some a ∧ nativePartOutput run 1=some b
  | .ESn1 => ∃a b m,p.output=.branch none (kids2 (splitOldSlot run) a (splitNewSlotNative run) b) m ∧ nativePartOutput run 0=some b
  | .ESl1 => True
  | _ => False

def SplitShapes (run : TreeRun) : Prop := ∀p∈run.parts,SplitShape run p

private theorem output_append {run : TreeRun} (p : TreePart) {n : Nat} {c : PTrie}
    (h : nativePartOutput run n=some c) : nativePartOutput (pushPart run p) n=some c := by
  unfold nativePartOutput at h ⊢
  obtain ⟨a,ha,hc⟩:=Option.map_eq_some_iff.mp h
  have hn: n<run.parts.length := (List.getElem?_eq_some_iff.mp ha).1
  simp only [pushPart,List.getElem?_append,hn,ite_true,ha,Option.map_some,hc]

private theorem split_push {run : TreeRun} (h : SplitShapes run) (p : TreePart)
    (hp : p.kind≠.SPB) : SplitShapes (pushPart run p) := by
  intro q hq hk
  simp only [pushPart,List.mem_append,List.mem_singleton] at hq
  rcases hq with hq|rfl
  · have hh:=h q hq hk
    cases hc:run.terminal <;> simp only [SplitShape,pushPart,hc] at hh ⊢
    all_goals try contradiction
    all_goals try trivial
    all_goals obtain ⟨a,b,c,ho,hs⟩:=hh
    all_goals refine ⟨a,b,c,ho,?_⟩
    all_goals first | exact output_append p hs | exact ⟨output_append p hs.1,output_append p hs.2⟩
  · exact (hp hk).elim

private theorem split_wrap {run : TreeRun} (h : SplitShapes run) (src : PTrie) (key : List Nat) :
    SplitShapes (wrapRun src key run) := by
  cases key with
  | nil=>exact h
  | cons n ns=>exact split_push h _ (by simp)

private theorem leaf_split_shapes (key : List Nat) (s : Slot) (m : Nat) (target : List Nat) (v : Bytes) :
    SplitShapes (leafSplitRun key s m target v) := by
  unfold leafSplitRun
  generalize commonPrefix key target=p
  cases h1:key.drop p.length <;> cases h2:target.drop p.length <;> simp only [h1,h2]
  all_goals try apply split_wrap
  all_goals simp [SplitShapes,SplitShape,terminalRun,nativePartOutput,splitOldSlot,splitNewSlotNative,nativeKey,h1,h2]

private theorem ext_split_shapes (key : List Nat) (c : PTrie) (m : Nat) (target : List Nat) (v : Bytes) :
    SplitShapes (extSplitRun key c m target v) := by
  unfold extSplitRun
  generalize commonPrefix key target=p
  cases h1:key.drop p.length with
  | nil=>simp [h1,SplitShapes,terminalRun]
  | cons x xs=>
    cases h2:target.drop p.length <;> cases xs <;> simp only [h1,h2,List.isEmpty_nil,List.isEmpty_cons,Bool.false_eq_true,ite_false,ite_true]
    all_goals apply split_wrap
    all_goals simp [SplitShapes,SplitShape,terminalRun,nativePartOutput,splitOldSlot,splitNewSlotNative,nativeKey,h1,h2]

    all_goals exact ⟨c,rfl⟩

mutual
/-- Every native fresh-value part embeds the actual inserted value, including
all leaf/extension splits and branch insertion cases. -/
theorem traceUpsert_split_shapes : ∀(root : PTrie)(key : List Nat)(v : Bytes)(run : TreeRun),
    traceUpsert root key v=some run→SplitShapes run
  | .hash h,key,v,run,hr=>by simp [traceUpsert] at hr
  | .leaf old s mem,key,v,run,hr=>by
    by_cases he:old=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run
      simp [SplitShapes,terminalRun,SplitShape,newLeaf]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run
      exact leaf_split_shapes old s mem key v
  | .ext old c mem,key,v,run,hr=>by
    cases hp:isPrefix old key with
    | false=>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run
      exact ext_split_shapes old c mem key v
    | true=>
      cases hm:c.mem? with
      | none=>simp [traceUpsert,hp,hm] at hr
      | some cm=>
        cases hc:traceUpsert c (key.drop old.length) v with
        | none=>simp [traceUpsert,hp,hm,hc] at hr
        | some inner=>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          apply split_push (traceUpsert_split_shapes c _ v inner hc)
          cases old <;> simp
  | .branch sv kids mem,[],v,run,hr=>by
    cases sv <;> simp only [traceUpsert,Option.isSome_none,Option.isSome_some,Bool.false_eq_true,
      ite_false,ite_true,Option.some.injEq] at hr <;> subst run <;>
      simp [SplitShapes,terminalRun,SplitShape]
  | .branch sv kids mem,n::key,v,run,hr=>by
    cases hc:traceKids (.branch sv kids mem) (n::key) kids n key v with
    | none=>simp [traceUpsert,hc] at hr
    | some kr=>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      apply split_push (traceKids_split_shapes _ _ kids n key v kr hc)
      cases kr.inserted <;> simp

theorem traceKids_split_shapes : ∀(source : PTrie)(whole : List Nat)(kids : Kids)(n : Nat)
    (key : List Nat)(v : Bytes)(run : KidsRun),
    traceKids source whole kids n key v=some run→SplitShapes run.inner
  | source,whole,.nil,n,key,v,run,hr=>by simp [traceKids] at hr
  | source,whole,.none rest,0,key,v,run,hr=>by
    simp only [traceKids,Option.some.injEq] at hr
    subst run
    simp [SplitShapes,terminalRun,SplitShape,newLeaf]
  | source,whole,.some c rest,0,key,v,run,hr=>by
    cases hm:c.mem? with
    | none=>simp [traceKids,hm] at hr
    | some cm=>
      cases hc:traceUpsert c key v with
      | none=>simp [traceKids,hm,hc] at hr
      | some inner=>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        exact traceUpsert_split_shapes c key v inner hc
  | source,whole,.none rest,n+1,key,v,run,hr=>by
    cases hc:traceKids source whole rest n key v with
    | none=>simp [traceKids,hc] at hr
    | some inner=>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_split_shapes source whole rest n key v inner hc
  | source,whole,.some c rest,n+1,key,v,run,hr=>by
    cases hc:traceKids source whole rest n key v with
    | none=>simp [traceKids,hc] at hr
    | some inner=>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_split_shapes source whole rest n key v inner hc
end


end ZkFormal.NearV3.Assembly
