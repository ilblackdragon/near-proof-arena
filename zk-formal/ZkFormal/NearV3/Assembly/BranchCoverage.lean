import ZkFormal.NearV3.Assembly.SourceContexts

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

def BranchCovered (contexts : List SourceContext) (run : TreeRun) : Prop :=
  ∀ p∈run.parts,p.kind=.RDB → ∃ ctx∈contexts,
    ctx.address.tree=p.source ∧ ∃ rest,ctx.key=p.slot::rest

private theorem branchCovered_mono {xs ys run} (h : BranchCovered xs run)
    (hm : ∀ x∈xs,x∈ys) : BranchCovered ys run := by
  intro p hp hk
  obtain ⟨ctx,hc,he,hr⟩ := h p hp hk
  exact ⟨ctx,hm ctx hc,he,hr⟩

private theorem leafSplit_noRDB (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (value : Bytes) :
    BranchCovered [] (leafSplitRun k s m key value) := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;> simp [BranchCovered,terminalRun,wrapRun,pushPart]

private theorem extSplit_noRDB (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (value : Bytes) :
    BranchCovered [] (extSplitRun k c m key value) := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,BranchCovered,terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [BranchCovered,terminalRun,wrapRun,pushPart]

mutual
theorem traceUpsert_branch_covered : ∀ t key value run,
    traceUpsert t key value=some run → ∀ n vid d,
      BranchCovered (sourceContexts n vid d t key) run
  | .hash _,_,_,_,h => by simp [traceUpsert] at h
  | .leaf k s m,key,value,run,h => by
    intro n vid d
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run
      simp [BranchCovered,terminalRun]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run
      exact branchCovered_mono (leafSplit_noRDB k s m key value) (by simp)
  | .ext k c m,key,value,run,h => by
    intro n vid d
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run
      exact branchCovered_mono (extSplit_noRDB k c m key value) (by simp)
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at h
      | some cm =>
        cases hr : traceUpsert c (key.drop k.length) value with
        | none => simp [traceUpsert,hp,hm,hr] at h
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst run
          intro p hpart hkind
          simp only [pushPart,List.mem_append,List.mem_singleton] at hpart
          rcases hpart with hpart | rfl
          · exact branchCovered_mono (traceUpsert_branch_covered _ _ _ _ hr (n+1) vid (d+1))
              (fun ctx hc => by simp [sourceContexts,hp,hc]) p hpart hkind
          · cases k <;> simp at hkind
  | .branch sv cs m,[],value,run,h => by
    intro n vid d
    simp only [traceUpsert,Option.some.injEq] at h
    subst run
    cases sv <;> simp [BranchCovered,terminalRun]
  | .branch sv cs m,slot::key,value,run,h => by
    intro n vid d
    cases hr : traceKids (.branch sv cs m) (slot::key) cs slot key value with
    | none => simp [traceUpsert,hr] at h
    | some inner =>
      simp only [traceUpsert,hr,Option.map_some,Option.some.injEq] at h
      subst run
      intro p hpart hkind
      simp only [pushPart,List.mem_append,List.mem_singleton] at hpart
      rcases hpart with hpart | rfl
      · exact branchCovered_mono (traceKids_branch_covered _ _ _ _ _ _ _ hr
          (n+1) (vid+(optSlotVal sv).length) (d+1))
          (fun ctx hc => by simp [sourceContexts,hc]) p hpart hkind
      · exact ⟨⟨⟨n,vid,d,.branch sv cs m⟩,slot::key⟩,by simp [sourceContexts],rfl,key,rfl⟩
theorem traceKids_branch_covered : ∀ source wholeKey cs slot key value run,
    traceKids source wholeKey cs slot key value=some run → ∀ n vid d,
      BranchCovered (kidSourceContexts n vid d cs slot key) run.inner
  | _,_,.nil,_,_,_,_,h => by simp [traceKids] at h
  | source,wholeKey,.none rest,0,key,value,run,h => by
    intro n vid d
    simp only [traceKids,Option.some.injEq] at h
    subst run
    simp [BranchCovered,terminalRun]
  | source,wholeKey,.some c rest,0,key,value,run,h => by
    intro n vid d
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key value with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        exact traceUpsert_branch_covered _ _ _ _ hr n vid d
  | source,wholeKey,.none rest,i+1,key,value,run,h => by
    intro n vid d
    cases hr : traceKids source wholeKey rest i key value with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_branch_covered _ _ _ _ _ _ _ hr n vid d
  | source,wholeKey,.some c rest,i+1,key,value,run,h => by
    intro n vid d
    cases hr : traceKids source wholeKey rest i key value with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_branch_covered _ _ _ _ _ _ _ hr (n+tsize c) (vid+(valsOf c).length) d
end

end ZkFormal.NearV3.Assembly
