import ZkFormal.NearV3.Render.Ups.TreeInsertTrace
import ZkFormal.NearV3.Render.Ups.TreeKeys

namespace ZkFormal.NearV3.Assembly
open NearSpec UpsRows Render.UpsGen

/-- Missing-child branch parts retain their actual terminal slot and case. -/
def RbiInfo (run : TreeRun) : Prop :=
  ∀p∈run.parts,p.kind=.RBI→p.slot=run.terminalKey.headD 0 ∧
    run.terminal=.BI ∧ run.matched=0 ∧ run.terminalKey≠[]

private theorem rbi_push {run : TreeRun} (h : RbiInfo run) (p : TreePart)
    (hp : p.kind≠.RBI) : RbiInfo (pushPart run p) := by
  intro q hq hf
  simp only [pushPart,List.mem_append,List.mem_singleton] at hq
  rcases hq with hq|rfl
  · exact h q hq hf
  · exact (hp hf).elim

private theorem rbi_wrap {run : TreeRun} (h : RbiInfo run) (src : PTrie) (key : List Nat) :
    RbiInfo (wrapRun src key run) := by
  cases key with
  | nil=>exact h
  | cons n ns=>exact rbi_push h _ (by simp)

private theorem leaf_rbi (key : List Nat) (s : Slot) (m : Nat) (target : List Nat) (v : Bytes) :
    RbiInfo (leafSplitRun key s m target v) := by
  unfold leafSplitRun
  generalize commonPrefix key target=p
  cases h1:key.drop p.length <;> cases h2:target.drop p.length <;> simp only [h1,h2]
  all_goals try apply rbi_wrap
  all_goals simp [RbiInfo,terminalRun,newLeaf]

private theorem ext_rbi (key : List Nat) (c : PTrie) (m : Nat) (target : List Nat) (v : Bytes) :
    RbiInfo (extSplitRun key c m target v) := by
  unfold extSplitRun
  generalize commonPrefix key target=p
  cases h1:key.drop p.length with
  | nil=>simp [h1,RbiInfo,terminalRun]
  | cons x xs=>
    cases h2:target.drop p.length <;> cases xs <;> simp only [h1,h2,List.isEmpty_nil,List.isEmpty_cons,Bool.false_eq_true,ite_false,ite_true]
    all_goals apply rbi_wrap
    all_goals simp [RbiInfo,terminalRun,newLeaf]

mutual
/-- Every native fresh-value part embeds the actual inserted value, including
all leaf/extension splits and branch insertion cases. -/
theorem traceUpsert_rbi_info : ∀(root : PTrie)(key : List Nat)(v : Bytes)(run : TreeRun),
    traceUpsert root key v=some run→RbiInfo run
  | .hash h,key,v,run,hr=>by simp [traceUpsert] at hr
  | .leaf old s mem,key,v,run,hr=>by
    by_cases he:old=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run
      simp [RbiInfo,terminalRun,newLeaf]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run
      exact leaf_rbi old s mem key v
  | .ext old c mem,key,v,run,hr=>by
    cases hp:isPrefix old key with
    | false=>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run
      exact ext_rbi old c mem key v
    | true=>
      cases hm:c.mem? with
      | none=>simp [traceUpsert,hp,hm] at hr
      | some cm=>
        cases hc:traceUpsert c (key.drop old.length) v with
        | none=>simp [traceUpsert,hp,hm,hc] at hr
        | some inner=>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          apply rbi_push (traceUpsert_rbi_info c _ v inner hc)
          cases old <;> simp
  | .branch sv kids mem,[],v,run,hr=>by
    cases sv <;> simp only [traceUpsert,Option.isSome_none,Option.isSome_some,Bool.false_eq_true,
      ite_false,ite_true,Option.some.injEq] at hr <;> subst run <;>
      simp [RbiInfo,terminalRun]
  | .branch sv kids mem,n::key,v,run,hr=>by
    cases hc:traceKids (.branch sv kids mem) (n::key) kids n key v with
    | none=>simp [traceUpsert,hc] at hr
    | some kr=>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      have hi:=traceKids_rbi_info _ _ kids n key v kr hc
      cases hins:kr.inserted with
      | false=>exact rbi_push hi _ (by simp [hins])
      | true=>
        have he:=(traceKids_inserted _ _ _ _ _ _ _ hc hins).2.2
        simp [he,pushPart,RbiInfo,terminalRun,hins]

theorem traceKids_rbi_info : ∀(source : PTrie)(whole : List Nat)(kids : Kids)(n : Nat)
    (key : List Nat)(v : Bytes)(run : KidsRun),
    traceKids source whole kids n key v=some run→RbiInfo run.inner
  | source,whole,.nil,n,key,v,run,hr=>by simp [traceKids] at hr
  | source,whole,.none rest,0,key,v,run,hr=>by
    simp only [traceKids,Option.some.injEq] at hr
    subst run
    simp [RbiInfo,terminalRun,newLeaf]
  | source,whole,.some c rest,0,key,v,run,hr=>by
    cases hm:c.mem? with
    | none=>simp [traceKids,hm] at hr
    | some cm=>
      cases hc:traceUpsert c key v with
      | none=>simp [traceKids,hm,hc] at hr
      | some inner=>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        exact traceUpsert_rbi_info c key v inner hc
  | source,whole,.none rest,n+1,key,v,run,hr=>by
    cases hc:traceKids source whole rest n key v with
    | none=>simp [traceKids,hc] at hr
    | some inner=>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_rbi_info source whole rest n key v inner hc
  | source,whole,.some c rest,n+1,key,v,run,hr=>by
    cases hc:traceKids source whole rest n key v with
    | none=>simp [traceKids,hc] at hr
    | some inner=>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      exact traceKids_rbi_info source whole rest n key v inner hc
end


/-- The insertion slot is the correct first/last physical branch window for
this fixed scheduler key; it is not guessed from a convenient bitmap. -/
theorem traceUpsert_rbi_side {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) {p : TreePart} (hp : p∈run.parts)
    (hk : p.kind=.RBI) :
    p.slot=edgeSlot (if run.splitCursor [0,15]=1 then 0 else 1) := by
  obtain ⟨hslot,_,hmatched,hnon⟩:=traceUpsert_rbi_info root [0,15] v run hr p hp hk
  have hkey:=(trace_fixedKey_bounds hr).1
  cases hc:run.consumed [0,15] with
  | zero=>simp [TreeRun.splitCursor,hc,hmatched,hkey,edgeSlot] at hslot ⊢;exact hslot
  | succ n=>
    cases n with
    | zero=>simp [TreeRun.splitCursor,hc,hmatched,hkey,edgeSlot] at hslot ⊢;exact hslot
    | succ n=>simp [hc] at hkey;exact (hnon hkey).elim

end ZkFormal.NearV3.Assembly
