import ZkFormal.NearV3.Render.Ups.TreeSplitKids
import ZkFormal.NearV3.Render.Ups.TreeEdge

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

def NativeBranchWidth : PTrie → Prop
  | .branch _ kids _ => (treeKids kids).length=16
  | _ => True

def RunBranchWidth (run : TreeRun) : Prop := ∀ p∈run.parts, NativeBranchWidth p.output

theorem branchWidth_push {run : TreeRun} (h : RunBranchWidth run) (p : TreePart)
    (hp : NativeBranchWidth p.output) : RunBranchWidth (pushPart run p) := by
  intro q hq
  simp only [pushPart,List.mem_append,List.mem_singleton] at hq
  rcases hq with hq|rfl
  exact h q hq
  exact hp

theorem leafSplit_branchWidth (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes) :
    RunBranchWidth (leafSplitRun k s m key v) := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;>
    simp [RunBranchWidth,NativeBranchWidth,terminalRun,wrapRun,pushPart,newLeaf,wrapExt,kids1,kids2]

theorem extSplit_branchWidth (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes) :
    RunBranchWidth (extSplitRun k c m key v) := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,RunBranchWidth,terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [RunBranchWidth,NativeBranchWidth,terminalRun,wrapRun,pushPart,newLeaf,wrapExt,kids1,kids2]

mutual
theorem traceUpsert_branchWidth : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → t.wf=true → RunBranchWidth run
  | .hash _,_,_,_,hr,_ => by simp [traceUpsert] at hr
  | .leaf k s m,key,v,run,hr,hw => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run; simp [RunBranchWidth,terminalRun,NativeBranchWidth,newLeaf]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run; exact leafSplit_branchWidth k s m key v
  | .ext k c m,key,v,run,hr,hw => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run; exact extSplit_branchWidth k c m key v
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hc] at hr
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          have cw : c.wf=true := by simp only [PTrie.wf,Bool.and_eq_true] at hw; exact hw.1.1.2
          apply branchWidth_push (traceUpsert_branchWidth c _ v inner hc cw)
          trivial
  | .branch bv cs m,[],v,run,hr,hw => by
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run
    have cw : Kids.wf cs 16=true := by simp only [PTrie.wf,Bool.and_eq_true] at hw; exact hw.1.2
    simpa [RunBranchWidth,terminalRun,NativeBranchWidth] using (treeKids_wf cs 16 cw).1
  | .branch bv cs m,n::key,v,run,hr,hw => by
    cases hc : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hc] at hr
    | some inner =>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      have cw : Kids.wf cs 16=true := by simp only [PTrie.wf,Bool.and_eq_true] at hw; exact hw.1.2
      exact branchWidth_push (traceKids_branchWidth _ _ cs n key v inner hc 16 cw) _
        (traceKids_output_wf hc cw).1
 theorem traceKids_branchWidth : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids)
    (n : Nat) (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v=some run → ∀ width,
    Kids.wf cs width=true → RunBranchWidth run.inner
  | _,_,.nil,_,_,_,_,hr,_,_ => by simp [traceKids] at hr
  | source,whole,.none rest,0,key,v,run,hr,width,hw => by
    simp only [traceKids,Option.some.injEq] at hr
    subst run; simp [RunBranchWidth,terminalRun,NativeBranchWidth,newLeaf]
  | source,whole,.some c rest,0,key,v,run,hr,width,hw => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at hr
    | some cm =>
      cases hc : traceUpsert c key v with
      | none => simp [traceKids,hm,hc] at hr
      | some inner =>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        have cw : c.wf=true := by simp only [Kids.wf,Bool.and_eq_true] at hw; exact hw.1.2
        exact traceUpsert_branchWidth c key v inner hc cw
  | source,whole,.none rest,n+1,key,v,run,hr,width,hw => by
    cases hc : traceKids source whole rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      have rw : Kids.wf rest (width-1)=true := by simp only [Kids.wf,Bool.and_eq_true] at hw; exact hw.2
      exact traceKids_branchWidth source whole rest n key v inner hc (width-1) rw
  | source,whole,.some c rest,n+1,key,v,run,hr,width,hw => by
    cases hc : traceKids source whole rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      have rw : Kids.wf rest (width-1)=true := by simp only [Kids.wf,Bool.and_eq_true] at hw; exact hw.2
      exact traceKids_branchWidth source whole rest n key v inner hc (width-1) rw
end
end ZkFormal.NearV3.Assembly
