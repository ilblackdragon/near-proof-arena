import ZkFormal.NearV3.Rcpt.Candidates.NativeSourceAddressDepth
import ZkFormal.NearV3.Render.Ups.TreeTerminalSources
import ZkFormal.NearV3.Render.Ups.TreeTerminalPrefix
import ZkFormal.NearV3.Render.Ups.TreePlanDepth

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 Assembly Render.UpsGen UpsRows

def sourcePosition (run : TreeRun) (k : Nat) : Nat :=
  run.parts.length-max (termPlan run.terminal run.matched).length (k+1)

theorem sourcePosition_push (run : TreeRun) (p : TreePart) (k : Nat)
    (hk : k<run.parts.length) (hn : (termPlan run.terminal run.matched).length≤run.parts.length) :
    sourcePosition (pushPart run p) k=sourcePosition run k+1 := by
  simp only [sourcePosition,pushPart,List.length_append,List.length_cons,List.length_nil]
  omega

theorem sourcePosition_last (run : TreeRun) (p : TreePart) :
    sourcePosition (pushPart run p) run.parts.length=0 := by
  simp only [sourcePosition,pushPart,List.length_append,List.length_cons,List.length_nil]
  omega

private theorem root_address (n v d : Nat) (t : PTrie) (key : List Nat) :
    (sourceAddresses n v d t key)[0]?=some ⟨n,v,d,t⟩ := by
  cases t <;> cases key <;> rfl

private theorem terminal_position {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) (hd : fdepth t key=1) (ht : run.terminalSource=t)
    (n v d k : Nat) (p : TreePart) (hp : run.parts[k]?=some p) :
    ∃a,(sourceAddresses n v d t key)[sourcePosition run k]?=some a ∧ a.tree=p.source := by
  have hl:=traceUpsert_nQ hr
  rw [hd] at hl
  have hlen : run.parts.length=(termPlan run.terminal run.matched).length := by omega
  have hk:=(List.getElem?_eq_some_iff.mp hp).1
  have hpos : sourcePosition run k=0 := by unfold sourcePosition;omega
  have hm : p∈run.parts.take (termPlan run.terminal run.matched).length := by
    rw [←hlen,List.take_length]
    exact List.mem_of_getElem? hp
  have hs:=(traceUpsert_terminalSources t key value run hr) p hm
  exact ⟨⟨n,v,d,t⟩,hpos ▸ root_address n v d t key,(hs.trans ht).symm⟩

private theorem push_address {run : TreeRun} {p q : TreePart} {addresses : List OccurrenceAddress}
    {root : OccurrenceAddress} (hroot : root.tree=q.source) (k : Nat)
    (hp : (pushPart run q).parts[k]?=some p) (hnot : p.kind≠.NLF)
    (hin : ∀k p,run.parts[k]?=some p→p.kind≠.NLF→
      (termPlan run.terminal run.matched).length≤run.parts.length ∧
      ∃a,addresses[sourcePosition run k]?=some a ∧ a.tree=p.source) :
    ∃a,(root::addresses)[sourcePosition (pushPart run q) k]?=some a ∧ a.tree=p.source := by
  have hk:=(List.getElem?_eq_some_iff.mp hp).1
  simp only [pushPart,List.length_append,List.length_cons,List.length_nil] at hk
  by_cases hi : k<run.parts.length
  · have hp' : run.parts[k]?=some p := by
      simpa only [pushPart,List.getElem?_append,hi,ite_true] using hp
    obtain ⟨hn,a,ha,ht⟩:=hin k p hp' hnot
    exact ⟨a,by rw [sourcePosition_push run q k hi hn];exact ha,ht⟩
  · have he : k=run.parts.length := by omega
    subst k
    have hpq : p=q := by simpa [pushPart] using hp.symm
    subst p
    exact ⟨root,by rw [sourcePosition_last];rfl,hroot⟩

mutual
theorem native_part_source_position : ∀t key value run,
    traceUpsert t key value=some run→∀n v d k p,run.parts[k]?=some p→p.kind≠.NLF→
    ∃a,(sourceAddresses n v d t key)[sourcePosition run k]?=some a ∧ a.tree=p.source
  | .hash _,_,_,_,h,_,_,_,_,_,_,_ => by simp [traceUpsert] at h
  | .leaf stored slot mem,key,value,run,h,n,v,d,k,p,hp,hnot => by
    apply terminal_position h (by simp [fdepth]) ?_ n v d k p hp
    by_cases he : stored=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run;simp only [terminalRun,he]
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run
      exact leafSplitRun_terminalSource stored slot mem key value
  | .ext stored child mem,key,value,run,h,n,v,d,k,p,hp,hnot => by
    cases hprefix : isPrefix stored key with
    | false =>
      apply terminal_position h (by simp [fdepth,hprefix]) ?_ n v d k p hp
      simp only [traceUpsert,hprefix,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run
      exact extSplitRun_terminalSource stored child mem key value
    | true =>
      cases hm : child.mem? with
      | none => simp [traceUpsert,hprefix,hm] at h
      | some cm =>
        cases hc : traceUpsert child (key.drop stored.length) value with
        | none => simp [traceUpsert,hprefix,hm,hc] at h
        | some inner =>
          simp only [traceUpsert,hprefix,ite_true,hm,hc,Option.some.injEq] at h
          subst run
          simp only [sourceAddresses,hprefix,ite_true]
          apply push_address (root:=⟨n,v,d,.ext stored child mem⟩) rfl k hp hnot
          intro j q hq hnq
          refine ⟨by have hl:=traceUpsert_nQ hc;omega,?_⟩
          exact native_part_source_position child (key.drop stored.length) value inner hc (n+1) v (d+1) j q hq hnq
  | .branch sv cs mem,[],value,run,h,n,v,d,k,p,hp,hnot => by
    apply terminal_position h (by simp [fdepth]) ?_ n v d k p hp
    simp only [traceUpsert,Option.some.injEq] at h
    subst run;cases sv <;> rfl
  | .branch sv cs mem,j::key,value,run,h,n,v,d,k,p,hp,hnot => by
    cases hc : traceKids (.branch sv cs mem) (j::key) cs j key value with
    | none => simp [traceUpsert,hc] at h
    | some inner =>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at h
      subst run
      simp only [sourceAddresses]
      apply push_address (root:=⟨n,v,d,.branch sv cs mem⟩) rfl k hp hnot
      intro i q hq hnq
      exact native_kid_source_position (.branch sv cs mem) (j::key) cs j key value inner hc
        (n+1) (v+(optSlotVal sv).length) (d+1) i q hq hnq

theorem native_kid_source_position : ∀source whole cs j key value run,
    traceKids source whole cs j key value=some run→∀n v d k p,run.inner.parts[k]?=some p→p.kind≠.NLF→
    (termPlan run.inner.terminal run.inner.matched).length≤run.inner.parts.length ∧
    ∃a,(kidSourceAddresses n v d cs j key)[sourcePosition run.inner k]?=some a ∧ a.tree=p.source
  | _,_,.nil,_,_,_,_,h,_,_,_,_,_,_,_ => by simp [traceKids] at h
  | source,whole,.none rest,0,key,value,run,h,n,v,d,k,p,hp,hnot => by
    simp only [traceKids,Option.some.injEq] at h
    subst run
    cases k with
    | zero => cases hp;exact False.elim (hnot rfl)
    | succ k => simp [terminalRun] at hp
  | source,whole,.some c rest,0,key,value,run,h,n,v,d,k,p,hp,hnot => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hc : traceUpsert c key value with
      | none => simp [traceKids,hm,hc] at h
      | some inner =>
        simp only [traceKids,hm,hc,Option.some.injEq] at h
        subst run
        dsimp only
        refine ⟨by have hl:=traceUpsert_nQ hc;omega,?_⟩
        exact native_part_source_position c key value inner hc n v d k p hp hnot
  | source,whole,.none rest,j+1,key,value,run,h,n,v,d,k,p,hp,hnot => by
    cases hc : traceKids source whole rest j key value with
    | none => simp [traceKids,hc] at h
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at h
      subst run
      exact native_kid_source_position source whole rest j key value inner hc n v d k p hp hnot
  | source,whole,.some c rest,j+1,key,value,run,h,n,v,d,k,p,hp,hnot => by
    cases hc : traceKids source whole rest j key value with
    | none => simp [traceKids,hc] at h
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at h
      subst run
      exact native_kid_source_position source whole rest j key value inner hc (n+tsize c) (v+(valsOf c).length) d k p hp hnot
end

theorem sourcePosition_plan {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) (k : Nat) :
    sourcePosition run k=planDepth (fdepth t key-1) (termPlan run.terminal run.matched).length k := by
  have hl:=traceUpsert_nQ hr
  unfold sourcePosition planDepth
  omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
