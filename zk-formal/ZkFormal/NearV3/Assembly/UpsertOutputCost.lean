import ZkFormal.NearV3.Assembly.UpsertSplitSize

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

mutual
/-- Only the terminal/split introduces a bounded additive cost; depth does not
multiply that overhead because proper ancestors retain their encoded widths. -/
theorem traceUpsert_output_charge : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun),
    traceUpsert t key v=some run → t.wf=true → key.length≤2 →
    outputByteCharge run≤sourceByteCharge run+4096
  | .hash _,_,_,_,hr,_,_ => by simp [traceUpsert] at hr
  | .leaf k s m,key,v,run,hr,hw,hk => by
    have hs : NearSpec.slotOk s=true := by simp only [PTrie.wf,Bool.and_eq_true] at hw; exact hw.1.1.2
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at hr
      subst run; subst key
      have hb := newLeaf_byte_size k v hk
      simp only [outputByteCharge,sourceByteCharge,terminalRun,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      omega
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at hr
      subst run; exact leafSplit_output_charge k s m key v hs hk
  | .ext k c m,key,v,run,hr,hw,hk => by
    have cw : c.wf=true := by simp only [PTrie.wf,Bool.and_eq_true] at hw; exact hw.1.1.2
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at hr
      subst run; exact extSplit_output_charge k c m key v cw hk
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at hr
      | some cm =>
        cases hc : traceUpsert c (key.drop k.length) v with
        | none => simp [traceUpsert,hp,hm,hc] at hr
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hc,Option.some.injEq] at hr
          subst run
          have h := traceUpsert_output_charge c _ v inner hc cw (by simp only [List.length_drop]; omega)
          have he := traceUpsert_extension_bytes hc cw k m (m+inner.output.memD-cm)
          simp only [outputByteCharge_push,sourceByteCharge_push,UpsSpec.qRDE]
          omega
  | .branch bv cs m,[],v,run,hr,hw,hk => by
    simp only [traceUpsert,Option.some.injEq] at hr
    subst run
    have h := branch_value_byte_growth bv cs m
      (m+valueMem v.length-(match bv with | some s => valueMem s.len | none => 0)) v
    simp only [outputByteCharge,sourceByteCharge,terminalRun,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    cases bv <;> simp_all only <;> omega
  | .branch bv cs m,n::key,v,run,hr,hw,hk => by
    have cw : Kids.wf cs 16=true := by simp only [PTrie.wf,Bool.and_eq_true] at hw; exact hw.1.2
    cases hc : traceKids (.branch bv cs m) (n::key) cs n key v with
    | none => simp [traceUpsert,hc] at hr
    | some inner =>
      simp only [traceUpsert,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      have h := traceKids_output_charge (.branch bv cs m) (n::key) cs n key v inner hc 16 cw
        (by simp only [List.length_cons] at hk; omega)
      have he := traceKids_branch_bytes hc cw bv m (m+inner.newMem-inner.oldMem)
      simp only [outputByteCharge_push,sourceByteCharge_push]
      omega
 theorem traceKids_output_charge : ∀ (source : PTrie) (wholeKey : List Nat) (cs : Kids)
    (n : Nat) (key : List Nat) (v : Bytes) (run : KidsRun),
    traceKids source wholeKey cs n key v=some run → ∀ width, Kids.wf cs width=true → key.length≤2 →
    outputByteCharge run.inner+(if run.inserted then 32 else 0)≤sourceByteCharge run.inner+4096
  | _,_,.nil,_,_,_,_,hr,_,_,_ => by simp [traceKids] at hr
  | source,whole,.none rest,0,key,v,run,hr,width,hw,hk => by
    simp only [traceKids,Option.some.injEq] at hr
    subst run
    have hb := newLeaf_byte_size key v hk
    simp only [outputByteCharge,sourceByteCharge,terminalRun,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,ite_true]
    omega
  | source,whole,.some c rest,0,key,v,run,hr,width,hw,hk => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at hr
    | some cm =>
      cases hc : traceUpsert c key v with
      | none => simp [traceKids,hm,hc] at hr
      | some inner =>
        simp only [traceKids,hm,hc,Option.some.injEq] at hr
        subst run
        have cw : c.wf=true := by simp only [Kids.wf,Bool.and_eq_true] at hw; exact hw.1.2
        simpa using traceUpsert_output_charge c key v inner hc cw hk
  | source,whole,.none rest,n+1,key,v,run,hr,width,hw,hk => by
    cases hc : traceKids source whole rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      have rw : Kids.wf rest (width-1)=true := by simp only [Kids.wf,Bool.and_eq_true] at hw; exact hw.2
      exact traceKids_output_charge source whole rest n key v inner hc (width-1) rw hk
  | source,whole,.some c rest,n+1,key,v,run,hr,width,hw,hk => by
    cases hc : traceKids source whole rest n key v with
    | none => simp [traceKids,hc] at hr
    | some inner =>
      simp only [traceKids,hc,Option.map_some,Option.some.injEq] at hr
      subst run
      have rw : Kids.wf rest (width-1)=true := by simp only [Kids.wf,Bool.and_eq_true] at hw; exact hw.2
      exact traceKids_output_charge source whole rest n key v inner hc (width-1) rw hk
end

/-- Concrete output-node cost against the native input occurrence measure. -/
theorem traceUpsert_output_charge_pre (t : PTrie) (key : List Nat) (v : Bytes) (run : TreeRun)
    (hr : traceUpsert t key v=some run) (hw : t.wf=true) (hk : key.length≤2) :
    outputByteCharge run≤4*unfoldedBytesT t+4096 := by
  have ho := traceUpsert_output_charge t key v run hr hw hk
  have hs := traceUpsert_source_charge t key v run hr
  have hn := nodeByteCharge_le_unfolded t
  omega

end ZkFormal.NearV3.Assembly
