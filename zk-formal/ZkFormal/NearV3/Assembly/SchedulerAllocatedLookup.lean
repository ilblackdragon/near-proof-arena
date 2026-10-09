import ZkFormal.NearV3.Assembly.SchedulerCodecAllocatedIds
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 ZkFormal.Near Render.UpsGen Rcpt.Candidates.NodePostUpdate

/-- A successful scheduler read supplies an executable lookup, including absence.
Unknown hashed subtrees cannot be replaced by an absent value. -/
theorem prior_lookup (before : List PTrie) (tree : PTrie) (prior : Option Bytes)
    (hr:readKey tree keyBwState "bandwidth scheduler state"=.ok prior) (wid : Nat) :
    ∃ss,nativeLookupSteps (forestLookupNid before) (forestLookupVid before) tree keyBwState=some ss ∧
      (nativeLookupWalk wid before.length (forestLookupNid before) tree ss).steps.getLast?.map lookupFinal=
        some (prior.map (fun _=>priorValueId before tree)) ∧
      (nativeLookupWalk wid before.length (forestLookupNid before) tree ss).steps.length=keyBwState.length+2 := by
  have hf:tree.find keyBwState=some prior := by
    unfold readKey at hr
    split at hr <;> simp_all
  have hd:=nativeLookupSteps_defined (forestLookupNid before) (forestLookupVid before) tree keyBwState
  rw [hf] at hd
  cases hs:nativeLookupSteps (forestLookupNid before) (forestLookupVid before) tree keyBwState with
  | none=>simp [hs] at hd
  | some ss=>
    refine ⟨ss,rfl,?_,nativeLookupWalk_length _ _ _ _ _ _ ss hs⟩
    cases prior with
    | none=>exact native_lookup_absent_final _ _ _ _ _ _ _ hs hf
    | some bytes=>exact present_walk before tree bytes hr wid ss hs

/-- The selected native block uses the SAME allocated value ID in its executable
lookup terminal and forest value provider. No caller-supplied lookup steps. -/
theorem allocated_lookup (bs : List NativeBlock)
    (hids:∀(i : Nat)(b : NativeBlock),bs[i]?=some b→
      b.vid=priorValueId ((bs.map (fun b=>b.witness.pre)).take i) b.witness.pre)
    (pre post : List NativeBlock) (b : NativeBlock) (he:bs=pre++b::post)
    (hb:b.Valid) (wid : Nat) :
    ∃ss,nativeLookupSteps (forestLookupNid (pre.map (fun b=>b.witness.pre)))
        (forestLookupVid (pre.map (fun b=>b.witness.pre))) b.witness.pre keyBwState=some ss ∧
      (nativeLookupWalk wid pre.length (forestLookupNid (pre.map (fun b=>b.witness.pre)))
        b.witness.pre ss).steps.getLast?.map lookupFinal=some (b.prior.map (fun _=>b.vid)) ∧
      (∀bytes,b.prior=some bytes→
        (forestStoreViews (bs.map (fun b=>b.witness.pre))).values[b.vid]?=some (seedValue b.vid bytes)) := by
  have hi:bs[pre.length]?=some b := by simp [he]
  have hid:=hids _ _ hi
  have ht:((bs.map (fun b=>b.witness.pre)).take pre.length)=pre.map (fun b=>b.witness.pre) := by
    simp [he,List.map_append]
  rw [ht] at hid
  obtain ⟨ss,hs,hfinal,_⟩:=prior_lookup (pre.map (fun b=>b.witness.pre)) b.witness.pre b.prior hb.2.1 wid
  refine ⟨ss,hs,?_,fun bytes hp=>allocated_present bs hids pre post b he hb bytes hp⟩
  simpa only [List.length_map,←hid] using hfinal
end ZkFormal.NearV3.Assembly.CodecDigest
