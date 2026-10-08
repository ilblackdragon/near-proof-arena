import ZkFormal.NearV3.Assembly.SchedulerNodeMessages
import ZkFormal.NearV3.Assembly.CompactWalkNativeRoot
import ZkFormal.NearV3.Render.Ups.SchedulerEncodedInstances

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render Render.UpsGen ZkFormal.Air ZkFormal.Near

/-- Final indexed native message is the actual runtime root, not a new hash premise. -/
theorem nativeJobMessage_root {root : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root key v=some run) (tau : Nat) :
    nativeJobMessage run v tau run.parts.length=
      digMsg (upsertJobId tau run.parts.length) (nodeEnc run.output).length
        ((sha256 (nodeEnc run.output)).map UInt8.toNat) := by
  obtain ⟨p,hp,hout⟩:=Option.map_eq_some_iff.mp (traceUpsert_rootOutput hr)
  rw [List.getLast?_eq_getElem?] at hp
  have hn:run.parts.length=run.parts.length-1+1:=by
    have hh:=(List.getElem?_eq_some_iff.mp hp).1
    omega
  conv=>lhs;rw [hn]
  rw [nativeJobMessage_part v tau hp,hout,←hn]

/-- Whole actual compact instance DIGEST consumers equal its native SHA batch,
including W3 and every branch/split/ancestor payload, with multiplicity. -/
theorem allocated_instance_messages {us : List SchedulerUpsertWitness} {tau : Nat}
    {u : SchedulerUpsertWitness} {I : UpsInst}
    (hv : u.Valid) (hw : u.pre.wf=true)
    (ha : AllocatedNativeInstance us tau u I) (hs : NativeShaFamily u I)
    (he : NativeEncodedInstance u I) (hi : InstOk I) (hp : NativePartFamily I) :
    ((CompactPhysicalDigests.digestRowMsgs I (.w 3)++
      (List.range (nQ I)).flatMap (fun k=>(List.range (part I k).q.length).flatMap
        (CompactPhysicalDigests.nodeDigestMsgs I k))).map Msg.toFp).Perm
      ((Sha.Gen.expectedDigests (upsertShaJobs I.tau u.value u.run)).map Msg.toFp) := by
  have hroot:=CompactPhysicalDigests.allocated_walk_root_digest hv ha hs (fun _=>0)
  have hroot' : (CompactPhysicalDigests.digestRowMsgs I (.w 3)).map Msg.toFp=
      [(nativeJobMessage u.run u.value I.tau u.run.parts.length).toFp] := by
    rw [nativeJobMessage_root hv.1]
    have heq : Sha.Gen.expectedDigests [upsertShaJob I.tau (nQ I) (nodeEnc u.run.output)]=
        [digMsg (upsertJobId I.tau u.run.parts.length) (nodeEnc u.run.output).length
          ((sha256 (nodeEnc u.run.output)).map UInt8.toNat)] := by
      simp only [Sha.Gen.expectedDigests,upsertShaJob,List.filter_cons_of_pos,List.filter_nil,
        List.map_cons,List.map_nil,List.length_map,nativeBytes_roundtrip,hs.1]
      rfl
    rw [heq] at hroot
    exact hroot.symm
  have hnodes : (((List.range (nQ I)).flatMap (fun k=>(List.range (part I k).q.length).flatMap
        (CompactPhysicalDigests.nodeDigestMsgs I k))).map Msg.toFp).Perm
      ((List.range u.run.parts.length).map (fun j=>(nativeJobMessage u.run u.value I.tau j).toFp)) := by
    obtain ⟨recordId,B,base,Qs,henc,rfl⟩:=he
    exact nativeInstance_node_messages recordId B (by simpa only [keyBwState_nibbles] using hv.1) hw base henc hi hp
  rw [List.map_append,hroot',nativeJobMessages_batch,List.map_map]
  apply List.Perm.trans ((List.Perm.refl _).append hnodes)
  rw [List.range_succ,List.map_append,List.map_cons,List.map_nil]
  exact List.perm_append_comm

end ZkFormal.NearV3.Assembly
