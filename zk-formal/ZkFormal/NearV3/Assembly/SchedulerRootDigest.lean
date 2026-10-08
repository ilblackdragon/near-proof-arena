import ZkFormal.NearV3.Assembly.SchedulerNativeDigests
import ZkFormal.NearV3.Render.Ups.SchedulerShaInstances
import ZkFormal.NearV3.Render.Ups.AcceptedInstanceList
import ZkFormal.NearV3.Render.Ups.TreeOutputLinks

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Near Render.UpsGen

/-- The last concrete SHA job encodes exactly the resulting native trie root. -/
theorem upsert_root_job {root : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root key value=some run) (tau : Nat) :
    (upsertShaJobs tau value run)[run.parts.length]?=
      some (upsertShaJob tau run.parts.length (nodeEnc run.output)) := by
  have ho := traceUpsert_rootOutput hr
  obtain ⟨p,hp,hout⟩ := Option.map_eq_some_iff.mp ho
  rw [List.getLast?_eq_getElem?] at hp
  have hl := (List.getElem?_eq_some_iff.mp hp).1
  have hn : run.parts.length=run.parts.length-1+1 := by omega
  conv => lhs; rw [hn]
  rw [upsertShaJobs_part,hp]
  simp only [Option.map_some,hout]
  rw [←hn]

/-- The actual allocated W3 root request carries exactly the last native SHA
job's length and digest. Root bytes are supplied by AllocatedNativeInstance. -/
theorem allocated_root_digest {us : List SchedulerUpsertWitness} {tau : Nat}
    {u : SchedulerUpsertWitness} {I : Render.UpsInst}
    (hv : u.Valid) (ha : AllocatedNativeInstance us tau u I) (hs : NativeShaFamily u I) :
    Sha.Gen.expectedDigests [upsertShaJob I.tau (nQ I) (nodeEnc u.run.output)]=
      [digMsg (upsertJobId I.tau (nQ I)) (rlen I) I.post] := by
  have hr := hv.1
  have ho := traceUpsert_rootOutput hr
  obtain ⟨p,hp,hout⟩ := Option.map_eq_some_iff.mp ho
  rw [List.getLast?_eq_getElem?] at hp
  have hl := (List.getElem?_eq_some_iff.mp hp).1
  have hk : nQ I-1<nQ I := by rw [hs.1];exact hl
  obtain ⟨M,hM,_,hbytes⟩ := hs.2 (nQ I-1) hk
  have hn : nQ I-1+1=u.run.parts.length := by rw [hs.1];omega
  rw [hn,upsert_root_job hr I.tau] at hM
  have hm := Option.some.inj hM
  subst M
  have hlen : rlen I=(nodeEnc u.run.output).length := by
    have he := congrArg List.length hbytes
    simpa only [upsertShaJob,List.length_map,rlen] using he.symm
  have hhash : sha256 (nodeEnc u.run.output)=u.run.output.hashOf := by
    have he := upsertShaJob_node_digest hr (List.mem_of_getElem? hp)
    simpa only [hout] using he
  rw [hlen,ha.2.2.1]
  simp only [Sha.Gen.expectedDigests,upsertShaJob,List.filter_cons_of_pos,List.filter_nil,
    List.map_cons,List.map_nil,List.length_map,nativeBytes_roundtrip,hhash]
  rfl

end ZkFormal.NearV3.Assembly
