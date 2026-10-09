import ZkFormal.NearV3.Assembly.SchedulerCodecSanityInput
import ZkFormal.NearV3.Assembly.SchedulerCodecHashBlock

namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Native prepared Codec input determines the entire sanity SHA job output. -/
theorem prepared_sanity_job {u : SchedulerUpsertWitness} (hv:u.Valid)
    {sp : Scheduler.SchedPub} {prev : Option Bytes} {old : Bandwidth.State}
    (hr : readKey u.pre keyBwState "bandwidth scheduler state"=.ok prev)
    (hp : schedPub u.ctx=some sp)
    (hd : (match prev with | none=>some Bandwidth.State.initial | some b=>Bandwidth.State.decode b)=some old)
    (tau : Nat) :
    Sha.Gen.expectedDigests [schedulerSanityJob tau u]=
      [digMsg (11+16*tau) 64 ((sha256 (codecSanityInput (ProcPreparedSequence.input sp old) prev.isSome)).map UInt8.toNat)] := by
  have hinput:=prepared_sanity_input hr hp hd
  obtain ⟨input,hi,hlen,_⟩:=SchedulerUpsertWitness.sanity hv
  rw [hinput] at hi
  cases hi
  simp only [Sha.Gen.expectedDigests,schedulerSanityJob,hinput,Option.getD_some,
    List.filter_cons_of_pos,List.filter_nil,List.map_cons,List.map_nil,
    List.length_map,nativeBytes_roundtrip,hlen]
  rfl

/-- The same native transition supplies the complete physical32-row Codec
hash block. Ordinary runtime reads discharge the SHA identity; no old Codec
local predicate or independent hash matching premise is used. -/
theorem prepared_hash_block {u : SchedulerUpsertWitness} (hv:u.Valid)
    {sp : Scheduler.SchedPub} {prev : Option Bytes} {old : Bandwidth.State}
    (hr : readKey u.pre keyBwState "bandwidth scheduler state"=.ok prev)
    (hp : schedPub u.ctx=some sp)
    (hd : (match prev with | none=>some Bandwidth.State.initial | some b=>Bandwidth.State.decode b)=some old)
    (R : Sched.Gen.Run) (htau:R.tau<ZkFormal.Algebra.P) (vidV base0 : Nat)
    (tr : Trace Fp) (t f : Nat) (pub : List Fp)
    (hrows : let I:=ProcPreparedSequence.input sp old
      let present:=prev.isSome
      let digest:=(sha256 (codecSanityInput I present)).map UInt8.toNat
      let hpre:=if present then I.prev.sanityHash.map UInt8.toNat else List.replicate 32 0
      ∀j,j<32→∀c,tr.cell t (f+j) c=Fp.ofNat
        ((ProcPriorCodecAssignments.hashRow (ProcPriorCodecNativeHash.instanceCells I R present vidV)
          digest hpre present base0 j)[c]!)) :
    (List.range 32).flatMap (fun j=>Near.rowTraffic Sched.Codec.interactions tr t (f+j) pub B_DIGEST false)=
      (Sha.Gen.expectedDigests [schedulerSanityJob R.tau u]).map Msg.toFp := by
  rw [prepared_sanity_job hv hr hp hd R.tau]
  exact installed_hash_block _ R _ vidV _ _ base0 (by simp) htau tr t f pub hrows

end ZkFormal.NearV3.Assembly.CodecDigest
