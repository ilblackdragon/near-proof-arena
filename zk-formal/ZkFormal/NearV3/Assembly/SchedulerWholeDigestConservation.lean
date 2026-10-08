import ZkFormal.NearV3.Assembly.SchedulerCodecNativeBlocks
import ZkFormal.NearV3.Assembly.SchedulerDigestConservation
import ZkFormal.NearV3.Assembly.SchedulerCodecRepairedDigests

namespace ZkFormal.NearV3.Assembly
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
open Render Render.UpsGen Candidates CodecDigest
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Complete scheduler DIGEST conservation between the native SHA jobs and
both physical consumers: compact UPS plus the corrected generated Codec.
The exact same operational witness sequence determines both job families. -/
theorem scheduler_whole_digest_count (bs : List NativeBlock) (insts : List UpsInst)
    (hlen:bs.length≤32) (hsize:insts.length=bs.length)
    (hb:∀b∈bs,b.Valid ∧ b.run.n≤64 ∧ b.witness.pre.wf=true)
    (ho:∀(i:Nat)(b:NativeBlock),bs[i]?=some b→b.run.tau=i)
    (hi:∀i u I,(bs.map NativeBlock.witness)[i]?=some u→insts[i]?=some I→
      AllocatedNativeInstance (bs.map NativeBlock.witness) i u I ∧
        NativeShaFamily u I ∧ NativeEncodedInstance u I)
    (hcap:UpsRelay.compactR insts≤2^22) (tu tc : Nat) (pub msg : List Fp) :
    tableBusCount UpsRelay.compactTable.interactions (CompactHeight.trace insts) tu pub B_DIGEST false msg+
      tableBusCount ProcPriorCodecActual.table.interactions
        (SchedHeight.trace (nativeBlockRows bs) Sched.Gen.codecPad) tc pub B_DIGEST false msg=
      ((Sha.Gen.expectedDigests (schedulerShaJobs 0 (bs.map NativeBlock.witness)++
        schedulerSanityJobs 0 (bs.map NativeBlock.witness))).map Msg.toFp).count msg := by
  have hv:∀u∈bs.map NativeBlock.witness,u.Valid ∧ u.pre.wf=true:=by
    intro u hu
    obtain ⟨b,hb',rfl⟩:=List.mem_map.mp hu
    exact ⟨(hb b hb').1.1,(hb b hb').2.2⟩
  have hup:=scheduler_compact_digest_count (bs.map NativeBlock.witness) insts
    (by simpa using hsize) hv hi hcap tu pub msg
  have hcodec:=native_codec_digest_count bs hlen (fun b h=>⟨(hb b h).1,(hb b h).2.1⟩) ho tc pub msg
  rw [repaired_digest_count]
  rw [hup,hcodec]
  simp only [Sha.Gen.expectedDigests,List.filter_append,List.map_append,List.count_append]

end ZkFormal.NearV3.Assembly
