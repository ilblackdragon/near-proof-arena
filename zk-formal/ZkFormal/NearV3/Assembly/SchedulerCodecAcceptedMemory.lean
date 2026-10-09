import ZkFormal.NearV3.Assembly.SchedulerCodecAcceptedQueries
import ZkFormal.NearV3.Candidates.ProcPriorNativeMemoryComplete
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- The SAME accepted forest-allocated blocks construct legal Codec, raw
parser and packed-address memory traces with exact prior-query balance.
The shared vertical installation and comparator provider are not assumed. -/
theorem accepted_allocated_memory {B : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w)
    (h:checkD0a B cb wb=.ok ()) (hB:B≤2000000) :
    ∃bs : List NativeBlock,bs.length≤32 ∧ preBytes (bs.map (fun b=>b.witness.pre))≤B ∧
      (∀b∈bs,b.Valid ∧ b.run.n≤64) ∧
      (∀(i:Nat)(b:NativeBlock),bs[i]?=some b→PreparedRun p i b ∧ b.run.tau=i ∧
        b.vid=priorValueId ((bs.map (fun b=>b.witness.pre)).take i) b.witness.pre) ∧
      (ProcPriorNativeMemory.allRows bs).length<2^22 ∧
      (∀time pub,TableLocal ProcPriorCodecActual.table
        (SchedHeight.trace (nativeBlockRows bs) codecPad) time pub ∧
        TableLocal (ProcPriorRawFrame.table B_SPOST 73 B_VBYTES 74 75)
          (ProcRawConcatGeometry.trace bs) time pub ∧
        TableLocal (ProcPriorMemoryGated.table 67 68 69)
          (ProcPriorMemoryGated.liftTrace (ProcPriorNativeMemory.trace (ProcPriorNativeMemory.allRows bs)) time pub) time pub) ∧
      ∀tm tc pub msg,tableBusCount (ProcPriorMemoryGated.table 67 68 69).interactions
        (ProcPriorMemoryGated.liftTrace (ProcPriorNativeMemory.trace (ProcPriorNativeMemory.allRows bs)) tm pub)
        tm pub 68 true msg=
        tableBusCount ProcPriorCodecActual.table.interactions
          (SchedHeight.trace (nativeBlockRows bs) codecPad) tc pub 68 false msg := by
  obtain ⟨bs,hlen,hforest,hvalid,hindex,hraw,hlocal,_,_⟩:=accepted_allocated_queries hp hk hw h hB
  have hb:∀b∈bs,b.Valid ∧ b.pub∈p.sched ∧
      ∃tauV,ActualRun.run (ProcPreparedSequence.input b.pub b.old) tauV=.ok b.run := by
    intro b hm
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hm
    have hr:=(hindex i b hi).1
    exact ⟨(hvalid b hm).1,List.mem_iff_getElem?.mpr ⟨i,hr.1⟩,i,hr.2⟩
  have hn:∀b∈bs,b.pub.ids.length≤64:=fun b hm=>(prepD0_sched hp b.pub (hb b hm).2.1).n64
  have ho:∀(i:Nat)(b:NativeBlock),bs[i]?=some b→b.run.tau=i:=fun i b hi=>(hindex i b hi).2.1
  have hcapraw:(ProcRawConcatGeometry.rows bs).length≤2001184:=by omega
  refine ⟨bs,hlen,hforest,hvalid,hindex,ProcPriorNativeMemory.capacity bs hn hlen hcapraw,?_,?_⟩
  · intro time pub
    exact ⟨(hlocal time pub).1,(hlocal time pub).2,
      ProcPriorNativeMemory.native_gated_local bs hn hlen ho hcapraw time 67 68 69 pub⟩
  · exact ProcPriorNativeMemory.codec_balance hp bs hlen hb hcapraw
end ZkFormal.NearV3.Assembly.CodecDigest
