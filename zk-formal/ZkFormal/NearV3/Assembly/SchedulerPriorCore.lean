import ZkFormal.NearV3.Assembly.SchedulerCodecAcceptedRecords
import ZkFormal.NearV3.Candidates.ProcPriorNativeMemoryWriteBalance
import ZkFormal.NearV3.Candidates.ProcPriorNativeMemoryComplete
import ZkFormal.NearV3.Candidates.ProcNativeIdBalance
import ZkFormal.NearV3.Candidates.ProcPriorOverlayBudget
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- A common witness for the checked prior-state components and natural-count
joins. This is not whole-family HoldsP: ID Local, public-ID/comparator providers
and shared vertical clock installation are separate obligations. -/
structure PriorCore (p : Prep) (B : Nat) (bs : List NativeBlock) : Prop where
  length : bs.length≤32
  forest : preBytes (bs.map (fun b=>b.witness.pre))≤B
  valid : ∀b∈bs,b.Valid ∧ b.run.n≤64
  indexed : ∀(i : Nat)(b : NativeBlock),bs[i]?=some b→PreparedRun p i b ∧ b.run.tau=i ∧
    b.vid=priorValueId ((bs.map (fun b=>b.witness.pre)).take i) b.witness.pre
  raw_bound : (ProcRawConcatGeometry.rows bs).length≤B+1184
  overlay_bound : ProcPriorOverlayBudget.occupied bs+4≤3134900
  codec_local : ∀t pub,TableLocal ProcPriorCodecActual.table
    (SchedHeight.trace (nativeBlockRows bs) codecPad) t pub
  raw_local : ∀t pub,TableLocal (ProcPriorRawFrame.table B_SPOST 73 B_VBYTES 74 75)
    (ProcRawConcatGeometry.trace bs) t pub
  record_local : ∀t pub,TableLocal (ProcPriorRecordLinear.table 75 71 72 67 76)
    (ProcRecordConcatTraffic.trace (fun b=>b.pub.ids) bs) t pub
  memory_local : ∀t pub,TableLocal (ProcPriorMemoryGated.table 67 68 69)
    (ProcPriorMemoryGated.liftTrace (ProcPriorNativeMemory.trace (ProcPriorNativeMemory.allRows bs)) t pub) t pub
  presence : ∀t pub msg,tableBusCount ProcPriorCodecActual.table.interactions
    (SchedHeight.trace (nativeBlockRows bs) codecPad) t pub B_SPOST true msg=
    tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (ProcRawConcatGeometry.trace bs) t pub B_SPOST false msg
  raw_record : ∀t pub msg,tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
    (ProcRawConcatGeometry.trace bs) t pub 75 true msg=
    tableBusCount (ProcPriorRecordLinear.table 75 71 72 67 76).interactions
      (ProcRecordConcatTraffic.trace (fun b=>b.pub.ids) bs) t pub 75 false msg
  memory_read : ∀tm tc pub msg,tableBusCount (ProcPriorMemoryGated.table 67 68 69).interactions
    (ProcPriorMemoryGated.liftTrace (ProcPriorNativeMemory.trace (ProcPriorNativeMemory.allRows bs)) tm pub)
    tm pub 68 true msg=tableBusCount ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) tc pub 68 false msg
  memory_write : ∀tm tr pub msg,tableBusCount (ProcPriorMemoryGated.table 67 68 69).interactions
    (ProcPriorMemoryGated.liftTrace (ProcPriorNativeMemory.trace (ProcPriorNativeMemory.allRows bs)) tm pub)
    tm pub 67 false msg=tableBusCount (ProcPriorRecordLinear.interactions 75 71 72 67 76)
      (ProcRecordConcatTraffic.trace (fun b=>b.pub.ids) bs) tr pub 67 true msg
  id_data : ∀req t pub msg,tableBusCount (ProcPriorRecordLinear.interactions 75 71 72 67 76)
    (ProcRecordConcatTraffic.trace (fun b=>b.pub.ids) bs) t pub (if req then 71 else 72) req msg=
    tableBusCount (ProcPriorIdTable.interactions 70 71 72 69)
      (ProcIdConcatTraffic.trace (fun b=>b.pub.ids) bs) t pub (if req then 71 else 72) (!req) msg

/-- One accepted native execution supplies all components and joins on the
SAME allocated block list; no independently chosen witnesses are reconciled. -/
theorem accepted_prior_core {B : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w)
    (h:checkD0a B cb wb=.ok ()) (hB:B≤2000000) :
    ∃bs,PriorCore p B bs := by
  obtain ⟨bs,hlen,hforest,hvalid,hindex,hraw,hlocal,hpresence,hrecord,_⟩:=accepted_record_tables hp hk hw h hB
  have hb:∀b∈bs,b.Valid ∧ b.pub∈p.sched ∧
      ∃tauV,ActualRun.run (ProcPreparedSequence.input b.pub b.old) tauV=.ok b.run := by
    intro b hm
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hm
    have hr:=(hindex i b hi).1
    exact ⟨(hvalid b hm).1,List.mem_iff_getElem?.mpr ⟨i,hr.1⟩,i,hr.2⟩
  have hn:∀b∈bs,b.pub.ids.length≤64:=fun b hm=>(prepD0_sched hp b.pub (hb b hm).2.1).n64
  have ho:∀(i:Nat)(b:NativeBlock),bs[i]?=some b→b.run.tau=i:=fun i b hi=>(hindex i b hi).2.1
  have hcapraw:(ProcRawConcatGeometry.rows bs).length≤2001184:=by omega
  refine ⟨bs,{
    length:=hlen,forest:=hforest,valid:=hvalid,indexed:=hindex,raw_bound:=hraw,
    overlay_bound:=(ProcPriorOverlayBudget.capacity bs hn hlen hcapraw).1,
    codec_local:=fun t pub=>(hlocal t pub).1,
    raw_local:=fun t pub=>(hlocal t pub).2.1,
    record_local:=fun t pub=>(hlocal t pub).2.2,
    memory_local:=fun t pub=>ProcPriorNativeMemory.native_gated_local bs hn hlen ho hcapraw t 67 68 69 pub,
    presence:=hpresence,raw_record:=hrecord,
    memory_read:=ProcPriorNativeMemory.codec_balance hp bs hlen hb hcapraw,
    memory_write:=ProcPriorNativeMemory.record_balance bs hn hlen hcapraw,
    id_data:=?_ }⟩
  exact fun req=>ProcNativeIdBalance.balance req (fun b=>b.pub.ids) bs (by omega)
    (Nat.le_of_lt (ProcNativeIdBalance.native_capacity _ bs hn hlen hcapraw))
end ZkFormal.NearV3.Assembly.CodecDigest
