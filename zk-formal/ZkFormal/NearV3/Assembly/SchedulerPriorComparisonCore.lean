import ZkFormal.NearV3.Assembly.SchedulerPriorCore
import ZkFormal.NearV3.Assembly.SchedulerCodecComparisonRecords
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
/-- One accepted native execution supplies all components and joins on the
SAME allocated block list; no independently chosen witnesses are reconciled. -/
theorem accepted_prior_comparison_core {B : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w)
    (h:checkD0a B cb wb=.ok ()) (hB:B≤2000000) :
    ∃bs,PriorCore p B bs ∧ (∀b∈bs,∀q∈b.output.cmps,Sched.Complete.CmpOk q) := by
  obtain ⟨bs,hcmps,hlen,hforest,hvalid,hindex,hraw,hlocal,hpresence,hrecord,_⟩:=accepted_comparison_record_tables hp hk hw h hB
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
    id_data:=?_ },hcmps⟩
  exact fun req=>ProcNativeIdBalance.balance req (fun b=>b.pub.ids) bs (by omega)
    (Nat.le_of_lt (ProcNativeIdBalance.native_capacity _ bs hn hlen hcapraw))
end ZkFormal.NearV3.Assembly.CodecDigest
