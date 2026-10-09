import ZkFormal.NearV3.Assembly.SchedulerPriorCore
import ZkFormal.NearV3.Candidates.ProcIdNativeLocal
import ZkFormal.NearV3.Candidates.ProcIdTaggedTraffic
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Extend the common accepted witness with the repaired, locally valid ID
trace and both data joins. No supplied ID ranges or boundary metadata. -/
theorem accepted_prior_id {B : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w)
    (h:checkD0a B cb wb=.ok ()) (hB:B≤2000000) :
    ∃bs,PriorCore p B bs ∧
      (∀t pub,TableLocal (ProcPriorIdTable.table 70 71 72 69)
        (ProcIdTaggedTrace.trace (ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs)) t pub) ∧
      ∀req t pub msg,tableBusCount (ProcPriorRecordLinear.interactions 75 71 72 67 76)
        (ProcRecordConcatTraffic.trace (fun b=>b.pub.ids) bs) t pub (if req then 71 else 72) req msg=
        tableBusCount (ProcPriorIdTable.interactions 70 71 72 69)
          (ProcIdTaggedTrace.trace (ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs)) t pub
          (if req then 71 else 72) (!req) msg := by
  obtain ⟨bs,hcore⟩:=accepted_prior_core hp hk hw h hB
  have hpub:∀b∈bs,b.pub∈p.sched := by
    intro b hb
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
    exact List.mem_iff_getElem?.mpr ⟨i,(hcore.indexed i b hi).1.1⟩
  have hn:∀b∈bs,b.pub.ids.length≤64:=fun b hb=>(prepD0_sched hp b.pub (hpub b hb)).n64
  have hraw:(ProcRawConcatGeometry.rows bs).length≤2001184 := by have :=hcore.raw_bound;omega
  have hcap:=ProcNativeIdBalance.native_capacity (fun b=>b.pub.ids) bs hn hcore.length hraw
  refine ⟨bs,hcore,?_,?_⟩
  · exact ProcIdNativeLocal.prepared hp bs (fun b hb=>(hcore.valid b hb).1) hpub
      (fun i b hi=>(hcore.indexed i b hi).2.1) hcore.length hcap
  · exact fun req=>ProcIdTaggedTraffic.balance req (fun b=>b.pub.ids) bs (by omega) (Nat.le_of_lt hcap)
end ZkFormal.NearV3.Assembly.CodecDigest
