import ZkFormal.NearV3.Assembly.SchedulerPriorId
import ZkFormal.NearV3.Candidates.ProcNativePublicIdBalance
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Public ID traffic is balanced for any common accepted block witness,
so this result composes with the concrete overlay without choosing new blocks. -/
theorem PriorCore.public_id {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) {bs : List NativeBlock}
    (hc:PriorCore p B bs) (hB:B≤2000000) (tc ti : Nat) (pub msg : List Fp) :
    tableBusCount ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) tc pub 70 true msg=
    tableBusCount (ProcPriorIdTable.interactions 70 71 72 69)
      (ProcIdTaggedTrace.trace (ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs)) ti pub 70 false msg := by
  have hb:∀b∈bs,b.Valid ∧ b.pub∈p.sched ∧
      ∃tauV,ActualRun.run (ProcPreparedSequence.input b.pub b.old) tauV=.ok b.run := by
    intro b hm
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hm
    have hr:=(hc.indexed i b hi).1
    exact ⟨(hc.valid b hm).1,List.mem_iff_getElem?.mpr ⟨i,hr.1⟩,i,hr.2⟩
  have hraw:(ProcRawConcatGeometry.rows bs).length≤2001184:=by
    have :=hc.raw_bound
    omega
  exact ProcNativePublicIdBalance.balance hp bs hc.length hb hraw tc ti pub msg
end ZkFormal.NearV3.Assembly.CodecDigest
