import ZkFormal.NearV3.Candidates.ProcPriorIdComparisonPair
import ZkFormal.NearV3.Assembly.SchedulerPriorCore
namespace ZkFormal.NearV3.Candidates.ProcPriorIdComparisonValid
open ZkFormal.NearV3.Assembly.CodecDigest
open ZkFormal.NearV3.Sched.Complete
open ProcIdTaggedCells ProcPriorComparisonRequests ProcPriorIdStrictOrder

theorem bounds (bs : List NativeBlock) (hv:∀b∈bs,b.Valid)
    (hn:∀b∈bs,b.pub.ids.length≤64) (hi:∀b∈bs,∀id∈b.pub.ids,id<2^64)
    (hlen:bs.length≤32) (ho:∀(i:Nat)(b:NativeBlock),bs[i]?=some b→b.run.tau=i)
    (hraw:(ProcRawConcatGeometry.rows bs).length≤2001184)
    (a : Tagged) (ha:a∈ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs) :
    a.1<32 ∧ a.2.event.key<2^64 ∧ a.2.event.ordinal+1<2^29 := by
  have hab:=ProcIdNativeLocal.bounds (fun b=>b.pub.ids) bs hv hi ho hlen a ha
  refine ⟨hab.1,hab.2,?_⟩
  obtain ⟨b,hb,r,hr,rfl⟩:=ProcIdTaggedRows.mem_origin _ bs a ha
  have hem:r.event∈ProcPriorIds.events b.pub.ids b.old.links:=by
    have hm:=ProcPriorIdRows.rowsFrom_events ⟨none,ProcPriorIdCarry.zero⟩
      (ProcPriorIds.events b.pub.ids b.old.links)
    change (ProcPriorIdRows.rows b.pub.ids b.old.links).map (·.event)=_ at hm
    rw [←hm]
    exact List.mem_map.mpr ⟨r,hr,rfl⟩
  have hs:=ProcPriorIdRanges.event_ordinal _ _ _ hem
  have hcharge:=ProcRawNativeLocal.length_le bs b hb
  have h64:=hn b hb
  unfold ProcRawConcatGeometry.blockLength ProcPriorRawSlots.length at hcharge
  dsimp only
  omega

theorem native (bs : List NativeBlock) (hv:∀b∈bs,b.Valid)
    (hn:∀b∈bs,b.pub.ids.length≤64) (hi:∀b∈bs,∀id∈b.pub.ids,id<2^64)
    (hlen:bs.length≤32) (ho:∀(i:Nat)(b:NativeBlock),bs[i]?=some b→b.run.tau=i)
    (hraw:(ProcRawConcatGeometry.rows bs).length≤2001184) : ∀q∈ids bs,CmpOk q := by
  exact ProcPriorMemoryComparisonValid.adjacent_ok Ordered
    (fun a=>a.1<32 ∧ a.2.event.key<2^64 ∧ a.2.event.ordinal+1<2^29) idPair
    (ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs) (ProcPriorIdStrictOrder.native bs ho)
    (bounds bs hv hn hi hlen ho hraw) ProcPriorIdComparisonPair.pair_ok

/-- Both actual prior comparator inventories are semantically valid for the
same accepted native blocks; duplicate current IDs remain allowed. -/
theorem prepared {B : Nat} {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) : ∀q∈requests bs,CmpOk q := by
  have hpub:∀b∈bs,b.pub∈p.sched:=by
    intro b hb
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
    exact List.mem_iff_getElem?.mpr ⟨i,(hc.indexed i b hi).1.1⟩
  have hn:∀b∈bs,b.pub.ids.length≤64:=fun b hb=>(ZkFormal.NearV3.Sched.prepD0_sched hp b.pub (hpub b hb)).n64
  have hi:∀b∈bs,∀id∈b.pub.ids,id<2^64:=fun b hb=>ZkFormal.NearV3.Sched.prepD0_ids64 hp b.pub (hpub b hb)
  have ho:∀(i:Nat)(b:NativeBlock),bs[i]?=some b→b.run.tau=i:=fun i b hb=>(hc.indexed i b hb).2.1
  have hr:(ProcRawConcatGeometry.rows bs).length≤2001184:=by have:=hc.raw_bound;omega
  intro q hq
  rcases List.mem_append.mp hq with hm|hi'
  · exact ProcPriorMemoryComparisonValid.native bs hn hc.length ho hr q hm
  · exact native bs (fun b hb=>(hc.valid b hb).1) hn hi hc.length ho hr q hi'
end ZkFormal.NearV3.Candidates.ProcPriorIdComparisonValid
