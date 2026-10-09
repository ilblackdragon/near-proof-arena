import ZkFormal.NearV3.Candidates.ProcPriorIdComparisonInventory
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Sched.Complete
open ProcPriorComparisonRequests

theorem prior_comparison_counts {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (tm ti : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorMemoryGated.table 67 68 69).interactions
      (ProcPriorMemoryGated.liftTrace (ProcPriorNativeMemory.trace (ProcPriorNativeMemory.allRows bs)) tm pub)
      tm pub 69 true msg+
    tableBusCount (ProcPriorIdTable.interactions 70 71 72 69)
      (ProcIdTaggedTrace.trace (ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs)) ti pub 69 true msg=
      ((requests bs).map cmpMsg).count msg := by
  have hpub:∀b∈bs,b.pub∈p.sched:=by
    intro b hb
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
    exact List.mem_iff_getElem?.mpr ⟨i,(hc.indexed i b hi).1.1⟩
  have hn:∀b∈bs,b.pub.ids.length≤64:=fun b hb=>(prepD0_sched hp b.pub (hpub b hb)).n64
  have hr:(ProcRawConcatGeometry.rows bs).length≤2001184:=by have:=hc.raw_bound;omega
  have hm:=ProcPriorNativeMemory.capacity bs hn hc.length hr
  have hi:(ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs).length<2^22:=by
    rw [ProcIdNativeLocal.length_eq]
    exact ProcNativeIdBalance.native_capacity _ bs hn hc.length hr
  rw [ProcPriorMemoryComparisonInventory.gated_count bs hm,
    ProcPriorIdComparisonInventory.count bs hi]
  simp only [requests,List.map_append,List.count_append]

/-- The same accepted prior witness installs directly into the existing
shared comparator. Only the independent old40 producer inventory and its
capacity/correctness remain inputs to this composition theorem. -/
theorem shared_comparator_local {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (old : List Request) (hok:∀q∈old,CmpOk q) (t : Nat) (pub : List Fp) :
    TableLocal (Cmp.table B_SCMP) (ProcSharedComparator.trace old bs) t pub := by
  apply ProcSharedComparator.local_table
  intro q hq
  rcases List.mem_append.mp hq with hold|hprior
  · exact hok q hold
  · exact ProcPriorIdComparisonValid.prepared hp bs hc hB q hprior

theorem shared_comparator_balance {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (old : List Request) (hold:old.length≤3090136)
    (tc tm ti : Nat) (pub msg : List Fp) :
    tableBusCount (Cmp.interactions B_SCMP) (ProcSharedComparator.trace old bs) tc pub B_SCMP false msg=
      (old.map cmpMsg).count msg+
      (tableBusCount (ProcPriorMemoryGated.table 67 68 69).interactions
        (ProcPriorMemoryGated.liftTrace (ProcPriorNativeMemory.trace (ProcPriorNativeMemory.allRows bs)) tm pub)
        tm pub 69 true msg+
      tableBusCount (ProcPriorIdTable.interactions 70 71 72 69)
        (ProcIdTaggedTrace.trace (ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs)) ti pub 69 true msg) := by
  have hn:∀b∈bs,b.pub.ids.length≤64:=by
    intro b hb
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
    exact (prepD0_sched hp b.pub (List.mem_iff_getElem?.mpr ⟨i,(hc.indexed i b hi).1.1⟩)).n64
  have hr:(ProcRawConcatGeometry.rows bs).length≤2001184:=by have:=hc.raw_bound;omega
  rw [ProcSharedComparator.receive_count old bs (ProcSharedComparator.capacity old bs hold hn hc.length hr),
    prior_comparison_counts hp bs hc hB]
end ZkFormal.NearV3.Assembly.CodecDigest
