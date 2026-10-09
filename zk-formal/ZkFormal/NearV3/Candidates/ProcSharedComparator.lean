import ZkFormal.NearV3.Candidates.ProcPriorComparisonBudget
namespace ZkFormal.NearV3.Candidates.ProcSharedComparator
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Complete
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcPriorComparisonRequests

def requests (old : List Request) (bs : List NativeBlock) :=old++ProcPriorComparisonRequests.requests bs
def trace (old : List Request) (bs : List NativeBlock) :=CmpHeight.trace (requests old bs)

theorem capacity (old : List Request) (bs : List NativeBlock)
    (hold:old.length≤3090136) (hn:∀b∈bs,b.pub.ids.length≤64)
    (hlen:bs.length≤32) (hraw:(ProcRawConcatGeometry.rows bs).length≤2001184) :
    (requests old bs).length≤2^22 := by
  have hp:=ProcPriorComparisonBudget.capacity bs hn hlen hraw
  simp only [requests,List.length_append]
  omega

/-- Existing fixed-height comparator renderer accepts the combined inventory;
its semantic comparison validity is kept explicit until native order/range
and scheduler inventory extraction discharge it. -/
theorem local_table (old : List Request) (bs : List NativeBlock)
    (hok:∀q∈requests old bs,CmpOk q) (t : Nat) (pub : List Fp) :
    TableLocal (Cmp.table B_SCMP) (trace old bs) t pub := by
  refine ⟨by change 1≤22;decide,by change 22≤22;decide,?_,?_⟩
  · exact CmpHeight.cmp_constraints (requests old bs) hok t pub
  · exact fun r hr=>CmpHeight.cmp_bits (requests old bs) B_SCMP t r pub hr

theorem receive_count (old : List Request) (bs : List NativeBlock)
    (hcap:(requests old bs).length≤2^22) (t : Nat) (pub : List Fp) (msg : List Fp) :
    tableBusCount (Cmp.interactions B_SCMP) (trace old bs) t pub B_SCMP false msg=
      (old.map cmpMsg).count msg+(ProcPriorComparisonRequests.requests bs |>.map cmpMsg).count msg := by
  unfold trace
  rw [CmpHeight.cmp_count (requests old bs) B_SCMP t pub msg false hcap]
  simp only [ite_true,fmsgs_expected,requests,List.map_append,List.count_append]

theorem send_count (old : List Request) (bs : List NativeBlock)
    (hcap:(requests old bs).length≤2^22) (t : Nat) (pub : List Fp) (msg : List Fp) :
    tableBusCount (Cmp.interactions B_SCMP) (trace old bs) t pub B_SCMP true msg=0 := by
  exact CmpHeight.cmp_count (requests old bs) B_SCMP t pub msg true hcap
end ZkFormal.NearV3.Candidates.ProcSharedComparator
