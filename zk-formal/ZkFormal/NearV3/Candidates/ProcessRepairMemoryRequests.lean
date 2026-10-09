import ZkFormal.NearV3.Candidates.ProcessRepairComparatorSound
import ZkFormal.NearV3.Candidates.ProcPriorRoutedMemoryRequests
namespace ZkFormal.NearV3.Candidates.ProcessRepairMemoryRequests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedMemoryRequests
theorem compare {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40) (j : Nat) (hj:j=2∨j=3)
    {r : Nat} (hr:r<tr.height 0) (hm:(request j).multNat tr 0 r pub≠0)
    {x y : Fp} (hmsg:(request j).msgVal tr 0 r pub=[x,y,1])
    (hx:x.toNat<2^29) (hy:y.toNat<2^29) :y.toNat≤x.toNat := by
  have ht:0<AP.tables.length := by rw [view.length];decide +kernel
  have hi:request j∈AP.tables[0]!.interactions := by
    rw [view.wires];exact request_member j hj
  have hb:(request j).bus=40 := by rcases hj with rfl|rfl <;> rfl
  have hs:(request j).send=true := by rcases hj with rfl|rfl <;> rfl
  exact ProcessRepairComparatorSound.prior_ge view hpub ht hr hi hb hs hm hmsg hx hy
end ZkFormal.NearV3.Candidates.ProcessRepairMemoryRequests
