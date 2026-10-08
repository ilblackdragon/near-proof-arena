import ZkFormal.NearV3.Candidates.CmpHeight
import ZkFormal.NearV3.Candidates.MemHeightTraffic
import ZkFormal.Near.Extract.Common
namespace ZkFormal.NearV3.Candidates.SchedLocalHeight
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete

theorem cmp_local (cmps : List (Nat × Nat × Nat)) (hok : ∀ q ∈ cmps, CmpOk q)
    (bus t : Nat) (pub : List Fp) : TableLocal (Cmp.table bus) (CmpHeight.trace cmps) t pub := by
  exact ⟨by change 1≤22; decide, by change 22≤22; decide, fun r hr=>CmpHeight.cmp_constraints cmps hok t pub r hr,
    fun r hr=>CmpHeight.cmp_bits cmps bus t r pub hr⟩

theorem mem_local (R : Run) (hg : ∀ g ∈ R.segs, SegOk g)
    (hrows : (memVs R.segs).length + 1 ≤ 2^22) (t : Nat) (pub : List Fp) :
    TableLocal Mem.table (MemHeight.trace R) t pub := by
  exact ⟨by change 1≤22; decide, by change 22≤22; decide, fun r hr=>MemHeight.mem_constraints R hg hrows t pub r hr,
    fun r hr=>MemHeight.mem_bits R hg t r pub hr⟩
end ZkFormal.NearV3.Candidates.SchedLocalHeight
