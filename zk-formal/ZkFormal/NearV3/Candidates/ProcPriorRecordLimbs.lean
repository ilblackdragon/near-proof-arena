import ZkFormal.NearV3.Candidates.ProcPriorRecordRows
import ZkFormal.NearV3.Candidates.ProcPriorIdLimbs
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordLimbs
open NearSpec

def digit (v i : Nat) : Nat:=((u64 v).getD i 0).toNat

theorem digit_bound (v i : Nat) : digit v i<256 := UInt8.toNat_lt _

theorem lo_bytes (v : Nat) :
    ProcPriorIdLimbs.lo v=digit v 0+256*digit v 1+65536*digit v 2 := by
  simp [digit,u64,leN,UInt8.toNat_ofNat',ProcPriorIdLimbs.lo]
  omega

theorem mid_bytes (v : Nat) :
    ProcPriorIdLimbs.mid v=digit v 3+256*digit v 4+65536*digit v 5 := by
  simp [digit,u64,leN,UInt8.toNat_ofNat',ProcPriorIdLimbs.mid]
  omega

theorem hi_bytes (v : Nat) (hv:v<18446744073709551616) :
    ProcPriorIdLimbs.hi v=digit v 6+256*digit v 7 := by
  simp [digit,u64,leN,UInt8.toNat_ofNat',ProcPriorIdLimbs.hi]
  omega

theorem high_sum_bound (v : Nat) (hv:v<18446744073709551616) :
    ProcPriorIdLimbs.mid v+ProcPriorIdLimbs.hi v<16842752 := by
  obtain ⟨_,hm,hh⟩:=ProcPriorIdLimbs.bounds v hv
  omega

theorem big_exact (v : Nat) :
    decide (ProcPriorIdLimbs.mid v+ProcPriorIdLimbs.hi v≠0)=ProcPriorSummary.big v := by
  have hr:=ProcPriorIdLimbs.reconstruct v
  have hl:ProcPriorIdLimbs.lo v<16777216:=Nat.mod_lt _ (by decide +kernel)
  unfold ProcPriorSummary.big
  congr 1
  apply propext
  omega

end ZkFormal.NearV3.Candidates.ProcPriorRecordLimbs
