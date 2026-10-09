import ZkFormal.NearV3.Candidates.ProcKindHeight
import ZkFormal.NearV3.Candidates.ProcKeyInverse
namespace ZkFormal.NearV3.Candidates.ProcKeyRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcHeightBits ProcNativeRows ProcKindHeight

theorem at_key (R : Run) (k : Nat) (hk : k<16) : atRow R k=keyV R k := by
  rw [atRow,dif_pos (by rw [procVs_length]; omega)]
  simp [procVs,keyVs,List.getElem_append,hk]

theorem key_cell (R : Run) (t k c : Nat) (hk : k<16) :
    (trace R).cell t k c=Fp.ofNat ((keyV R k).cell c) := by
  rw [cell_cast,at_key R k hk]

theorem flag_cast (k : Nat) : Fp.ofNat (b2n (k==15))=if k=15 then 1 else 0 := by
  by_cases h : k=15 <;> simp [b2n,h] <;> rfl

end ZkFormal.NearV3.Candidates.ProcKeyRows
