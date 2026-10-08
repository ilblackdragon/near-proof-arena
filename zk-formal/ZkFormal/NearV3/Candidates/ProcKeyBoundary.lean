import ZkFormal.NearV3.Candidates.ProcKeyInterior
namespace ZkFormal.NearV3.Candidates.ProcKeyBoundary
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcHeightBits ProcNativeRows ProcKindHeight ProcKeyRows

theorem after_key (R : Run) :
    atRow R 16=match R.rounds with | []=>tailV R | rd::_=>hdrV R rd := by
  cases h : R.rounds with
  | nil => simp [atRow,procVs,keyVs,h]
  | cons rd rds =>
    have hlen : 16<(procVs R).length := by
      rw [procVs_length]
      simp only [h,List.map_cons,List.sum_cons]
      omega
    rw [atRow,dif_pos hlen]
    simp [procVs,keyVs,h,roundVs,List.getElem_append]

theorem after_key_kind (R : Run) : (atRow R 16).kK=0 := by
  rw [after_key]
  cases R.rounds <;> rfl

theorem after_key_limb (R : Run) (i : Nat) (hi : i<16) :
    (atRow R 16).cell (Proc.colL i)=keyLimb R.seed i := by
  rw [ProcKeyRotate.limb_cell _ i hi,after_key]
  cases R.rounds <;> simp [tailV,hdrV,baseV,Nat.mod_eq_of_lt hi]

/-- Key-register rotation at the boundary enters a round header or the real tail row. -/
theorem boundary_rotation (R : Run) (i : Nat) (hi : i<16) :
    (atRow R 16).cell (Proc.colL i)=(keyV R 15).cell (Proc.colL ((i+1)%16)) := by
  rw [after_key_limb R i hi,ProcKeyRotate.limb_cell _ _ (Nat.mod_lt _ (by decide))]
  change keyLimb R.seed i=keyLimb R.seed ((((i+1)%16)+15)%16)
  congr 1
  omega
end ZkFormal.NearV3.Candidates.ProcKeyBoundary
