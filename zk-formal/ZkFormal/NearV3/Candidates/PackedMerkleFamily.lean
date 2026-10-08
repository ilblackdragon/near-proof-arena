import ZkFormal.NearV3.Candidates.PackedFamily
import ZkFormal.NearV3.Candidates.MerkleEmpty

/-! Packed SHA plus the actual empty/nonempty Merkle repair. Not admitted. -/
namespace ZkFormal.NearV3.Candidates.PackedMerkleFamily
open ZkFormal.Air ZkFormal.Size

def tables (n : Nat) : List Air.Table :=
  List.replicate n (ShaCarryKinds.table ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST) ++
    (CurrentFamily.tables.drop 4).set 23 MerkleEmpty.table

def air (n : Nat) : Air := ⟨tables n,67,202⟩
def bytes (n : Nat) : Nat := sizeOfWeq (ZkFormal.V2.G.pg 2) ((tables n).map (shapeOf 2))

theorem actual_model (n : Nat) : sizeMaxDedup (air n) (ZkFormal.V2.G.pg 2)=bytes n :=
  sizeMaxDedup_eq_model (air n) (ZkFormal.V2.G.pg 2)

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem merkle_shape : shapeOf 2 MerkleEmpty.table=⟨60,3,7,3,19⟩ := by decide +kernel

theorem four_wf : (tables 4).all (fun t => t.wf (air 4) 8)=true := by decide +kernel
theorem shapes (n : Nat) : (tables n).map (shapeOf 2)=
    List.replicate n (⟨512,9,5,9,22⟩:TShape) ++
      ((CurrentFamily.shapes 2).drop 4).set 23 ⟨60,3,7,3,19⟩ := by
  simp [tables,List.map_append,List.map_replicate,List.map_set,List.map_drop,
    PackedFamily.sha_shape,merkle_shape,CurrentFamily.shapes]

theorem bytes_four : bytes 4=9395334 := by
  unfold bytes
  rw [shapes,CurrentFamily.shapes_two]
  decide +kernel

theorem bytes_three : bytes 3=8822405 := by
  unfold bytes
  rw [shapes,CurrentFamily.shapes_two]
  decide +kernel
end ZkFormal.NearV3.Candidates.PackedMerkleFamily
