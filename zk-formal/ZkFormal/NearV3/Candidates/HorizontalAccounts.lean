import ZkFormal.NearV3.Candidates.HorizontalTables
import ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty

/-! Empty-account compatible horizontal inventory. Shape unchanged; full honest
trace construction and global SHA placement remain independent obligations. -/
namespace ZkFormal.NearV3.Candidates.HorizontalAccounts
open ZkFormal.Air ZkFormal.Size

def rest : List Air.Table := HorizontalTables.rest.set 5 Rcpt.Candidates.AccountEmpty.table
def tables : List Air.Table := HorizontalTables.fuse HorizontalTables.selected :: rest
def air : Air := ⟨tables,67,202⟩
def bytes : Nat := sizeOfWeq (ZkFormal.V2.G.pg 2) (tables.map (shapeOf 2))

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem account_shape : shapeOf 2 Rcpt.Candidates.AccountEmpty.table=⟨16,7,5,7,17⟩ := by
  decide +kernel

theorem rest_shapes : rest.map (shapeOf 2)=
  [⟨73,4,5,4,11⟩,⟨56,4,5,4,21⟩,⟨272,2,5,2,21⟩,⟨137,2,3,2,20⟩,
   ⟨77,4,6,4,20⟩,⟨16,7,5,7,17⟩,⟨7,2,5,2,16⟩,⟨6,2,5,2,13⟩,
   ⟨33,1,3,1,2⟩,⟨60,3,7,3,19⟩,⟨49,1,3,1,18⟩] := by
  decide +kernel

theorem actual_model : sizeMaxDedup air (ZkFormal.V2.G.pg 2)=bytes :=
  sizeMaxDedup_eq_model air (ZkFormal.V2.G.pg 2)
end ZkFormal.NearV3.Candidates.HorizontalAccounts
