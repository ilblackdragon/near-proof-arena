import ZkFormal.NearV3.Candidates.GatedLengthFusion
import ZkFormal.NearV3.Candidates.ProcPriorVertical
import ZkFormal.NearV3.Candidates.InteractionPairing
namespace ZkFormal.NearV3.Candidates.VerticalPriorFusion
open ZkFormal.Air HorizontalProfile

def selected : List Air.Table:=GatedLengthFusion.selected.take 19++[ProcPriorVertical.table]
def raw : Air.Table:=HorizontalTables.fuse selected
def table : Air.Table:={raw with interactions:=InteractionPairing.reorder raw.interactions}
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem width : table.width=3401 := by decide +kernel
theorem aux_degree : table.auxDegree 2=8 := by decide +kernel
theorem degree : table.degree 2=8 := by decide +kernel

/-- Interaction reordering preserves every bus count, including multiplicity. -/
theorem traffic (tr : Trace Algebra.Fp) (t : Nat) (pub : List Algebra.Fp)
    (bus : Nat) (send : Bool) (msg : List Algebra.Fp) :
    tableBusCount table.interactions tr t pub bus send msg=
      tableBusCount raw.interactions tr t pub bus send msg :=
  InteractionPairing.count _ tr t pub bus send msg

theorem local_iff (tr : Trace Algebra.Fp) (t : Nat) (pub : List Algebra.Fp) :
    ZkFormal.Near.TableLocal table tr t pub ↔ ZkFormal.Near.TableLocal raw tr t pub :=
  InteractionPairing.local_iff raw tr t pub

private theorem shape_from (T : Air.Table) (hw : T.width=3401) (hd : T.degree 2=8)
    (hp : profiles T=profiles table) (hl : T.maxLog=22) :
    ZkFormal.Size.shapeOf 2 T=⟨3401,115,7,115,22⟩ := by
  unfold ZkFormal.Size.shapeOf Table.quotCount
  rw [hd,auxCount_eq,numSide_eq,numSide_eq,hp,hw,hl]
  decide +kernel

theorem shape : ZkFormal.Size.shapeOf 2 table=⟨3401,115,7,115,22⟩ :=
  shape_from table width degree rfl rfl

def tables : List Air.Table:=table::HorizontalAccounts.rest
def bytes : Nat:=ZkFormal.Size.sizeOfWeq (ZkFormal.V2.G.pg 2) (tables.map (ZkFormal.Size.shapeOf 2))
theorem bytes_exact : bytes=8378132 := by
  unfold bytes
  simp only [tables,List.map_cons,shape,HorizontalAccounts.rest_shapes]
  decide +kernel

theorem margin : 8388608-bytes=10476 := by rw [bytes_exact]
theorem below_limit : bytes<8388608 := by rw [bytes_exact];decide

end ZkFormal.NearV3.Candidates.VerticalPriorFusion
