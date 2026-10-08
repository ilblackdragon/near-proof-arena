import ZkFormal.NearV3.Candidates.GatedIdFusion
import ZkFormal.NearV3.Candidates.ProcPriorValueLength
import ZkFormal.NearV3.Candidates.ProcPriorIdTable
namespace ZkFormal.NearV3.Candidates.GatedLengthFusion
open ZkFormal.Air HorizontalProfile
open HorizontalTables (fuse)

def selected : List Air.Table := GatedIdFusion.selected.set 5 (ProcPriorValueLength.table 73)

theorem value_slot : GatedIdFusion.selected[5]?=some Rcpt.Candidates.SizeCount.valTable := by rfl
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem fused_aux_degree : (fuse selected).auxDegree 2=8 := by
  rw [auxDegree_eq,fuse_profiles]
  decide +kernel

theorem selected_constraints : selected.all (fun T=>T.allConstraints.all
    (fun e=>decide (e.degree≤8)))=true := by
  apply List.all_eq_true.mpr
  intro T hT
  rcases List.mem_or_eq_of_mem_set hT with ho|rfl
  · exact List.all_eq_true.mp GatedIdFusion.selected_constraints T ho
  · decide +kernel

theorem fused_degree : (fuse selected).degree 2=8 := by
  have hc : ∀ e∈(fuse selected).allConstraints, e.degree≤8 :=
    fused_constraint_bound selected 8 (by
      intro T hT e he
      exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp selected_constraints T hT) e he))
  have fold : ∀ xs : List Nat, (∀ x∈xs,x≤8)→xs.foldr max 2≤8 := by
    intro xs
    induction xs with
    | nil => intro _; decide
    | cons x xs ih => intro h; exact Nat.max_le.mpr ⟨h x (by simp), ih (by intro y hy; exact h y (by simp [hy]))⟩
  unfold Table.degree
  rw [fused_aux_degree]
  exact Nat.max_eq_left (fold _ (by intro x hx; obtain ⟨e,he,rfl⟩:=List.mem_map.mp hx; exact hc e he))

theorem fused_width : (fuse selected).width=3405 := by decide +kernel

private theorem shape_from (T : Air.Table) (hw : T.width=3405)
    (hd : T.degree 2=8)
    (hp : profiles T=selected.flatMap profiles)
    (hl : T.maxLog=22) : ZkFormal.Size.shapeOf 2 T=⟨3405,112,7,112,22⟩ := by
  unfold ZkFormal.Size.shapeOf Table.quotCount
  rw [hd,auxCount_eq,numSide_eq,numSide_eq,hp,hw,hl]
  decide +kernel

theorem fused_shape : ZkFormal.Size.shapeOf 2 (fuse selected)=⟨3405,112,7,112,22⟩ := by
  apply shape_from _ fused_width fused_degree _ rfl
  rw [fuse_profiles]
/-- Concrete size proposal only: extra buses are provisional and parser/ID
renderer repairs plus full execution admission remain outside this inventory. -/
def tables : List Air.Table := fuse selected::HorizontalAccounts.rest

def bytes : Nat := ZkFormal.Size.sizeOfWeq (ZkFormal.V2.G.pg 2)
  (tables.map (ZkFormal.Size.shapeOf 2))

theorem bytes_exact : bytes=8360820 := by
  unfold bytes
  simp only [tables,List.map_cons,fused_shape,HorizontalAccounts.rest_shapes]
  decide +kernel

theorem headroom : 8388608-bytes=27788 := by rw [bytes_exact]

theorem below_limit : bytes<8388608 := by rw [bytes_exact];decide

end ZkFormal.NearV3.Candidates.GatedLengthFusion
