import ZkFormal.NearV3.Candidates.GatedLengthFusion
import ZkFormal.NearV3.Candidates.ProcPriorRawFrame
namespace ZkFormal.NearV3.Candidates.RawFrameFusion
open ZkFormal.Air HorizontalProfile
open HorizontalTables (fuse)

def memory : Air.Table := ProcPriorRawFrame.table Sched.B_S0F 73 B_VBYTES 74 75
def selected : List Air.Table := GatedLengthFusion.selected++[memory]
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem fused_aux_degree : (fuse selected).auxDegree 2=8 := by
  rw [auxDegree_eq,fuse_profiles]
  decide +kernel

theorem selected_constraints : selected.all (fun T=>T.allConstraints.all
    (fun e=>decide (e.degree≤8)))=true := by
  apply List.all_eq_true.mpr
  intro T hT
  rcases List.mem_append.mp hT with ho|hn
  · exact List.all_eq_true.mp GatedLengthFusion.selected_constraints T ho
  · have ht : T=memory:=List.mem_singleton.mp hn
    subst T
    decide +kernel

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

theorem fused_width : (fuse selected).width=3428 := by
  change ((GatedLengthFusion.selected++[memory]).map (·.width)).sum=3428
  rw [List.map_append,List.sum_append]
  change (fuse GatedLengthFusion.selected).width+_=3428
  rw [GatedLengthFusion.fused_width]
  decide +kernel

private theorem shape_from (T : Air.Table) (hw : T.width=3428)
    (hd : T.degree 2=8)
    (hp : profiles T=selected.flatMap profiles)
    (hl : T.maxLog=22) : ZkFormal.Size.shapeOf 2 T=⟨3428,115,7,115,22⟩ := by
  unfold ZkFormal.Size.shapeOf Table.quotCount
  rw [hd,auxCount_eq,numSide_eq,numSide_eq,hp,hw,hl]
  decide +kernel

theorem fused_shape : ZkFormal.Size.shapeOf 2 (fuse selected)=⟨3428,115,7,115,22⟩ := by
  apply shape_from _ fused_width fused_degree _ rfl
  rw [fuse_profiles]
/-- Concrete size proposal only: extra buses are provisional and parser/ID
record joins plus full execution admission remain outside this inventory. -/
def tables : List Air.Table := fuse selected::HorizontalAccounts.rest

def bytes : Nat := ZkFormal.Size.sizeOfWeq (ZkFormal.V2.G.pg 2)
  (tables.map (ZkFormal.Size.shapeOf 2))

theorem bytes_exact : bytes=8403188 := by
  unfold bytes
  simp only [tables,List.map_cons,fused_shape,HorizontalAccounts.rest_shapes]
  decide +kernel

theorem excess : bytes-8388608=14580 := by rw [bytes_exact]

theorem over_limit : 8388608<bytes := by rw [bytes_exact];decide

end ZkFormal.NearV3.Candidates.RawFrameFusion
