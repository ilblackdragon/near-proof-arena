import ZkFormal.NearV3.Candidates.HorizontalCertified
import ZkFormal.NearV3.Candidates.ReceiptRepairedProfile
namespace ZkFormal.NearV3.Candidates.HorizontalReceipt
open ZkFormal.Air ZkFormal.Size
open HorizontalProfile

def selected : List Air.Table := HorizontalTables.selected.set 13 Assembly.ReceiptCandidateRouting.candidateTable
def tables : List Air.Table := HorizontalTables.fuse selected :: HorizontalAccounts.rest
def air : Air := ⟨tables,67,202⟩

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem receipt_slot : HorizontalTables.selected[13]?=some Assembly.RoutingQCandidate.candidateTable := by rfl

private theorem map_replace {α β : Type} (f : α→β) : ∀(xs : List α)(i : Nat)(a b : α),
    xs[i]?=some a→f b=f a→(xs.set i b).map f=xs.map f := by
  intro xs
  induction xs with
  | nil => intro i a b h _;simp at h
  | cons x xs ih =>
    intro i a b h hf
    cases i with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at h;subst a;simp [hf]
    | succ i => simpa using ih i a b h hf

theorem profiles_equal : selected.flatMap profiles=HorizontalTables.selected.flatMap profiles := by
  unfold List.flatMap selected
  rw [map_replace profiles _ 13 Assembly.RoutingQCandidate.candidateTable _ receipt_slot (by rfl)]

theorem widths_equal : (selected.map (·.width)).sum=(HorizontalTables.selected.map (·.width)).sum := by
  unfold selected
  rw [map_replace (fun T : Air.Table=>T.width) _ 13 Assembly.RoutingQCandidate.candidateTable _ receipt_slot (by rfl)]

theorem constraint_bound : selected.all (fun T=>T.allConstraints.all
    (fun e=>decide (e.degree≤8)))=true := by
  apply List.all_eq_true.mpr
  intro T hT
  rcases List.mem_or_eq_of_mem_set hT with ho|rfl
  · exact List.all_eq_true.mp HorizontalAuxCheck.selected_constraints T ho
  · decide +kernel

theorem fused_aux_degree : (HorizontalTables.fuse selected).auxDegree 2=8 := by
  rw [auxDegree_eq,fuse_profiles,profiles_equal]
  have h:=HorizontalAuxCheck.fused_aux_degree
  rw [auxDegree_eq,fuse_profiles] at h
  exact h

theorem fused_degree : (HorizontalTables.fuse selected).degree 2=8 := by
  have hc : ∀e∈(HorizontalTables.fuse selected).allConstraints,e.degree≤8 :=
    fused_constraint_bound selected 8 (by
      intro T hT e he
      exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp constraint_bound T hT) e he))
  have fold : ∀xs : List Nat,(∀x∈xs,x≤8)→xs.foldr max 2≤8 := by
    intro xs
    induction xs with
    | nil => intro _;decide
    | cons x xs ih => intro h;exact Nat.max_le.mpr ⟨h x (by simp),ih (by intro y hy;exact h y (by simp [hy]))⟩
  unfold Table.degree
  rw [fused_aux_degree]
  exact Nat.max_eq_left (fold _ (by intro x hx;obtain ⟨e,he,rfl⟩:=List.mem_map.mp hx;exact hc e he))

private theorem shape_congr (A B : Air.Table)
    (hw : A.width=B.width) (hd : A.degree 2=B.degree 2)
    (hp : profiles A=profiles B) (hl : A.maxLog=B.maxLog) : shapeOf 2 A=shapeOf 2 B := by
  unfold shapeOf Table.quotCount
  rw [auxCount_eq,auxCount_eq,numSide_eq,numSide_eq,numSide_eq,numSide_eq,hw,hd,hp,hl]

theorem fused_shape : shapeOf 2 (HorizontalTables.fuse selected)=⟨3372,106,7,106,22⟩ := by
  have hp : profiles (HorizontalTables.fuse selected)=profiles (HorizontalTables.fuse HorizontalTables.selected) := by
    rw [fuse_profiles,fuse_profiles,profiles_equal]
  exact (shape_congr _ _ widths_equal (fused_degree.trans HorizontalAuxCheck.fused_degree.symm)
    hp rfl).trans HorizontalAuxCheck.fused_shape

/-- Full concrete family proof-size accounting with the repaired receipt table.
Scheduler prior-state repairs and complete trace/soundness admission remain open. -/
theorem family_shapes : tables.map (shapeOf 2)=HorizontalAccounts.tables.map (shapeOf 2) := by
  simp only [tables,HorizontalAccounts.tables,List.map_cons,fused_shape,HorizontalAuxCheck.fused_shape]

theorem proof_bytes : sizeMaxDedup air (ZkFormal.V2.G.pg 2)=8288148 := by
  rw [sizeMaxDedup_eq_model]
  change sizeOfWeq (ZkFormal.V2.G.pg 2) (tables.map (shapeOf 2))=8288148
  rw [family_shapes]
  exact HorizontalCertified.bytes_exact

end ZkFormal.NearV3.Candidates.HorizontalReceipt
