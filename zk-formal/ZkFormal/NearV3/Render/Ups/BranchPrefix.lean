import ZkFormal.NearV3.Render.Ups.FieldStart
import ZkFormal.NearV3.Render.Ups.UniqueFieldPosition

namespace ZkFormal.NearV3.Render.UpsGen

def branchPrefix (ty : Nat) : List (Nat×Nat) :=
  [(0,1)]++(if ty=3 then [(4,4),(5,32)] else [])

theorem branch_field_shape {Q : UpsPartI} (f : FieldsOk Q) (ht : Q.ty=2 ∨ Q.ty=3) :
    Q.shape=branchPrefix Q.ty++(6,2)::(List.replicate (nWin Q.shape) (7,32)++[(8,8)]) := by
  calc Q.shape=nodeFields Q.ty Q.qhk (nWin Q.shape) := f.shape
       _ = _ := by rcases ht with ht|ht <;> simp [nodeFields,branchPrefix,ht]

theorem branch_prefix_avoid (ty : Nat) : ∀ f ∈ branchPrefix ty,f.1≠6 := by
  by_cases h : ty=3 <;> simp [branchPrefix,h]

theorem branch_bitmap_start {Q : UpsPartI} (f : FieldsOk Q) (ht : Q.ty=2 ∨ Q.ty=3)
    (pre post : List (Nat×Nat)) (width : Nat) (he : Q.shape=pre++(6,width)::post) :
    width=2 ∧ fieldsLen pre=fieldsLen (branchPrefix Q.ty) := by
  have hmem : (6,width)∈nodeFields Q.ty Q.qhk (nWin Q.shape) := by rw [←f.shape,he]; simp
  have hw := (nodeFields_length hmem).2.2.2.2.2.2.1 rfl
  have hc : fieldAt Q.shape (fieldsLen pre)=(6,0,width,nWin pre) := by
    rw [he]; exact field_start_cursor pre post 6 width (by omega)
  have hs := branch_field_shape f ht
  have ha := unique_field_position (branchPrefix Q.ty)
    (List.replicate (nWin Q.shape) (7,32)++[(8,8)]) 6 2 (fieldsLen pre)
    (by decide) (branch_prefix_avoid _) (by
      intro a ha
      simp only [List.mem_append,List.mem_replicate,List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with ⟨_,rfl⟩ | rfl <;> decide)
    (by rw [←hs,hc])
  rw [←hs,hc] at ha
  simp only [Nat.add_zero] at ha
  exact ⟨hw,ha⟩

end ZkFormal.NearV3.Render.UpsGen
