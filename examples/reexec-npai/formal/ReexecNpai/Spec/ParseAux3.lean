import ReexecNpai.Spec.ParseAux2

/-!
# Setting the root's `pslot`

The epilogue of `pParse` writes `C_ROOT` into the `pslot` field of the last
entry. `updPs r p` changes that field only; nothing structural depends on it.
-/

set_option maxRecDepth 8000

namespace ReexecNpai
namespace ParseProof

open NearSpec NearSpec.TransferV1

def updPs (r p i : Nat) (e : Ent) : Ent := if i = r then { e with pslot := p } else e

section
variable {r p i : Nat} {e : Ent}
@[simp] theorem updPs_pre : (updPs r p i e).pre = e.pre := by unfold updPs; split <;> rfl
@[simp] theorem updPs_preLen : (updPs r p i e).preLen = e.preLen := by unfold updPs; split <;> rfl
@[simp] theorem updPs_kid : (updPs r p i e).kid = e.kid := by unfold updPs; split <;> rfl
@[simp] theorem updPs_res : (updPs r p i e).res = e.res := by unfold updPs; split <;> rfl
@[simp] theorem updPs_val : (updPs r p i e).val = e.val := by unfold updPs; split <;> rfl
@[simp] theorem updPs_nf : (updPs r p i e).nf = e.nf := by unfold updPs; split <;> rfl
@[simp] theorem updPs_lo : (updPs r p i e).lo = e.lo := by unfold updPs; split <;> rfl
@[simp] theorem updPs_rst : (updPs r p i e).rst = e.rst := by unfold updPs; split <;> rfl
theorem updPs_ne (h : i ≠ r) : updPs r p i e = e := by simp [updPs, h]
theorem updPs_pslot_self : (updPs r p r e).pslot = p := by simp [updPs]
@[simp] theorem vlenAt_updPs (pb : Bytes) : vlenAt pb (updPs r p i e) = vlenAt pb e := by
  simp [vlenAt]
@[simp] theorem childSlot_updPs (q : Nat) : childSlot (updPs r p i e) q = childSlot e q := by
  simp [childSlot]
@[simp] theorem entRev_updPs (pb : Bytes) : entRev pb (updPs r p i e) = entRev pb e := by
  simp [entRev]
end

section
variable {A : List Ent} {r p : Nat}

theorem getD_updPs (i : Nat) (d : Ent) (f : Ent → Nat) (hf : ∀ e, f (updPs r p i e) = f e) :
    f ((A.mapIdx (updPs r p)).getD i d) = f (A.getD i d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  cases A[i]? <;> simp [hf]

theorem treeAt_updPs (K : List Nat) (vals : Nat → Bytes) :
    ∀ j, treeAt (A.mapIdx (updPs r p)) K vals j = treeAt A K vals j := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
  cases hj : A[j]? with
  | none =>
    have h1 : (A.mapIdx (updPs r p))[j]? = none := by simp [hj]
    rw [treeAt, h1, treeAt, hj]
  | some e =>
    have h1 : (A.mapIdx (updPs r p))[j]? = some (updPs r p j e) := by simp [hj]
    cases hn : e.nf with
    | leaf k ref mm =>
      rw [treeAt_leaf h1 (by simpa using hn), treeAt_leaf hj hn]
    | ext k h mm =>
      cases h with
      | some hh => rw [treeAt_exth h1 (by simpa using hn), treeAt_exth hj hn]
      | none =>
        rw [treeAt_ext h1 (by simpa using hn), treeAt_ext hj hn]
        simp only [updPs_kid]
        split
        · rename_i hlt; rw [ih _ hlt]
        · rfl
    | branch v ks mm =>
      rw [treeAt_branch h1 (by simpa using hn), treeAt_branch hj hn]
      simp only [updPs_kid]
      congr 1
      apply kidsOf_congr; intro q _ _
      split
      · rename_i hlt; rw [ih _ hlt]
      · rfl

theorem vals0_updPs (pb : Bytes) : vals0 pb (A.mapIdx (updPs r p)) = vals0 pb A := by
  funext i
  simp only [vals0, vlenAt, pseg]
  rw [getD_updPs i default Ent.val (fun _ => updPs_val)]

theorem revSum_updPs (pb : Bytes) : revSum pb (A.mapIdx (updPs r p)) = revSum pb A := by
  rw [revSum_eq, revSum_eq, List.length_mapIdx]
  apply ssum_congr; intro i _ _
  exact getD_updPs i default (entRev pb) (fun _ => entRev_updPs pb)

theorem nodeWF_updPs {pb : Bytes} {K : List Nat} {j : Nat} (hr : A.length ≤ r + 1) (hj : j < A.length)
    (h : NodeWF pb A K j) : NodeWF pb (A.mapIdx (updPs r p)) K j := by
  obtain ⟨e, he, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have he' : (A.mapIdx (updPs r p))[j]? = some (updPs r p j e) := by simp [he]
  refine ⟨updPs r p j e, he', ?_⟩
  simp only [updPs_nf, updPs_rst, updPs_pre, updPs_preLen, updPs_val, updPs_lo, updPs_kid, updPs_res,
    vlenAt_updPs, childSlot_updPs]
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_, ?_⟩
  · intro q hq
    obtain ⟨ec, hc1, hc2, hc3, hc4, hc5⟩ := h10 q hq
    refine ⟨ec, ?_, hc2, hc3, hc4, hc5⟩
    simp only [List.getElem?_mapIdx, hc1, Option.map_some]
    rw [updPs_ne (by omega)]
  · have hres : (A.getD (K.getD e.kid 0) e).res =
        ((A.mapIdx (updPs r p)).getD (K.getD e.kid 0) (updPs r p j e)).res := by
      generalize K.getD e.kid 0 = c
      simp only [List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
      cases A[c]? <;> simp
    rw [h11, hres]

end

end ParseProof
end ReexecNpai
