import ZkFormal.NearV3.Candidates.HorizontalAccounts

namespace ZkFormal.NearV3.Candidates.HorizontalInventory
open ZkFormal.Air

/-- Original physical order, with the checked empty-account extension. -/
def original : List Air.Table := (PackedMerkleFamily.tables 4).set 19 Rcpt.Candidates.AccountEmpty.table

def selectedIndices : List Nat := [0,1,2,3,4,6,8,9,13,14,15,16,17,18,22,23,24,25,29]
def restIndices : List Nat := [5,7,10,11,12,19,20,21,26,27,28]
def tableAt (i : Nat) : Air.Table := original.getD i MerkleEmpty.table

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

/-- Every original table appears exactly once, including the four distinct SHA slots. -/
theorem indices_partition : (selectedIndices++restIndices).Perm (List.range 30) := by decide +kernel

theorem selected_exact : selectedIndices.map tableAt=HorizontalTables.selected := by rfl

theorem rest_exact : restIndices.map tableAt=HorizontalAccounts.rest := by rfl

theorem original_exact : (List.range 30).map tableAt=original := by rfl

/-- Fusion reorders the repaired original inventory; it neither drops nor
duplicates a component. The component trace list must follow these exact indices. -/
theorem partition : (HorizontalTables.selected++HorizontalAccounts.rest).Perm original := by
  have h := indices_partition.map tableAt
  simpa only [List.map_append,selected_exact,rest_exact,original_exact] using h

/-- Any additive per-component quantity, in particular bus multiplicities, is
preserved by the concrete partition used by the admitted candidate. -/
theorem partition_sum (f : Air.Table→Nat) :
    ((HorizontalTables.selected++HorizontalAccounts.rest).map f).sum=(original.map f).sum :=
  by
    have sum_perm : ∀{xs ys : List Nat},xs.Perm ys → xs.sum=ys.sum := by
      intro xs ys h
      induction h with
      | nil => rfl
      | cons x h ih => simp only [List.sum_cons,ih]
      | swap x y xs => simp only [List.sum_cons]; omega
      | trans h1 h2 ih1 ih2 => exact ih1.trans ih2
    exact sum_perm (partition.map f)

/-- Index-sensitive accounting retains distinct SHA traces even when their
AIR tables are identical. -/
theorem indexed_partition_sum (f : Nat→Nat) :
    (selectedIndices.map f).sum+(restIndices.map f).sum=((List.range 30).map f).sum := by
  simp only [selectedIndices,restIndices,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  simp only [List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
    List.sum_append,List.sum_cons,List.sum_nil]
  omega

end ZkFormal.NearV3.Candidates.HorizontalInventory
