import ZkFormal.NearV3.Candidates.ProcGeneratedTimeOrder
import Init.Data.Vector.Perm
import Lean
namespace ZkFormal.NearV3.Candidates.ProcQsortPermutation
-- Pin references to the recursive helpers of the audited Lean 4.34.1 implementation.
local macro "partitionLoop" "(" args:term,* ")" : term => do
  let id := (Lean.mkIdent
  ((((`_private.Init.Data.Array.QSort.Basic).num 0).str "Array").str "qpartition" |>.str "loop"))
  `($id $args*)
local macro "sortLoop" "(" args:term,* ")" : term => do
  let id := (Lean.mkIdent
  ((((`_private.Init.Data.Array.QSort.Basic).num 0).str "Array").str "qsort" |>.str "sort"))
  `($id $args*)
theorem partition_loop_perm {α : Type} {n : Nat} (lt : α → α → Bool)
    (lo hi : Nat) (hhi : hi<n) (pivot : α) (a : Vector α n) (i k : Nat)
    (hlo : lo≤i) (hik : i≤k) (hkh : k≤hi) :
    ((partitionLoop(lt,lo,hi,hhi,pivot,a,i,k,hlo,hik,hkh)).2).toList.Perm a.toList := by
  fun_induction partitionLoop(lt,lo,hi,hhi,pivot,a,i,k,hlo,hik,hkh)
  · rename_i ih
    exact ih.trans (Vector.perm_iff_toList_perm.mp (Vector.swap_perm (by omega) (by omega)))
  · assumption
  · exact Vector.perm_iff_toList_perm.mp (Vector.swap_perm (by omega) (by omega))
theorem partition_perm {α : Type} {n : Nat} (a : Vector α n) (lt : α → α → Bool)
    (lo hi : Nat) (hw : lo≤hi) (hlo : lo<n) (hhi : hi<n) :
    (Array.qpartition a lt lo hi hw hlo hhi).2.toList.Perm a.toList := by
  unfold Array.qpartition
  apply (partition_loop_perm _ _ _ _ _ _ _ _ _ _ _).trans
  repeat first
    | split
    | apply (Vector.perm_iff_toList_perm.mp (Vector.swap_perm _ _)).trans
    | exact List.Perm.refl _

theorem sort_loop_perm {α : Type} {n : Nat} (lt : α → α → Bool) (a : Vector α n)
    (lo hi : Nat) (hw : lo≤hi) (hlo : lo<n) (hhi : hi<n) :
    (sortLoop(lt,a,lo,hi,hw,hlo,hhi)).toList.Perm a.toList := by
  fun_induction sortLoop(lt,a,lo,hi,hw,hlo,hhi)
  · rename_i a lo hi hw hlo hhi h mid hm b he hge
    have hp := partition_perm a lt lo hi hw hlo hhi
    rw [he] at hp
    exact hp
  · rename_i a lo hi hw hlo hhi h mid hm b he hge ih3 ih2 ih1
    have hp := partition_perm a lt lo hi hw hlo hhi
    rw [he] at hp
    exact ih1.trans (ih2.trans hp)
  · exact List.Perm.refl _
theorem qsort_perm {α : Type} (a : Array α) (lt : α → α → Bool) (lo hi : Nat) :
    (a.qsort lt lo hi).toList.Perm a.toList := by
  unfold Array.qsort
  split
  · exact List.Perm.refl _
  · exact sort_loop_perm lt a.toVector _ _ _ _ _

theorem sortPush_perm (xs : List (Nat×Nat×Nat×Nat)) :
    (ZkFormal.NearV3.Sched.Gen.sortPush xs).Perm xs := by
  exact qsort_perm xs.toArray _ _ _
end ZkFormal.NearV3.Candidates.ProcQsortPermutation
