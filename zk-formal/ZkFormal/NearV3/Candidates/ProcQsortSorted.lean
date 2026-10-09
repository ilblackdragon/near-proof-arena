import ZkFormal.NearV3.Candidates.ProcQsortProgress
namespace ZkFormal.NearV3.Candidates.ProcQsortSorted
local macro "sortLoop" "(" args:term,* ")" : term => do
  let id := (Lean.mkIdent
  ((((`_private.Init.Data.Array.QSort.Basic).num 0).str "Array").str "qsort" |>.str "sort"))
  `($id $args*)
def Sorted {α : Type} {n : Nat} (le : α → α → Prop) (lo hi : Nat) (a : Vector α n) : Prop :=
  ∀i j (hi' : i<n) (hj : j<n),lo≤i → i<j → j≤hi → le a[i] a[j]

theorem sort_sorted {α : Type} {n : Nat} (lt : α → α → Bool) (le : α → α → Prop)
    (hrefl : ∀a,le a a) (htrans : ∀a b c,le a b → le b c → le a c)
    (hasym : ∀a b,lt a b=true → lt b a=false)
    (htrue : ∀a b,lt a b=true → le a b) (hfalse : ∀a b,lt a b=false → le b a)
    (a : Vector α n) (lo hi : Nat) (hw : lo≤hi) (hlo : lo<n) (hhi : hi<n) :
    Sorted le lo hi (sortLoop(lt,a,lo,hi,hw,hlo,hhi)) := by
  fun_induction sortLoop(lt,a,lo,hi,hw,hlo,hhi)
  · rename_i a lo hi hw hlo hhi hlt mid hm b he hge
    have hp := ProcQsortProgress.partition_progress lt hasym a lo hi hw hlo hhi hlt
    rw [he] at hp
    dsimp only at hp
    omega
  · rename_i a lo hi hw hlo hhi hlt mid hm b he hge ih3 ih2 ih1
    have hmid : mid<n := by omega
    have hp := ProcQsortPivot.partition_order a lt lo hi hw hlo hhi mid hmid
      (by rw [he])
    rw [he] at hp
    dsimp only at hp
    let left := sortLoop(lt,b,lo,mid,hm.1,hlo,hmid)
    have hl0 : ProcQsortRangePredicate.Holds (fun x=>le x b[mid]) lo mid b := by
      intro j hj hlj hjm
      by_cases hje : j=mid
      · subst j; exact hrefl _
      · exact htrue _ _ (hp.1 j hj hlj (by omega))
    have hl : ProcQsortRangePredicate.Holds (fun x=>le x b[mid]) lo mid left :=
      ProcQsortRangePredicate.sort_holds lt b lo mid hm.1 hlo hmid _ lo mid (by omega) (by omega) hl0
    have hr0 : ProcQsortRangePredicate.Holds (fun x=>le b[mid] x) (mid+1) hi left := by
      intro j hj hmj hjh
      have hf := ProcQsortFrame.sort_loop_frame lt b lo mid hm.1 hlo hmid j hj (Or.inr (by omega))
      change le b[mid] (sortLoop(lt,b,lo,mid,hm.1,hlo,hmid))[j]
      rw [hf]
      exact hfalse _ _ (hp.2 j hj (by omega) hjh)
    have hr := ProcQsortRangePredicate.sort_holds lt left (mid+1) hi (by omega) (by omega) hhi
      (fun x=>le b[mid] x) (mid+1) hi (by omega) (by omega) hr0
    intro i j hi' hj hli hij hjh
    by_cases hjm : j≤mid
    · have hfi := ProcQsortFrame.sort_loop_frame lt left (mid+1) hi (by omega) (by omega) hhi i hi' (Or.inl (by omega))
      have hfj := ProcQsortFrame.sort_loop_frame lt left (mid+1) hi (by omega) (by omega) hhi j hj (Or.inl (by omega))
      rw [hfi,hfj]
      exact ih2 i j hi' hj hli hij hjm
    · by_cases him : mid<i
      · exact ih1 i j hi' hj (by omega) hij hjh
      · have hfi := ProcQsortFrame.sort_loop_frame lt left (mid+1) hi (by omega) (by omega) hhi i hi' (Or.inl (by omega))
        rw [hfi]
        exact htrans _ _ _ (hl i hi' hli (by omega)) (hr j hj (by omega) hjh)
  · intro i j hi' hj hli hij hjh
    omega
theorem qsort_pairwise {α : Type} (lt : α → α → Bool) (le : α → α → Prop)
    (hrefl : ∀a,le a a) (htrans : ∀a b c,le a b → le b c → le a c)
    (hasym : ∀a b,lt a b=true → lt b a=false)
    (htrue : ∀a b,lt a b=true → le a b) (hfalse : ∀a b,lt a b=false → le b a)
    (a : Array α) : (a.qsort lt).toList.Pairwise le := by
  unfold Array.qsort
  split
  · rename_i hz
    have he : a.toList=[] := List.length_eq_zero_iff.mp (by simpa using hz)
    simp [he]
  · rename_i hn
    simp only [Nat.min_eq_left (Nat.zero_le _),Nat.min_self,Nat.max_eq_right (Nat.zero_le _)]
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have h := sort_sorted lt le hrefl htrans hasym htrue hfalse a.toVector 0 (a.size-1)
      (by omega) (by omega) (by omega)
    exact h i j (by simpa using hi) (by simpa using hj) (by omega) hij (by simpa using Nat.le_pred_of_lt (show j<a.size by simpa using hj))

theorem push_sort_order (xs : List (Nat×Nat×Nat×Nat)) :
    (ZkFormal.NearV3.Sched.Gen.sortPush xs).Pairwise (fun a b=>a.1≤b.1) := by
  apply qsort_pairwise
  · intro a; exact Nat.le_refl _
  · intro a b c hab hbc; exact Nat.le_trans hab hbc
  · intro a b h
    simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
    simp only [Bool.or_eq_false_iff,Bool.and_eq_false_imp,decide_eq_false_iff_not,beq_iff_eq]
    rcases h with h|⟨he,h⟩ <;> constructor <;> intro <;> omega
  · intro a b h
    simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
    rcases h with h|⟨he,h⟩ <;> omega
  · intro a b h
    simp only [Bool.or_eq_false_iff,decide_eq_false_iff_not] at h
    omega
end ZkFormal.NearV3.Candidates.ProcQsortSorted
