import ZkFormal.NearV3.Candidates.ProcQsortRangePredicate
namespace ZkFormal.NearV3.Candidates.ProcQsortProgress
-- Pin references to the recursive helpers of the audited Lean 4.34.1 implementation.
local macro "partitionLoop" "(" args:term,* ")" : term => do
  let id := (Lean.mkIdent
  ((((`_private.Init.Data.Array.QSort.Basic).num 0).str "Array").str "qpartition" |>.str "loop"))
  `($id $args*)
def Room {α : Type} {n : Nat} (lt : α → α → Bool) (hi i k : Nat)
    (pivot : α) (a : Vector α n) : Prop :=
  i<k ∨ ∃j, ∃hj : j<n,k≤j ∧ j<hi ∧ lt a[j] pivot=false

theorem loop_progress {α : Type} {n : Nat} (lt : α → α → Bool)
    (lo hi : Nat) (hhi : hi<n) (pivot : α) (a : Vector α n) (i k : Nat)
    (hlo : lo≤i) (hik : i≤k) (hkh : k≤hi) (hr : Room lt hi i k pivot a) :
    (partitionLoop(lt,lo,hi,hhi,pivot,a,i,k,hlo,hik,hkh)).1.val<hi := by
  fun_induction partitionLoop(lt,lo,hi,hhi,pivot,a,i,k,hlo,hik,hkh)
  · rename_i a i k hlo hik hkh hk ht ih
    apply ih
    rcases hr with hr|⟨j,hj,hkj,hjh,hbad⟩
    · exact Or.inl (by omega)
    · have hne : j≠k := by intro he; subst j; simp [ht] at hbad
      refine Or.inr ⟨j,hj,by omega,hjh,?_⟩
      rw [Vector.getElem_swap_of_ne (by omega) hne]
      exact hbad
  · rename_i a i k hlo hik hkh hk ht ih
    exact ih (Or.inl (by omega))
  · rcases hr with hr|⟨j,hj,hkj,hjh,hbad⟩ <;> dsimp only <;> omega

theorem median_sentinel {α : Type} {n : Nat} (lt : α → α → Bool)
    (ha : ∀a b,lt a b=true → lt b a=false)
    (a : Vector α n) (i j : Nat) (hi : i<n) (hj : j<n) :
    let b := if lt a[i] a[j] then a.swap i j hi hj else a
    lt b[i] b[j]=false := by
  dsimp only
  split
  · rename_i h
    simpa using ha _ _ h
  · simpa using (show ¬lt a[i] a[j]=true from by assumption)

theorem partition_progress {α : Type} {n : Nat} (lt : α → α → Bool)
    (ha : ∀a b,lt a b=true → lt b a=false)
    (a : Vector α n) (lo hi : Nat) (hw : lo≤hi) (hlo : lo<n) (hhi : hi<n)
    (hlt : lo<hi) : (Array.qpartition a lt lo hi hw hlo hhi).1.val<hi := by
  unfold Array.qpartition
  apply loop_progress
  apply Or.inr
  refine ⟨(lo+hi)/2,by omega,by omega,by omega,?_⟩
  exact median_sentinel lt ha _ _ _ _ _
end ZkFormal.NearV3.Candidates.ProcQsortProgress
