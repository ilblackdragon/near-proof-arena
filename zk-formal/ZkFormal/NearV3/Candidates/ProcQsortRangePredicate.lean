import ZkFormal.NearV3.Candidates.ProcQsortPivot
namespace ZkFormal.NearV3.Candidates.ProcQsortRangePredicate
-- Pin references to the recursive helpers of the audited Lean 4.34.1 implementation.
local macro "partitionLoop" "(" args:term,* ")" : term => do
  let id := (Lean.mkIdent
  ((((`_private.Init.Data.Array.QSort.Basic).num 0).str "Array").str "qpartition" |>.str "loop"))
  `($id $args*)
local macro "sortLoop" "(" args:term,* ")" : term => do
  let id := (Lean.mkIdent
  ((((`_private.Init.Data.Array.QSort.Basic).num 0).str "Array").str "qsort" |>.str "sort"))
  `($id $args*)
def Holds {α : Type} {n : Nat} (P : α → Prop) (L H : Nat) (a : Vector α n) : Prop :=
  ∀j (hj : j<n),L≤j → j≤H → P a[j]

theorem swap_holds {α : Type} {n : Nat} (P : α → Prop) (L H : Nat) (a : Vector α n)
    (i k : Nat) (hi : i<n) (hk : k<n) (hli : L≤i) (hih : i≤H) (hlk : L≤k) (hkh : k≤H)
    (h : Holds P L H a) : Holds P L H (a.swap i k hi hk) := by
  intro j hj hlj hjh
  rw [Vector.getElem_swap]
  split
  · exact h k hk hlk hkh
  · split
    · exact h i hi hli hih
    · exact h j hj hlj hjh

theorem loop_holds {α : Type} {n : Nat} (lt : α → α → Bool)
    (lo hi : Nat) (hhi : hi<n) (pivot : α) (a : Vector α n) (i k : Nat)
    (hlo : lo≤i) (hik : i≤k) (hkh : k≤hi)
    (P : α → Prop) (L H : Nat) (hL : L≤lo) (hH : hi≤H) (h : Holds P L H a) :
    Holds P L H (partitionLoop(lt,lo,hi,hhi,pivot,a,i,k,hlo,hik,hkh)).2 := by
  fun_induction partitionLoop(lt,lo,hi,hhi,pivot,a,i,k,hlo,hik,hkh)
  · rename_i ih
    apply ih
    exact swap_holds P L H _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) h
  · rename_i ih
    exact ih h
  · exact swap_holds P L H _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h

theorem partition_holds {α : Type} {n : Nat} (a : Vector α n) (lt : α → α → Bool)
    (lo hi : Nat) (hw : lo≤hi) (hlo : lo<n) (hhi : hi<n)
    (P : α → Prop) (L H : Nat) (hL : L≤lo) (hH : hi≤H) (h : Holds P L H a) :
    Holds P L H (Array.qpartition a lt lo hi hw hlo hhi).2 := by
  unfold Array.qpartition
  apply loop_holds _ _ _ _ _ _ _ _ _ _ _ P L H hL hH
  repeat first
    | split
    | apply swap_holds P L H _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
    | exact h

theorem sort_holds {α : Type} {n : Nat} (lt : α → α → Bool) (a : Vector α n)
    (lo hi : Nat) (hw : lo≤hi) (hlo : lo<n) (hhi : hi<n)
    (P : α → Prop) (L H : Nat) (hL : L≤lo) (hH : hi≤H) (h : Holds P L H a) :
    Holds P L H (sortLoop(lt,a,lo,hi,hw,hlo,hhi)) := by
  fun_induction sortLoop(lt,a,lo,hi,hw,hlo,hhi)
  · rename_i a lo hi hw hlo hhi hlt mid hm b he hge
    have hp := partition_holds a lt lo hi hw hlo hhi P L H hL hH h
    rw [he] at hp
    exact hp
  · rename_i a lo hi hw hlo hhi hlt mid hm b he hge ih3 ih2 ih1
    have hp := partition_holds a lt lo hi hw hlo hhi P L H hL hH h
    rw [he] at hp
    exact ih1 (by omega) hH (ih2 hL (by omega) hp)
  · exact h
theorem qsort_holds {α : Type} [Inhabited α] (a : Array α) (lt : α → α → Bool)
    (lo hi : Nat) (P : α → Prop) (L H : Nat)
    (hL : L≤min lo (a.size-1))
    (hH : max (min lo (a.size-1)) (min hi (a.size-1))≤H)
    (h : ∀j (hj : j<a.size),L≤j → j≤H → P a[j]) :
    ∀j (hj : j<a.size),L≤j → j≤H → P (a.qsort lt lo hi)[j]! := by
  intro j hj hlj hjh
  unfold Array.qsort
  split
  · simpa [getElem!_pos,hj] using h j hj hlj hjh
  · have hh := sort_holds lt a.toVector (min lo (a.size-1))
      (max (min lo (a.size-1)) (min hi (a.size-1))) (by omega) (by omega) (by omega)
      P L H hL hH h
    simpa [getElem!_pos,hj] using hh j hj hlj hjh
end ZkFormal.NearV3.Candidates.ProcQsortRangePredicate
