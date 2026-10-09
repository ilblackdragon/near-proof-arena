import ZkFormal.NearV3.Candidates.ProcQsortPermutation
namespace ZkFormal.NearV3.Candidates.ProcQsortFrame
-- Pin references to the recursive helpers of the audited Lean 4.34.1 implementation.
local macro "partitionLoop" "(" args:term,* ")" : term => do
  let id := (Lean.mkIdent
  ((((`_private.Init.Data.Array.QSort.Basic).num 0).str "Array").str "qpartition" |>.str "loop"))
  `($id $args*)
local macro "sortLoop" "(" args:term,* ")" : term => do
  let id := (Lean.mkIdent
  ((((`_private.Init.Data.Array.QSort.Basic).num 0).str "Array").str "qsort" |>.str "sort"))
  `($id $args*)
theorem swap_outside {α : Type} {n : Nat} (a : Vector α n) (lo hi i j k : Nat)
    (hi' : i<n) (hj : j<n) (hk : k<n) (hli : lo≤i) (hih : i≤hi)
    (hlj : lo≤j) (hjh : j≤hi) (hout : k<lo ∨ hi<k) :
    (a.swap i j hi' hj)[k]=a[k] := by
  apply Vector.getElem_swap_of_ne <;> omega

theorem partition_loop_frame {α : Type} {n : Nat} (lt : α → α → Bool)
    (lo hi : Nat) (hhi : hi<n) (pivot : α) (a : Vector α n) (i k : Nat)
    (hlo : lo≤i) (hik : i≤k) (hkh : k≤hi) (j : Nat) (hj : j<n)
    (hout : j<lo ∨ hi<j) :
    (partitionLoop(lt,lo,hi,hhi,pivot,a,i,k,hlo,hik,hkh)).2[j]=a[j] := by
  fun_induction partitionLoop(lt,lo,hi,hhi,pivot,a,i,k,hlo,hik,hkh)
  · rename_i ih
    rw [ih]
    exact swap_outside _ lo hi _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hout
  · assumption
  · exact swap_outside _ lo hi _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hout

theorem partition_frame {α : Type} {n : Nat} (a : Vector α n) (lt : α → α → Bool)
    (lo hi : Nat) (hw : lo≤hi) (hlo : lo<n) (hhi : hi<n)
    (j : Nat) (hj : j<n) (hout : j<lo ∨ hi<j) :
    (Array.qpartition a lt lo hi hw hlo hhi).2[j]=a[j] := by
  unfold Array.qpartition
  rw [partition_loop_frame _ _ _ _ _ _ _ _ _ _ _ j hj hout]
  repeat first | split | rw [swap_outside _ lo hi _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hout] | rfl
theorem sort_loop_frame {α : Type} {n : Nat} (lt : α → α → Bool) (a : Vector α n)
    (lo hi : Nat) (hw : lo≤hi) (hlo : lo<n) (hhi : hi<n)
    (j : Nat) (hj : j<n) (hout : j<lo ∨ hi<j) :
    (sortLoop(lt,a,lo,hi,hw,hlo,hhi))[j]=a[j] := by
  fun_induction sortLoop(lt,a,lo,hi,hw,hlo,hhi)
  · rename_i a lo hi hw hlo hhi h mid hm b he hge
    have hp := partition_frame a lt lo hi hw hlo hhi j hj hout
    rw [he] at hp
    exact hp
  · rename_i a lo hi hw hlo hhi h mid hm b he hge ih3 ih2 ih1
    have hp := partition_frame a lt lo hi hw hlo hhi j hj hout
    rw [he] at hp
    rw [ih1 (by omega),ih2 (by omega)]
    exact hp
  · rfl

/-- The public quicksort clamps its requested bounds before sorting. -/
theorem qsort_frame {α : Type} [Inhabited α] (a : Array α) (lt : α → α → Bool) (lo hi j : Nat)
    (hj : j<a.size)
    (hout : j<min lo (a.size-1) ∨ max (min lo (a.size-1)) (min hi (a.size-1))<j) :
    (a.qsort lt lo hi)[j]! =(a[j]) := by
  unfold Array.qsort
  split
  · simp [getElem!_pos,hj]
  · have hh := sort_loop_frame lt a.toVector (min lo (a.size-1))
      (max (min lo (a.size-1)) (min hi (a.size-1))) (by omega) (by omega) (by omega) j hj hout
    simpa [getElem!_pos,hj] using hh
end ZkFormal.NearV3.Candidates.ProcQsortFrame
