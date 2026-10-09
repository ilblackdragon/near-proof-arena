import ZkFormal.NearV3.Candidates.ProcQsortFrame
namespace ZkFormal.NearV3.Candidates.ProcQsortPivot
-- Pin references to the recursive helpers of the audited Lean 4.34.1 implementation.
local macro "partitionLoop" "(" args:term,* ")" : term => do
  let id := (Lean.mkIdent
  ((((`_private.Init.Data.Array.QSort.Basic).num 0).str "Array").str "qpartition" |>.str "loop"))
  `($id $args*)
theorem loop_pivot {α : Type} {n : Nat} (lt : α → α → Bool)
    (lo hi : Nat) (hhi : hi<n) (pivot : α) (a : Vector α n) (i k : Nat)
    (hlo : lo≤i) (hik : i≤k) (hkh : k≤hi) (hp : a[hi]=pivot)
    (m : Nat) (hm : m<n) (he : (partitionLoop(lt,lo,hi,hhi,pivot,a,i,k,hlo,hik,hkh)).1.val=m) :
    (partitionLoop(lt,lo,hi,hhi,pivot,a,i,k,hlo,hik,hkh)).2[m]=pivot := by
  fun_induction partitionLoop(lt,lo,hi,hhi,pivot,a,i,k,hlo,hik,hkh)
  · rename_i ih
    apply ih ?_ he
    rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
    exact hp
  · rename_i ih
    exact ih hp he
  · dsimp only at he
    subst m
    simpa using hp
def Scan {α : Type} {n : Nat} (lt : α → α → Bool) (lo _hi i k : Nat)
    (pivot : α) (a : Vector α n) : Prop :=
  (∀j (hj : j<n),lo≤j → j<i → lt a[j] pivot=true) ∧
  (∀j (hj : j<n),i≤j → j<k → lt a[j] pivot=false)

theorem scan_skip {α : Type} {n : Nat} (lt : α → α → Bool)
    (lo hi i k : Nat) (pivot : α) (a : Vector α n) (hk : k<n)
    (hs : Scan lt lo hi i k pivot a) (ht : lt a[k] pivot=false) :
    Scan lt lo hi i (k+1) pivot a := by
  refine ⟨hs.1,?_⟩
  intro j hj hij hjk
  by_cases he : j=k
  · subst j; exact ht
  · exact hs.2 j hj hij (by omega)

theorem scan_swap {α : Type} {n : Nat} (lt : α → α → Bool)
    (lo hi i k : Nat) (pivot : α) (a : Vector α n) (hi' : i<n) (hk : k<n)
    (hik : i≤k) (hs : Scan lt lo hi i k pivot a) (ht : lt a[k] pivot=true) :
    Scan lt lo hi (i+1) (k+1) pivot (a.swap i k hi' hk) := by
  constructor
  · intro j hj hlj hji
    by_cases he : j=i
    · subst j; simpa using ht
    · rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
      exact hs.1 j hj hlj (by omega)
  · intro j hj hij hjk
    by_cases he : j=k
    · subst j
      simpa using hs.2 i hi' (by omega) (by omega)
    · rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
      exact hs.2 j hj (by omega) (by omega)

theorem loop_order {α : Type} {n : Nat} (lt : α → α → Bool)
    (lo hi : Nat) (hhi : hi<n) (pivot : α) (a : Vector α n) (i k : Nat)
    (hlo : lo≤i) (hik : i≤k) (hkh : k≤hi) (hs : Scan lt lo hi i k pivot a)
    (m : Nat) (he : (partitionLoop(lt,lo,hi,hhi,pivot,a,i,k,hlo,hik,hkh)).1.val=m) :
    (∀j (hj : j<n),lo≤j → j<m →
      lt (partitionLoop(lt,lo,hi,hhi,pivot,a,i,k,hlo,hik,hkh)).2[j] pivot=true) ∧
    (∀j (hj : j<n),m<j → j≤hi →
      lt (partitionLoop(lt,lo,hi,hhi,pivot,a,i,k,hlo,hik,hkh)).2[j] pivot=false) := by
  fun_induction partitionLoop(lt,lo,hi,hhi,pivot,a,i,k,hlo,hik,hkh)
  · rename_i a i k hlo hik hkh hk ht ih
    exact ih (scan_swap lt lo hi i k pivot a (by omega) (by omega) hik hs ht) he
  · rename_i a i k hlo hik hkh hk ht ih
    exact ih (scan_skip lt lo hi i k pivot a (by omega) hs (by simpa using ht)) he
  · rename_i a i k hlo hik hkh hk
    dsimp only at he
    subst m
    constructor
    · intro j hj hlj hji
      rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
      exact hs.1 j hj hlj hji
    · intro j hj hij hjh
      by_cases he : j=hi
      · subst j
        simpa using hs.2 i (by omega) (by omega) (by omega)
      · rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
        exact hs.2 j hj (by omega) (by omega)

theorem partition_order {α : Type} {n : Nat} (a : Vector α n) (lt : α → α → Bool)
    (lo hi : Nat) (hw : lo≤hi) (hlo : lo<n) (hhi : hi<n)
    (m : Nat) (hm : m<n) (he : (Array.qpartition a lt lo hi hw hlo hhi).1.val=m) :
    (∀j (hj : j<n),lo≤j → j<m →
      lt (Array.qpartition a lt lo hi hw hlo hhi).2[j]
        (Array.qpartition a lt lo hi hw hlo hhi).2[m]=true) ∧
    (∀j (hj : j<n),m<j → j≤hi →
      lt (Array.qpartition a lt lo hi hw hlo hhi).2[j]
        (Array.qpartition a lt lo hi hw hlo hhi).2[m]=false) := by
  unfold Array.qpartition at he ⊢
  have hp := loop_pivot lt lo hi hhi _ _ lo lo (Nat.le_refl _) (Nat.le_refl _) hw rfl m hm he
  have ho := loop_order lt lo hi hhi _ _ lo lo (Nat.le_refl _) (Nat.le_refl _) hw
    (by constructor <;> intro j hj h1 h2 <;> omega) m he
  rw [hp]
  exact ho
end ZkFormal.NearV3.Candidates.ProcQsortPivot
