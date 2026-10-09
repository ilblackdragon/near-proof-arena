import ZkFormal.NearV3.Candidates.InteractionTriples
namespace ZkFormal.NearV3.Candidates.InteractionTriples
open ZkFormal.Air

theorem singles_sum (s : Bool) (xs : List Interaction) (f : Interaction→Nat) (hz:f (dummy s)=0) :
    ((singles s xs).map f).sum=(xs.map f).sum := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp [singles,List.flatMap_cons,hz,Nat.add_assoc] at ih ⊢;exact ih

theorem pairs_sum (s : Bool) (xs : List Interaction) (f : Interaction→Nat) (hz:f (dummy s)=0) :
    ((pairs s xs).map f).sum=(xs.map f).sum := by
  cases xs with
  | nil=>rfl
  | cons x xs=>
    cases xs with
    | nil=>simp [pairs,hz]
    | cons y ys=>simp only [pairs,List.map_cons,List.sum_cons,hz,Nat.zero_add];rw [pairs_sum s ys f hz]
termination_by xs.length

theorem lows_sum (s : Bool) (xs : List Interaction) (f : Interaction→Nat) (hz:f (dummy s)=0) :
    ((lows s xs).map f).sum=(xs.map f).sum := by
  cases xs with
  | nil=>rfl
  | cons x xs=>
    cases xs with
    | nil=>simp [lows,hz]
    | cons y ys=>
      cases ys with
      | nil=>simp [lows,hz]
      | cons z zs=>simp only [lows,List.map_cons,List.sum_cons];rw [lows_sum s zs f hz]
termination_by xs.length

theorem highLow_sum (s : Bool) (xs ys : List Interaction) (f : Interaction→Nat) (hz:f (dummy s)=0) :
    ((highLow s xs ys).map f).sum=(xs.map f).sum+(ys.map f).sum := by
  cases xs with
  | nil=>simpa [highLow] using lows_sum s ys f hz
  | cons x xs=>
    cases ys with
    | nil=>simpa [highLow] using singles_sum s (x::xs) f hz
    | cons y ys=>
      simp only [highLow,List.map_cons,List.sum_cons,hz,Nat.zero_add]
      rw [highLow_sum s xs ys f hz]
      omega
termination_by xs.length

theorem side_sum (s : Bool) (xs : List Interaction) (f : Interaction→Nat) (hz:f (dummy s)=0) :
    ((side s xs).map f).sum=(xs.map f).sum := by
  simp only [side,List.map_append,List.sum_append,singles_sum s _ f hz,
    pairs_sum s _ f hz,highLow_sum s _ _ f hz]
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.filter_cons,List.map_cons,List.sum_cons]
    by_cases h4:4<x.phiDegree <;> by_cases h3:x.phiDegree=3 <;>
      by_cases he4:x.phiDegree=4 <;> by_cases h2:x.phiDegree≤2
    all_goals simp [h4,h3,he4,h2,List.map_cons,List.sum_cons]
    all_goals omega

theorem reorder_sum (xs : List Interaction) (f : Interaction→Nat)
    (ht:f (dummy true)=0) (hf:f (dummy false)=0) :
    ((reorder xs).map f).sum=(xs.map f).sum := by
  simp only [reorder,List.map_append,List.sum_append,side_sum true _ f ht,side_sum false _ f hf]
  have hp:=List.filter_append_perm (fun i:Interaction=>i.send) xs
  have hh:=List.Perm.sum_nat (hp.map f)
  simpa only [List.map_append,List.sum_append] using hh

end ZkFormal.NearV3.Candidates.InteractionTriples
