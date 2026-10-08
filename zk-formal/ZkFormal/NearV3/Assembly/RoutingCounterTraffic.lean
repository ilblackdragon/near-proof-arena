import ZkFormal.NearV3.Assembly.RoutingCounterPatch

namespace ZkFormal.NearV3.Assembly.RoutingQCandidate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

private theorem fold_sum_congr {α : Type} (xs : List α) (f g : α→Nat)
    (h : ∀x∈xs,f x=g x) (start : Nat) :
    xs.foldr (fun x a=>f x+a) start=xs.foldr (fun x a=>g x+a) start := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rw [h x (by simp),ih (by intro y hy; exact h y (by simp [hy]))]

/-- Generic exact count transfer; entries on unrelated buses do not require
message equality. Useful for a witness-only counter assignment. -/
theorem tableBusCount_congr (is : List Interaction) (tr tr' : Trace Fp) (t : Nat)
    (pub : List Fp) (bus : Nat) (sd : Bool) (msg : List Fp)
    (hh : tr'.height t=tr.height t)
    (hm : ∀r i,i∈is → i.bus=bus → i.msgVal tr' t r pub=i.msgVal tr t r pub)
    (hu : ∀r i,i∈is → i.multNat tr' t r pub=i.multNat tr t r pub) :
    tableBusCount is tr' t pub bus sd msg=tableBusCount is tr t pub bus sd msg := by
  unfold tableBusCount
  rw [hh]
  have hs : ∀rs : List Nat,∀a,
    rs.foldr (fun r acc=>is.foldr (fun i acc'=>
      (if i.bus=bus ∧ i.send=sd ∧ i.msgVal tr' t r pub=msg then i.multNat tr' t r pub else 0)+acc') acc) a=
    rs.foldr (fun r acc=>is.foldr (fun i acc'=>
      (if i.bus=bus ∧ i.send=sd ∧ i.msgVal tr t r pub=msg then i.multNat tr t r pub else 0)+acc') acc) a := by
    intro rs
    induction rs with
    | nil => intros; rfl
    | cons r rs ih =>
      intro a
      simp only [List.foldr_cons]
      rw [ih]
      apply fold_sum_congr
      intro i hi
      by_cases hb : i.bus=bus
      · rw [hm r i hi hb,hu r i hi]
      · simp [hb]
  exact hs _ 0

theorem counterPatch_multNat {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (users : Nat→Nat) {i : Interaction} (hi : i∈RcptV3.interactions) :
    i.multNat (counterPatch tr t users) t r pub=i.multNat tr t r pub := by
  have he : ∀e∈i.mult,e.eval (counterPatch tr t users) t r pub=e.eval tr t r pub := by
    intro e he
    apply counterPatch_eval
    have hm := List.mem_flatMap.mpr ⟨i,hi,he⟩
    have := List.all_eq_true.mp multiplicities_counter_free e hm
    simpa using this
  unfold Interaction.multNat
  have go : ∀es,(∀e∈es,e∈i.mult) → ∀k,
    Interaction.multNat.go (counterPatch tr t users) t r pub es k=
    Interaction.multNat.go tr t r pub es k := by
    intro es
    induction es with
    | nil => intros; rfl
    | cons e es ih =>
      intro hm k
      simp only [Interaction.multNat.go]
      rw [he e (hm e (by simp)),ih (by intro e he; exact hm e (by simp [he]))]
  exact go _ (fun _ he=>he) 0

theorem counterPatch_other_bus (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (users : Nat→Nat) (bus : Nat) (hb : bus≠B_BND) (sd : Bool) (msg : List Fp) :
    tableBusCount candidateTable.interactions (counterPatch tr t users) t pub bus sd msg=
      tableBusCount candidateTable.interactions tr t pub bus sd msg := by
  apply tableBusCount_congr
  · rfl
  · intro r i hi hib
    exact counterPatch_other_message users hi (by omega)
  · intro r i hi
    exact counterPatch_multNat users hi

end ZkFormal.NearV3.Assembly.RoutingQCandidate
