import ZkFormal.Near.Extract.Common

/-!
# ZkFormal.Near.Extract.BusCount — `tableBusCount` as a count in a message list

`tableBusCount is tr t pub b s m` (L4) is a fold over rows and interactions.
`tableBusCount_eq` rewrites it as the count of `m` in the list of all active
messages (`rowTraffic`, each message repeated by its multiplicity), which is
how the table-view extractions establish `TableTraffic`.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]

/-- Messages of row `r` on bus `b`, side `s` (with multiplicity). -/
def rowTraffic (is : List Interaction) (tr : Trace F) (t r : Nat) (pub : List F) (b : Nat)
    (s : Bool) : List (List F) :=
  is.flatMap fun i =>
    if i.bus = b ∧ i.send = s then List.replicate (i.multNat tr t r pub) (i.msgVal tr t r pub) else []

theorem count_rowTraffic (is : List Interaction) (tr : Trace F) (t r : Nat) (pub : List F)
    (b : Nat) (s : Bool) (m : List F) :
    is.foldr (fun i acc' =>
      (if i.bus = b ∧ i.send = s ∧ i.msgVal tr t r pub = m then i.multNat tr t r pub else 0) + acc') 0 =
    (rowTraffic is tr t r pub b s).count m := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.foldr_cons, rowTraffic, List.flatMap_cons, List.count_append] at ih ⊢
    rw [ih]
    congr 1
    by_cases hb : i.bus = b ∧ i.send = s
    · rw [if_pos hb, List.count_replicate]
      by_cases hm : i.msgVal tr t r pub = m
      · simp [hb.1, hb.2, hm]
      · have : ¬ (i.msgVal tr t r pub == m) = true := by simpa using hm
        simp [hm, this]
    · rw [if_neg hb]
      have : ¬ (i.bus = b ∧ i.send = s ∧ i.msgVal tr t r pub = m) := fun h => hb ⟨h.1, h.2.1⟩
      simp [this]

theorem foldr_add_acc {α : Type} (l : List α) (g : α → Nat) (acc : Nat) :
    l.foldr (fun i a => g i + a) acc = l.foldr (fun i a => g i + a) 0 + acc := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.foldr_cons]; rw [ih]; omega

theorem foldr_rows (is : List Interaction) (tr : Trace F) (t : Nat) (pub : List F) (b : Nat)
    (s : Bool) (m : List F) (rows : List Nat) :
    rows.foldr (fun r acc =>
      is.foldr (fun i acc' =>
        (if i.bus = b ∧ i.send = s ∧ i.msgVal tr t r pub = m then i.multNat tr t r pub else 0)
          + acc') acc) 0 =
    (rows.flatMap fun r => rowTraffic is tr t r pub b s).count m := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.foldr_cons, List.flatMap_cons, List.count_append]
    rw [← ih, ← count_rowTraffic, foldr_add_acc]

/-- **`tableBusCount` is a count in the list of active messages.** -/
theorem tableBusCount_eq (is : List Interaction) (tr : Trace F) (t : Nat) (pub : List F) (b : Nat)
    (s : Bool) (m : List F) :
    tableBusCount is tr t pub b s m =
      ((List.range (tr.height t)).flatMap fun r => rowTraffic is tr t r pub b s).count m :=
  foldr_rows is tr t pub b s m _

end

end ZkFormal.Near
