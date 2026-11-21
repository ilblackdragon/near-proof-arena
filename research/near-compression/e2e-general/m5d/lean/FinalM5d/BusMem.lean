import StateM5a.ChipStub
import ZkFormal.Sha.Sound.Bridge

/-!
# FinalM5d.BusMem — a received message was sent (and conversely), from `Holds`

Generic (any `Air`), on lane B's list form of the buses (`StateM5a.Bus.busList`):

* `mem_busList`: `m ∈ busList A tr pub b s` iff some row `r` of some table `t` has an interaction
  on `(b, s)` with nonzero multiplicity and message `m`;
* `recv_sent` / `sent_recv`: under `Holds`, a received message is sent and a sent one received
  (count equality on the bus);
* `occ_of_holds`: the same at the level of one interaction occurrence, the form the whole-AIR
  proofs use (`Occ A tr pub b s m`).
-/

namespace FinalM5d.BusMem

open ZkFormal.Air ZkFormal.Algebra StateM5a.Bus

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]

/-- An occurrence of message `m` on `(b, s)`: table `t`, row `r`, an interaction with nonzero
multiplicity. -/
def Occ (A : Air) (tr : Trace F) (pub : List F) (b : Nat) (s : Bool) (m : List F) : Prop :=
  ∃ t, ∃ ht : t < A.tables.length, ∃ r, r < tr.height t ∧ ∃ i ∈ (A.tables[t]'ht).interactions,
    i.bus = b ∧ i.send = s ∧ i.multNat tr t r pub ≠ 0 ∧ i.msgVal tr t r pub = m

theorem mem_rowBusList {is : List Interaction} {tr : Trace F} {t r : Nat} {pub : List F} {b : Nat}
    {s : Bool} {m : List F} :
    m ∈ rowBusList is tr t r pub b s ↔
      ∃ i ∈ is, i.bus = b ∧ i.send = s ∧ i.multNat tr t r pub ≠ 0 ∧ i.msgVal tr t r pub = m := by
  simp only [rowBusList, List.mem_flatMap]
  constructor
  · rintro ⟨i, hi, hm⟩
    split at hm
    · rename_i hbs
      obtain ⟨hn, rfl⟩ := List.mem_replicate.1 hm
      exact ⟨i, hi, hbs.1, hbs.2, hn, rfl⟩
    · simp at hm
  · rintro ⟨i, hi, hb, hs, hn, rfl⟩
    refine ⟨i, hi, ?_⟩
    simp only [hb, hs, and_self, ite_true]
    exact List.mem_replicate.2 ⟨hn, rfl⟩

theorem mem_go {tr : Trace F} {pub : List F} {b : Nat} {s : Bool} {m : List F} :
    ∀ (Ts : List Table) (t0 : Nat), m ∈ busList.go tr pub b s Ts t0 ↔
      ∃ j, ∃ hj : j < Ts.length, ∃ r, r < tr.height (t0 + j) ∧
        m ∈ rowBusList (Ts[j]'hj).interactions tr (t0 + j) r pub b s
  | [], t0 => by simp [busList.go]
  | T :: Ts, t0 => by
    simp only [busList.go, List.mem_append, tableBusList, List.mem_flatMap, List.mem_range]
    rw [mem_go Ts (t0 + 1)]
    constructor
    · rintro (⟨r, hr, hm⟩ | ⟨j, hj, r, hr, hm⟩)
      · exact ⟨0, by simp, r, by simpa using hr, by simpa using hm⟩
      · refine ⟨j + 1, by simp; omega, r, ?_, ?_⟩
        · rw [show t0 + (j + 1) = t0 + 1 + j by omega]; exact hr
        · rw [show t0 + (j + 1) = t0 + 1 + j by omega]; simpa using hm
    · rintro ⟨j, hj, r, hr, hm⟩
      rcases j with _ | j
      · exact .inl ⟨r, by simpa using hr, by simpa using hm⟩
      · refine .inr ⟨j, by simp at hj; omega, r, ?_, ?_⟩
        · rw [show t0 + 1 + j = t0 + (j + 1) by omega]; exact hr
        · rw [show t0 + 1 + j = t0 + (j + 1) by omega]; simpa using hm

theorem mem_busList {A : Air} {tr : Trace F} {pub : List F} {b : Nat} {s : Bool} {m : List F} :
    m ∈ busList A tr pub b s ↔ Occ A tr pub b s m := by
  unfold busList Occ
  rw [mem_go A.tables 0]
  constructor
  · rintro ⟨j, hj, r, hr, hm⟩
    obtain ⟨i, hi, h1, h2, h3, h4⟩ := mem_rowBusList.1 hm
    exact ⟨j, hj, r, by simpa using hr, i, hi, h1, h2, by simpa using h3, by simpa using h4⟩
  · rintro ⟨t, ht, r, hr, i, hi, h1, h2, h3, h4⟩
    exact ⟨t, ht, r, by simpa using hr, mem_rowBusList.2 ⟨i, hi, h1, h2, by simpa using h3, by simpa using h4⟩⟩

theorem mem_iff_of_holds {A : Air} {pub : List F} {tr : Trace F} (h : Holds A pub tr) (b : Nat)
    (m : List F) : m ∈ busList A tr pub b true ↔ m ∈ busList A tr pub b false := by
  rw [← List.count_pos_iff, ← List.count_pos_iff, count_busList, count_busList, h.balance b m]

/-- **A received message was sent.** -/
theorem recv_sent {A : Air} {pub : List F} {tr : Trace F} (h : Holds A pub tr) {b : Nat}
    {m : List F} (hm : Occ A tr pub b false m) : Occ A tr pub b true m :=
  mem_busList.1 ((mem_iff_of_holds h b m).2 (mem_busList.2 hm))

/-- **A sent message was received.** -/
theorem sent_recv {A : Air} {pub : List F} {tr : Trace F} (h : Holds A pub tr) {b : Nat}
    {m : List F} (hm : Occ A tr pub b true m) : Occ A tr pub b false m :=
  mem_busList.1 ((mem_iff_of_holds h b m).1 (mem_busList.2 hm))

/-- A single-bit multiplicity is nonzero iff the bit is `1`. -/
theorem multNat_one {i : Interaction} {g : Expr} (hg : i.mult = [g]) {tr : Trace F} {t r : Nat}
    {pub : List F} : i.multNat tr t r pub ≠ 0 ↔ g.eval tr t r pub = 1 := by
  simp only [Interaction.multNat, hg, Interaction.multNat.go]
  split <;> simp_all

/-- An occurrence from a concrete row and interaction. -/
theorem occ_of {A : Air} {tr : Trace F} {pub : List F} {t : Nat} (ht : t < A.tables.length) {r : Nat}
    (hr : r < tr.height t) {i : Interaction} (hi : i ∈ (A.tables[t]'ht).interactions)
    (hn : i.multNat tr t r pub ≠ 0) : Occ A tr pub i.bus i.send (i.msgVal tr t r pub) :=
  ⟨t, ht, r, hr, i, hi, rfl, rfl, hn, rfl⟩

end

end FinalM5d.BusMem
