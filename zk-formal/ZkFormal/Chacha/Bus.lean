import ZkFormal.V2.Air

/-!
# ZkFormal.Chacha.Bus — bus counts as message lists; matching receives with sends

`tableBusCount` is the count of a message in the list of active messages
(`tableBusCount_eq`, as in `Near.Extract.BusCount`).  `recv_matched`: in a `HoldsP` trace,
if every sender on bus `b` (tables and public segments) is one known table `tc`, every
active receive on `b` equals an active send of `tc` at some row.
-/

namespace ZkFormal.Chacha

open ZkFormal.Air ZkFormal.V2

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

theorem tableBusCount_eq (is : List Interaction) (tr : Trace F) (t : Nat) (pub : List F) (b : Nat)
    (s : Bool) (m : List F) :
    tableBusCount is tr t pub b s m =
      ((List.range (tr.height t)).flatMap fun r => rowTraffic is tr t r pub b s).count m := by
  unfold tableBusCount
  generalize List.range (tr.height t) = rows
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.foldr_cons, List.flatMap_cons, List.count_append]
    rw [← ih, ← count_rowTraffic, foldr_add_acc]

/-- A positive table count comes from an active interaction. -/
theorem exists_of_tableBusCount {is : List Interaction} {tr : Trace F} {t : Nat} {pub : List F}
    {b : Nat} {s : Bool} {m : List F} (h : tableBusCount is tr t pub b s m ≠ 0) :
    ∃ r, r < tr.height t ∧ ∃ i ∈ is, i.bus = b ∧ i.send = s ∧ i.msgVal tr t r pub = m ∧
      i.multNat tr t r pub ≠ 0 := by
  rw [tableBusCount_eq] at h
  obtain ⟨x, hx, hxm⟩ : ∃ x ∈ (List.range (tr.height t)).flatMap fun r => rowTraffic is tr t r pub b s, x = m := by
    have := List.count_pos_iff.mp (Nat.pos_of_ne_zero h)
    exact ⟨m, this, rfl⟩
  subst hxm
  obtain ⟨r, hr, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp hx
  by_cases hbs : i.bus = b ∧ i.send = s
  · rw [if_pos hbs] at hx
    obtain ⟨hrep, hm⟩ := List.mem_replicate.mp hx
    exact ⟨r, List.mem_range.mp hr, i, hi, hbs.1, hbs.2, hm.symm, hrep⟩
  · rw [if_neg hbs] at hx; simp at hx

/-- An active interaction contributes to the table count. -/
theorem tableBusCount_pos {is : List Interaction} {tr : Trace F} {t : Nat} {pub : List F}
    {r : Nat} (hr : r < tr.height t) {i : Interaction} (hi : i ∈ is) (hm : i.multNat tr t r pub ≠ 0) :
    tableBusCount is tr t pub i.bus i.send (i.msgVal tr t r pub) ≠ 0 := by
  rw [tableBusCount_eq]
  apply Nat.pos_iff_ne_zero.mp
  apply List.count_pos_iff.mpr
  apply List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, ?_⟩
  apply List.mem_flatMap.mpr ⟨i, hi, ?_⟩
  rw [if_pos ⟨rfl, rfl⟩]
  exact List.mem_replicate.mpr ⟨hm, rfl⟩

theorem busCount_go_pos (tr : Trace F) (pub : List F) (b : Nat) (s : Bool) (m : List F) :
    ∀ (Ts : List Table) (k : Nat), busCount.go tr pub b s m Ts k ≠ 0 →
      ∃ t, t < Ts.length ∧ tableBusCount Ts[t]!.interactions tr (k + t) pub b s m ≠ 0
  | [], _, h => by simp [busCount.go] at h
  | T :: Ts, k, h => by
    simp only [busCount.go] at h
    by_cases h0 : tableBusCount T.interactions tr k pub b s m = 0
    · rw [h0, Nat.zero_add] at h
      obtain ⟨t, ht, h'⟩ := busCount_go_pos tr pub b s m Ts (k + 1) h
      exact ⟨t + 1, by simp; omega, by rw [show k + (t + 1) = k + 1 + t by omega]; simpa using h'⟩
    · exact ⟨0, by simp, by simpa using h0⟩

theorem busCount_go_ge (tr : Trace F) (pub : List F) (b : Nat) (s : Bool) (m : List F) :
    ∀ (Ts : List Table) (k t : Nat), t < Ts.length →
      tableBusCount Ts[t]!.interactions tr (k + t) pub b s m ≤ busCount.go tr pub b s m Ts k
  | [], _, _, h => by simp at h
  | T :: Ts, k, 0, _ => by simp [busCount.go]
  | T :: Ts, k, t + 1, h => by
    simp only [busCount.go]
    have := busCount_go_ge tr pub b s m Ts (k + 1) t (by simp at h; omega)
    rw [show k + 1 + t = k + (t + 1) by omega] at this
    simp only [List.getElem!_cons_succ] at this ⊢
    omega

end

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F] [PubVal F]

/-- Public messages on bus `b`, side `send`, have count `0` if no segment of that side uses `b`. -/
theorem pubCount_zero {AP : AirP} {pub : List F} {b : Nat} {s : Bool}
    (h : ∀ seg ∈ AP.pubSegs, seg.bus = b → seg.send ≠ s) (m : List F) : pubCount AP pub b s m = 0 := by
  unfold pubCount pubMsgs
  apply List.length_eq_zero_iff.mpr
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  obtain ⟨seg, hseg, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
  simp only [decide_eq_true_eq, Prod.mk.injEq, not_and]
  intro hb hs
  exact absurd hs (h seg hseg hb)

/-- **Receives are matched by sends of the unique sending table.** -/
theorem recv_matched {AP : AirP} {pub : List F} {tr : Trace F} (hH : HoldsP AP pub tr)
    {b tc : Nat} (htc : tc < AP.tables.length)
    (honly : ∀ t, t < AP.tables.length → t ≠ tc → ∀ i ∈ AP.tables[t]!.interactions, i.bus = b → i.send = false)
    (hpub : ∀ seg ∈ AP.pubSegs, seg.bus = b → seg.send = false)
    {t r : Nat} (ht : t < AP.tables.length) (hr : r < tr.height t) {i : Interaction}
    (hi : i ∈ AP.tables[t]!.interactions) (hb : i.bus = b) (hs : i.send = false)
    (hm : i.multNat tr t r pub ≠ 0) :
    ∃ r', r' < tr.height tc ∧ ∃ i' ∈ AP.tables[tc]!.interactions, i'.bus = b ∧ i'.send = true ∧
      i'.msgVal tr tc r' pub = i.msgVal tr t r pub ∧ i'.multNat tr tc r' pub ≠ 0 := by
  have hbal := hH.balance b (i.msgVal tr t r pub)
  rw [pubCount_zero (fun seg h1 h2 => by rw [hpub seg h1 h2] at *; simp at *) _] at hbal
  have hrecv : busCount AP.toAir tr pub b false (i.msgVal tr t r pub) ≠ 0 := by
    have h1 := tableBusCount_pos hr hi hm
    rw [hb, hs] at h1
    have h2 := busCount_go_ge tr pub b false (i.msgVal tr t r pub) AP.tables 0 t ht
    simp only [Nat.zero_add] at h2
    unfold busCount; omega
  have hsend : busCount AP.toAir tr pub b true (i.msgVal tr t r pub) ≠ 0 := by omega
  obtain ⟨t', ht', hc⟩ := busCount_go_pos tr pub b true _ AP.tables 0 hsend
  simp only [Nat.zero_add] at hc
  obtain ⟨r', hr', i', hi', hb', hs', hmsg, hm'⟩ := exists_of_tableBusCount hc
  by_cases e : t' = tc
  · subst e; exact ⟨r', hr', i', hi', hb', hs', hmsg, hm'⟩
  · have := honly t' ht' e i' hi' hb'; rw [this] at hs'; simp at hs'

end

end ZkFormal.Chacha
