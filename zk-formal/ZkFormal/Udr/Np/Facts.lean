import ZkFormal.Udr.Np.Frame

/-!
# ZkFormal.Udr.Np.Facts — what a shaped transcript looks like

Header presence and admissibility, entries fit the schedule, number of
challenges (`E / 2`), the first oracles and the finals.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

section
variable {A : Air} {prm : Params}

theorem fits_header {p : PartV Fp8 (Oracle Fp)} {n : Nat} (h : PartV.Fits p (.header n)) :
    ∃ l, p = .header l := by
  cases p with
  | header l => exact ⟨l, rfl⟩
  | _ => exact absurd h id

theorem fits_oracle {p : PartV Fp8 (Oracle Fp)} {ms : List (Nat × Nat)} (h : PartV.Fits p (.oracle ms)) :
    ∃ o, p = .oracle o := by
  cases p with
  | oracle o => exact ⟨o, rfl⟩
  | _ => exact absurd h id

theorem fits_elems {p : PartV Fp8 (Oracle Fp)} {n : Nat} (h : PartV.Fits p (.elems n)) :
    ∃ xs, p = .elems xs ∧ xs.length = n := by
  cases p with
  | elems xs => exact ⟨xs, rfl, h⟩
  | _ => exact absurd h id

theorem fits_msg {e : Entry Fp8 (Oracle Fp)} {parts : List Part} (h : Entry.Fits e (.msg parts)) :
    ∃ ps : List (PartV Fp8 (Oracle Fp)), e = .msg ps ∧ ps.length = parts.length ∧
      ∀ k (hk : k < ps.length), ∃ pt, parts[k]? = some pt ∧ PartV.Fits ps[k] pt := by
  cases e with
  | msg ps => exact ⟨ps, rfl, h⟩
  | chal => exact absurd h id

theorem fits_chal {e : Entry Fp8 (Oracle Fp)} {b : Bool} (h : Entry.Fits e (.chal b)) :
    ∃ c, e = .chal c := by
  cases e with
  | chal c => exact ⟨c, rfl⟩
  | msg => exact absurd h id

/-- The first slot of every slot list is a message starting with the header. -/
theorem slots_zero (τ : PTn) : ∃ rest, ((Vnp A prm).slots τ)[0]? =
    some (.msg (.header A.tables.length :: rest)) := by
  unfold IopSpec.slots
  split
  · exact ⟨_, rfl⟩
  · exact ⟨[], rfl⟩

theorem shaped_hdr {τ : PTn} (hs : Shaped (Vnp A prm) τ) (hne : τ.entries ≠ []) :
    ∃ l, τ.header? = some l ∧ headerOk A prm l = true ∧ (Vnp A prm).slots τ = schedule A prm l := by
  obtain ⟨s, hs1, hs2⟩ := hs.2.2 0 (List.length_pos_iff.mpr hne)
  obtain ⟨rest, hr⟩ := slots_zero (A := A) (prm := prm) τ
  rw [hr] at hs1; cases hs1
  obtain ⟨ps, hps, hlen, hfit⟩ := fits_msg hs2
  obtain ⟨pt, hpt, hf⟩ := hfit 0 (by simp only [List.length_cons] at hlen; omega)
  simp only [List.length_cons] at hlen
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hpt
  subst hpt
  obtain ⟨l, hl⟩ := fits_header hf
  have hh : τ.header? = some l := by
    obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil hne
    have h0 : τ.entries[0]'(List.length_pos_iff.mpr hne) = e := by simp only [he, List.getElem_cons_zero]
    rw [h0] at hps; subst hps
    obtain ⟨p0, ps', rfl⟩ : ∃ p0 ps', ps = p0 :: ps' := List.exists_cons_of_ne_nil (by
      intro h; subst h; simp at hlen)
    simp only [List.getElem_cons_zero] at hl; subst hl
    unfold PT.header?; rw [he]
  exact ⟨l, hh, (verifier_headerOk (hs.1 l hh)).1, by unfold IopSpec.slots; rw [hh]; rfl⟩

theorem shaped_fits {τ : PTn} (hs : Shaped (Vnp A prm) τ) {l : List Nat} (hl : τ.header? = some l)
    (k : Nat) (hk : k < τ.entries.length) :
    ∃ s, (schedule A prm l)[k]? = some s ∧ Entry.Fits τ.entries[k] s := by
  obtain ⟨s, h1, h2⟩ := hs.2.2 k hk
  refine ⟨s, ?_, h2⟩
  unfold IopSpec.slots at h1; rw [hl] at h1; exact h1

/-! ## Number of challenges -/

def isChalE : Entry Fp8 (Oracle Fp) → Bool
  | .chal _ => true
  | .msg _ => false

theorem chals_cons (cb : Bytes) (e : Entry Fp8 (Oracle Fp)) (es : List (Entry Fp8 (Oracle Fp))) :
    (PT.chals (⟨cb, e :: es⟩ : PTn)).length = (if isChalE e then 1 else 0) + (PT.chals ⟨cb, es⟩).length := by
  cases e <;> simp [PT.chals, isChalE] <;> omega

theorem chals_length_alt (cb : Bytes) : ∀ es : List (Entry Fp8 (Oracle Fp)),
    (∀ k (hk : k < es.length), isChalE es[k] = true ↔ k % 2 = 1) →
    (PT.chals (⟨cb, es⟩ : PTn)).length = es.length / 2
  | [], _ => rfl
  | [a], h => by
    have := h 0 (by simp)
    rw [chals_cons]
    simp only [List.getElem_cons_zero, Nat.zero_mod] at this
    have ha : isChalE a = false := by
      cases hh : isChalE a
      · rfl
      · rw [hh] at this; simp at this
    rw [ha]; simp [PT.chals]
  | a :: b :: es, h => by
    have h0 := h 0 (by simp)
    have h1 := h 1 (by simp)
    simp only [List.getElem_cons_zero, Nat.zero_mod, List.getElem_cons_succ] at h0 h1
    have ha : isChalE a = false := by
      cases hh : isChalE a
      · rfl
      · rw [hh] at h0; simp at h0
    have hb : isChalE b = true := by simpa using h1
    rw [chals_cons, chals_cons, chals_length_alt cb es (fun k hk => by
      have := h (k + 2) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [this]; omega), ha, hb]
    simp only [List.length_cons]
    simp; omega

theorem shaped_chals_length {τ : PTn} (hs : Shaped (Vnp A prm) τ) :
    τ.chals.length = τ.entries.length / 2 := by
  by_cases hne : τ.entries = []
  · unfold PT.chals; rw [hne]; rfl
  obtain ⟨l, hl, _, _⟩ := shaped_hdr hs hne
  have : τ = ⟨τ.cb, τ.entries⟩ := rfl
  rw [this]
  refine chals_length_alt τ.cb τ.entries fun k hk => ?_
  obtain ⟨s, h1, h2⟩ := shaped_fits hs hl k hk
  obtain ⟨ps, hps⟩ := schedule_pairs A prm l
  rw [hps] at h1
  have halt := alt_pairs _ ps k s h1
  cases s with
  | msg parts =>
    obtain ⟨_, he, _⟩ := fits_msg h2
    rw [he]; simp only [isChalE, Bool.false_eq_true, false_iff]
    simp only [slotIsMsg, true_iff] at halt; omega
  | chal b =>
    obtain ⟨_, he⟩ := fits_chal h2
    rw [he]; simp only [isChalE, true_iff]
    simp only [slotIsMsg, Bool.false_eq_true, false_iff] at halt; omega

/-! ## Early entries -/

theorem sched_get (l : List Nat) :
    (schedule A prm l)[0]? = some (.msg [.header A.tables.length,
      .oracle ((layout A prm l).map fun L => (L.lde, L.width))]) ∧
    (schedule A prm l)[2]? = some (.msg []) ∧
    (schedule A prm l)[4]? = some (.msg [.oracle ((layout A prm l).map fun L => (L.lde, 8 * L.aux)),
      .elems ((layout A prm l).map fun L => L.sendG + L.recvG).sum]) ∧
    (schedule A prm l)[6]? = some (.msg [.oracle ((layout A prm l).map fun L => (L.lde, 8 * L.quot))]) ∧
    (schedule A prm l)[7]? = some (.chal true) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem fits_two {e : Entry Fp8 (Oracle Fp)} {p q : Part} (h : Entry.Fits e (.msg [p, q])) :
    ∃ a b, e = .msg [a, b] ∧ PartV.Fits a p ∧ PartV.Fits b q := by
  obtain ⟨ps, rfl, hlen, hf⟩ := fits_msg h
  match ps, hlen with
  | [a, b], _ =>
    obtain ⟨_, h0, f0⟩ := hf 0 (by simp)
    obtain ⟨_, h1, f1⟩ := hf 1 (by simp)
    simp at h0 h1; subst h0; subst h1
    exact ⟨a, b, rfl, f0, f1⟩

theorem fits_one {e : Entry Fp8 (Oracle Fp)} {p : Part} (h : Entry.Fits e (.msg [p])) :
    ∃ a, e = .msg [a] ∧ PartV.Fits a p := by
  obtain ⟨ps, rfl, hlen, hf⟩ := fits_msg h
  match ps, hlen with
  | [a], _ =>
    obtain ⟨_, h0, f0⟩ := hf 0 (by simp)
    simp at h0; subst h0
    exact ⟨a, rfl, f0⟩

theorem fits_nil {e : Entry Fp8 (Oracle Fp)} (h : Entry.Fits e (.msg [])) : e = .msg [] := by
  obtain ⟨ps, rfl, hlen, _⟩ := fits_msg h
  match ps, hlen with
  | [], _ => rfl

theorem oracles_cons (cb : Bytes) (e : Entry Fp8 (Oracle Fp)) (es : List (Entry Fp8 (Oracle Fp))) :
    PT.oracles (⟨cb, e :: es⟩ : PTn) = PT.oracles (⟨cb, [e]⟩ : PTn) ++ PT.oracles ⟨cb, es⟩ := by
  simp [PT.oracles]

theorem elems_cons (cb : Bytes) (e : Entry Fp8 (Oracle Fp)) (es : List (Entry Fp8 (Oracle Fp))) :
    PT.elems (⟨cb, e :: es⟩ : PTn) = PT.elems (⟨cb, [e]⟩ : PTn) ++ PT.elems ⟨cb, es⟩ := by
  simp [PT.elems]

/-- From `E ≥ 1`: at least one oracle. -/
theorem shaped_oracles1 {τ : PTn} (hs : Shaped (Vnp A prm) τ) (hE : 1 ≤ τ.entries.length) :
    1 ≤ τ.oracles.length := by
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  obtain ⟨l, hl, _, _⟩ := shaped_hdr hs hne
  obtain ⟨s, h1, h2⟩ := shaped_fits hs hl 0 (by omega)
  rw [(sched_get l).1] at h1; cases h1
  obtain ⟨a, b, he, ha, hb⟩ := fits_two h2
  obtain ⟨o, rfl⟩ := fits_oracle hb
  obtain ⟨l', rfl⟩ := fits_header ha
  obtain ⟨e, es, hes⟩ := List.exists_cons_of_ne_nil hne
  have : τ = ⟨τ.cb, e :: es⟩ := by rw [← hes]
  rw [this, oracles_cons]
  have h0 : e = τ.entries[0] := by simp [hes]
  rw [h0, he]; simp [PT.oracles]

/-- From `E ≥ 5`: at least two oracles, and the finals are present. -/
theorem shaped_oracles2 {τ : PTn} (hs : Shaped (Vnp A prm) τ) (hE : 5 ≤ τ.entries.length) :
    2 ≤ τ.oracles.length ∧ τ.elems ≠ [] := by
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  obtain ⟨l, hl, _, _⟩ := shaped_hdr hs hne
  obtain ⟨s, h1, h2⟩ := shaped_fits hs hl 0 (by omega)
  rw [(sched_get l).1] at h1; cases h1
  obtain ⟨a, b, he, ha, hb⟩ := fits_two h2
  obtain ⟨o, rfl⟩ := fits_oracle hb
  obtain ⟨l', rfl⟩ := fits_header ha
  obtain ⟨s4, h41, h42⟩ := shaped_fits hs hl 4 (by omega)
  rw [(sched_get l).2.2.1] at h41; cases h41
  obtain ⟨a4, b4, he4, ha4, hb4⟩ := fits_two h42
  obtain ⟨o4, rfl⟩ := fits_oracle ha4
  obtain ⟨xs, rfl, _⟩ := fits_elems hb4
  match hes : τ.entries, hE with
  | e0 :: e1 :: e2 :: e3 :: e4 :: es, _ =>
    have : τ = ⟨τ.cb, e0 :: e1 :: e2 :: e3 :: e4 :: es⟩ := by rw [← hes]
    have h0 : e0 = τ.entries[0] := by simp [hes]
    have h4 : e4 = τ.entries[4] := by simp [hes]
    rw [← h0] at he; rw [← h4] at he4
    subst he; subst he4
    rw [this]
    constructor
    · rw [oracles_cons, oracles_cons, oracles_cons, oracles_cons, oracles_cons]
      simp [PT.oracles]; omega
    · rw [elems_cons, elems_cons, elems_cons, elems_cons, elems_cons]
      simp [PT.elems]

end

end ZkFormal.Udr.Np
