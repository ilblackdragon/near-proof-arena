import ZkFormal.Udr.Np.QueryFacts

/-!
# ZkFormal.Udr.Np.ShapeLate — basic shape facts for the late rounds

* a shaped transcript with an entry has its header, admissible, and its
  slots are the schedule;
* after `8` entries there are at least `4` challenges and two clear-text parts;
* `push` / `pushChal` keep the header, and append to oracles / elems / chals.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

section
variable {K O : Type}

theorem pushChal_entries (τ : PT K O) (c : K) : (τ.pushChal c).entries = τ.entries ++ [.chal c] := rfl
theorem push_entries (τ : PT K O) (m : List (PartV K O)) :
    (τ.push m).entries = τ.entries ++ [.msg m] := rfl

theorem header_append (τ : PT K O) (e : Entry K O) (h : τ.entries ≠ []) :
    (⟨τ.cb, τ.entries ++ [e]⟩ : PT K O).header? = τ.header? := by
  rcases τ with ⟨cb, es⟩
  rcases es with _ | ⟨e0, es⟩
  · exact absurd rfl h
  · show PT.header? ⟨cb, e0 :: (es ++ [e])⟩ = PT.header? ⟨cb, e0 :: es⟩
    rcases e0 with ps | c
    · rcases ps with _ | ⟨p, ps⟩
      · rfl
      · rcases p <;> rfl
    · rfl

theorem pushChal_header (τ : PT K O) (c : K) (h : τ.entries ≠ []) :
    (τ.pushChal c).header? = τ.header? := header_append τ _ h

theorem push_header (τ : PT K O) (m : List (PartV K O)) (h : τ.entries ≠ []) :
    (τ.push m).header? = τ.header? := header_append τ _ h

theorem pushChal_chals (τ : PT K O) (c : K) : (τ.pushChal c).chals = τ.chals ++ [c] := by
  simp [PT.pushChal, PT.chals, List.filterMap_append]

theorem pushChal_oracles (τ : PT K O) (c : K) : (τ.pushChal c).oracles = τ.oracles := by
  simp [PT.pushChal, PT.oracles, List.flatMap_append]

theorem pushChal_elems (τ : PT K O) (c : K) : (τ.pushChal c).elems = τ.elems := by
  simp [PT.pushChal, PT.elems, List.flatMap_append]

theorem push_chals (τ : PT K O) (m : List (PartV K O)) : (τ.push m).chals = τ.chals := by
  simp [PT.push, PT.chals, List.filterMap_append]

theorem push_oracles (τ : PT K O) (m : List (PartV K O)) :
    ∃ os, (τ.push m).oracles = τ.oracles ++ os := by
  simp [PT.push, PT.oracles, List.flatMap_append]

theorem push_elems (τ : PT K O) (m : List (PartV K O)) :
    ∃ es, (τ.push m).elems = τ.elems ++ es := by
  simp [PT.push, PT.elems, List.flatMap_append]

end

section
variable (A : Air) (prm : Params)

/-- A shaped transcript with at least one entry has an admissible header,
and its slots are the schedule. -/
theorem sh_header (τ : PTn) (hs : Shaped (Vnp A prm) τ) (hE : 1 ≤ τ.entries.length) :
    ∃ hdr, τ.header? = some hdr ∧ headerOk A prm hdr = true ∧
      (Vnp A prm).slots τ = schedule A prm hdr := by
  cases hh : τ.header? with
  | some hdr => exact ⟨hdr, rfl, hs.1 hdr hh, by simp [IopSpec.slots, hh, Vnp, Iop.verifier]⟩
  | none =>
    exfalso
    obtain ⟨s, hs0, hfit⟩ := hs.2.2 0 (by omega)
    simp only [IopSpec.slots, hh, Vnp, Iop.verifier] at hs0
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs0
    subst hs0
    rcases τ with ⟨cb, es⟩
    rcases es with _ | ⟨e0, es⟩
    · simp at hE
    · simp only [List.getElem_cons_zero] at hfit
      rcases e0 with ps | c
      · obtain ⟨hl, hk⟩ := hfit
        simp only [List.length_cons, List.length_nil] at hl
        obtain ⟨pt, hpt, hf⟩ := hk 0 (by omega)
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hpt
        subst hpt
        rcases ps with _ | ⟨p, ps⟩
        · simp at hl
        · rcases p with l | o | xs
          · simp [PT.header?] at hh
          · exact hf
          · exact hf
      · exact hfit

theorem fits_chal_iff (e : Entry Fp8 (Oracle Fp)) (b : Bool) (h : Entry.Fits e (.chal b)) :
    ∃ c, e = .chal c := by
  rcases e with ps | c
  · exact absurd h id
  · exact ⟨c, rfl⟩

/-- After eight entries there are at least four challenges. -/
theorem sh_chals4 (τ : PTn) (hs : Shaped (Vnp A prm) τ) (hE : 8 ≤ τ.entries.length) :
    4 ≤ τ.chals.length := by
  obtain ⟨hdr, hh, -, hsl⟩ := sh_header A prm τ hs (by omega)
  have hc : ∀ k, k < 8 → k % 2 = 1 → ∃ c, τ.entries[k]? = some (.chal c) := by
    intro k hk hodd
    obtain ⟨s, hs0, hfit⟩ := hs.2.2 k (by omega)
    rw [hsl] at hs0
    have : ∃ b, (schedule A prm hdr)[k]? = some (.chal b) := by
      simp only [schedule]
      rw [List.getElem?_append_left (by simp; omega)]
      have : k = 1 ∨ k = 3 ∨ k = 5 ∨ k = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> simp
    obtain ⟨b, hb⟩ := this
    rw [hb, Option.some.injEq] at hs0
    subst hs0
    obtain ⟨c, hc⟩ := fits_chal_iff _ _ hfit
    exact ⟨c, by rw [List.getElem?_eq_getElem (by omega), hc]⟩
  rcases τ with ⟨cb, es⟩
  simp only at hE hc ⊢
  match es, hE, hc with
  | e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: es, _, hc =>
    obtain ⟨c1, h1⟩ := hc 1 (by omega) rfl
    obtain ⟨c3, h3⟩ := hc 3 (by omega) rfl
    obtain ⟨c5, h5⟩ := hc 5 (by omega) rfl
    obtain ⟨c7, h7⟩ := hc 7 (by omega) rfl
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h1 h3 h5 h7
    subst h1 h3 h5 h7
    simp only [PT.chals, List.filterMap_cons]
    rcases e0 with _ | _ <;> rcases e2 with _ | _ <;> rcases e4 with _ | _ <;> rcases e6 with _ | _ <;>
      simp

end
end ZkFormal.Udr.Np
