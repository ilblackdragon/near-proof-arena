import ZkFormal.Near.Extract.SmallViews
import ZkFormal.Near.Extract.Segments

/-!
# ZkFormal.Near.Extract.MrkShape — the mrk table's node sequence is `merklize`

Pure arithmetic: a node sequence that obeys the mrk table's level rules (as
naturals) enumerates `mrkShape n`.  Within a level, only the level's last
node (`lil`) carries meaningful `s`/`odd`/`top`; its `i + 1 = s` makes `s`
small, so `sp + odd = 2·s` holds in `ℕ`.
-/

namespace ZkFormal.Near.MrkShape

/-- One node of the mrk table, as naturals / booleans. -/
structure ND where
  j : Nat
  i : Nat
  sp : Nat
  s : Nat
  odd : Bool
  lil : Bool
  top : Bool
  pr : Bool
  deriving Repr, Inhabited

/-- The level rules (`g t` = node `t`). -/
structure Rules (ds : List ND) : Prop where
  pr : ∀ t, t < ds.length → (ds.getD t default).pr = ((ds.getD t default).odd && (ds.getD t default).lil)
  lil : ∀ t, t < ds.length → (ds.getD t default).lil = true →
    (ds.getD t default).i + 1 = (ds.getD t default).s ∧
    (ds.getD t default).sp + (if (ds.getD t default).odd then 1 else 0) = 2 * (ds.getD t default).s
  top : ∀ t, t < ds.length → (ds.getD t default).lil = true →
    ((ds.getD t default).top = true ↔ (ds.getD t default).s = 1)
  step : ∀ t, t + 1 < ds.length → (ds.getD t default).lil = false →
    (ds.getD (t + 1) default).j = (ds.getD t default).j ∧
    (ds.getD (t + 1) default).i = (ds.getD t default).i + 1 ∧
    (ds.getD (t + 1) default).sp = (ds.getD t default).sp
  up : ∀ t, t + 1 < ds.length → (ds.getD t default).lil = true →
    (ds.getD t default).top = false ∧ (ds.getD (t + 1) default).j = (ds.getD t default).j + 1 ∧
    (ds.getD (t + 1) default).i = 0 ∧ (ds.getD (t + 1) default).sp = (ds.getD t default).s
  last : 0 < ds.length → (ds.getD (ds.length - 1) default).lil = true ∧
    (ds.getD (ds.length - 1) default).top = true

def shapeOf (ds : List ND) : List (Nat × Nat × Bool) := ds.map fun d => (d.j, d.i, !d.pr)

theorem shapeOf_drop (ds : List ND) (t m : Nat) (h : t + m ≤ ds.length) :
    shapeOf (ds.drop t) = ((List.range m).map fun k => let d := ds.getD (t + k) default; (d.j, d.i, !d.pr)) ++
      shapeOf (ds.drop (t + m)) := by
  induction m generalizing t with
  | zero => simp
  | succ m ih =>
    rw [ih t (by omega)]
    have : ds.drop (t + m) = ds.getD (t + m) default :: ds.drop (t + m + 1) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.drop_eq_getElem_cons (by omega)
    rw [this, List.range_succ, List.map_append, List.append_assoc]
    simp [shapeOf, show t + (m + 1) = t + m + 1 by omega]

/-- A level starting at node `t` (`i = 0`) produces `mrkLevels f j sp`. -/
theorem levels_from (ds : List ND) (hR : Rules ds) :
    ∀ f t, t < ds.length → (ds.getD t default).i = 0 → (ds.getD t default).sp + 1 ≤ f →
      shapeOf (ds.drop t) = mrkLevels f (ds.getD t default).j (ds.getD t default).sp := by
  intro f
  induction f with
  | zero => intro t _ _ h; omega
  | succ f ih =>
    intro t ht hi hf
    -- first `lil` at or after t
    have hex : ∃ m, t + m < ds.length ∧ (ds.getD (t + m) default).lil = true :=
      ⟨ds.length - 1 - t, by omega, by
        have := (hR.last (by omega)).1; rwa [show t + (ds.length - 1 - t) = ds.length - 1 by omega]⟩
    obtain ⟨m, ⟨hm, hlm⟩, hmin⟩ := exists_least hex
    have hnl : ∀ k, k < m → (ds.getD (t + k) default).lil = false := fun k hk => by
      cases h : (ds.getD (t + k) default).lil
      · rfl
      · exact absurd ⟨by omega, h⟩ (hmin k hk)
    -- the level's nodes
    have hlev : ∀ k, k ≤ m → (ds.getD (t + k) default).j = (ds.getD t default).j ∧ (ds.getD (t + k) default).i = k ∧ (ds.getD (t + k) default).sp = (ds.getD t default).sp := by
      intro k
      induction k with
      | zero => intro _; exact ⟨rfl, hi, rfl⟩
      | succ k ihk =>
        intro hk
        obtain ⟨h1, h2, h3⟩ := ihk (by omega)
        obtain ⟨e1, e2, e3⟩ := hR.step (t + k) (by omega) (hnl k (by omega))
        rw [show t + (k + 1) = t + k + 1 by omega]
        exact ⟨e1.trans h1, by rw [e2, h2], e3.trans h3⟩
    obtain ⟨hj, hiv, hsp⟩ := hlev m (Nat.le_refl _)
    obtain ⟨hs1, hs2⟩ := hR.lil (t + m) hm hlm
    have hS : (ds.getD (t + m) default).s = ((ds.getD t default).sp + 1) / 2 := by
      rw [hsp] at hs2; split at hs2 <;> omega
    have hmS : m + 1 = ((ds.getD t default).sp + 1) / 2 := by rw [← hS, ← hs1, hiv]
    rw [shapeOf_drop ds t (m + 1) (by omega)]
    simp only [mrkLevels]
    rw [← hmS]
    congr 1
    · apply List.map_congr_left
      intro k hk; rw [List.mem_range] at hk
      obtain ⟨h1, h2, h3⟩ := hlev k (by omega)
      rw [h1, h2, hR.pr (t + k) (by omega)]
      by_cases hkm : k = m
      · subst hkm
        have e : (ds.getD t default).sp + (if (ds.getD (t + k) default).odd = true then 1 else 0) =
            2 * (k + 1) := by rw [← hsp, hs2, ← hs1, hiv]
        rw [hlm]
        cases hodd : (ds.getD (t + k) default).odd
        · rw [hodd, if_neg (by decide)] at e
          show (_, _, !(false && true)) = (_, _, decide (2 * k + 1 < (ds.getD t default).sp))
          rw [decide_eq_true (by omega)]; rfl
        · rw [hodd, if_pos rfl] at e
          show (_, _, !(true && true)) = (_, _, decide (2 * k + 1 < (ds.getD t default).sp))
          rw [decide_eq_false (by omega)]; rfl
      · rw [hnl k (by omega)]
        show (_, _, !(_ && false)) = (_, _, decide (2 * k + 1 < (ds.getD t default).sp))
        rw [Bool.and_false, decide_eq_true (by omega)]; rfl
    · by_cases hs : (m + 1) = 1
      · rw [if_pos hs]
        have htop := (hR.top (t + m) hm hlm).2 (by omega)
        have hlast : t + m + 1 = ds.length := by
          rcases Nat.lt_or_ge (t + m + 1) ds.length with h | h
          · have := (hR.up (t + m) h hlm).1; rw [htop] at this; cases this
          · omega
        rw [show t + (m + 1) = ds.length by omega]; simp [shapeOf]
      · rw [if_neg hs]
        have hnext : t + m + 1 < ds.length := by
          rcases Nat.lt_or_ge (t + m + 1) ds.length with h | h
          · exact h
          · have hl := hR.last (by omega)
            rw [show ds.length - 1 = t + m by omega] at hl
            have := (hR.top (t + m) hm hlm).1 hl.2; omega
        obtain ⟨-, u1, u2, u3⟩ := hR.up (t + m) hnext hlm
        have := ih (t + m + 1) hnext u2 (by rw [u3]; omega)
        rw [show t + (m + 1) = t + m + 1 by omega, this, u1, u3, hj, hS, hmS]

theorem shape (ds : List ND) (hR : Rules ds) (n : Nat) (hne : 0 < ds.length)
    (h0 : (ds.getD 0 default).j = 1 ∧ (ds.getD 0 default).i = 0 ∧ (ds.getD 0 default).sp = n) :
    shapeOf ds = mrkShape n := by
  have := levels_from ds hR (n + 1) 0 hne h0.2.1 (by omega)
  rw [List.drop_zero, h0.1, h0.2.2] at this
  exact this

end ZkFormal.Near.MrkShape
