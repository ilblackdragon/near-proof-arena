import ZkFormal.Near.Render.Proof.WalkShape

/-!
# ZkFormal.Near.Render.Proof.MrkRecs — the row records of the mrk table

`recs n = (mrkShape n).flatMap expand`: consecutive records are related by
`MAdj` (next row of a segment / next node of the level / first node of the
next level), every record satisfies `RecOk`, the first is node `(1, 0)`, the
last ends the top node (level of size 1).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

abbrev Rec := Nat × Nat × Bool × Nat

namespace MrkGen

def expand (x : Nat × Nat × Bool) : List Rec :=
  if x.2.2 then (List.range 64).map fun p => (x.1, x.2.1, true, p) else [(x.1, x.2.1, false, 0)]

theorem recs_eq (n : Nat) : recs n = (mrkShape n).flatMap expand := by
  simp only [recs]; congr 1

/-- The record ends its node. -/
def EndOf (r : Rec) : Prop := r.2.2.1 = false ∨ r.2.2.2 = 63

def MAdj (n : Nat) (r r' : Rec) : Prop :=
  (r.2.2.1 = true → r.2.2.2 < 63 → r' = (r.1, r.2.1, true, r.2.2.2 + 1)) ∧
  (EndOf r → r.2.1 + 1 < size n r.1 → r' = (r.1, r.2.1 + 1, decide (2 * (r.2.1 + 1) + 1 < size n (r.1 - 1)), 0)) ∧
  (EndOf r → r.2.1 + 1 = size n r.1 → size n r.1 ≠ 1 ∧ r' = (r.1 + 1, 0, decide (1 < size n r.1), 0))

def RecOk (n : Nat) (r : Rec) : Prop :=
  1 ≤ r.1 ∧ r.1 ≤ n + 1 ∧ r.2.1 < size n r.1 ∧ r.2.2.1 = decide (2 * r.2.1 + 1 < size n (r.1 - 1)) ∧
  (r.2.2.1 = true → r.2.2.2 < 64) ∧ (r.2.2.1 = false → r.2.2.2 = 0)

end MrkGen

theorem Adj2.of_get {α : Type} {R : α → α → Prop} : ∀ {l : List α},
    (∀ q (h : q + 1 < l.length), R l[q] l[q + 1]) → Adj2 R l
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: l, h => ⟨h 0 (by simp), Adj2.of_get (l := b :: l) (fun q hq => h (q + 1) (by simp at hq ⊢; omega))⟩

theorem Adj2.flatMap {α β : Type} {R : β → β → Prop} (g : α → List β) : ∀ {l : List α},
    (∀ x ∈ l, Adj2 R (g x)) →
    Adj2 (fun x y => ∀ a b, (g x).getLast? = some a → (g y).head? = some b → R a b) l →
    (∀ x ∈ l, g x ≠ []) → Adj2 R (l.flatMap g)
  | [], _, _, _ => trivial
  | [x], h1, _, _ => by simpa using h1 x (by simp)
  | x :: y :: l, h1, ⟨hxy, h2⟩, h3 => by
    rw [List.flatMap_cons]
    refine Adj2.append (h1 x (by simp)) (Adj2.flatMap g (l := y :: l) (fun z hz => h1 z (by simp [hz])) h2
      (fun z hz => h3 z (by simp [hz]))) ?_
    intro a b ha hb
    apply hxy a b ha
    rw [List.flatMap_cons] at hb
    cases hgy : g y with
    | nil => exact absurd hgy (h3 y (by simp))
    | cons c cs => rw [hgy] at hb; simpa using hb

namespace MrkGen

theorem expand_ne (x : Nat × Nat × Bool) : expand x ≠ [] := by
  unfold expand; split <;> simp

theorem expand_head (x : Nat × Nat × Bool) : (expand x).head? = some (x.1, x.2.1, x.2.2, 0) := by
  unfold expand; split
  · rename_i h; rw [List.range_succ_eq_map]; simp [h]
  · rename_i h; simp at h; simp [h]

theorem expand_last (x : Nat × Nat × Bool) :
    (expand x).getLast? = some (x.1, x.2.1, x.2.2, if x.2.2 then 63 else 0) := by
  unfold expand; split
  · rename_i h; simp [h, List.getLast?_eq_getElem?]
  · rename_i h; simp at h; simp [h]

theorem expand_mem {x : Nat × Nat × Bool} {r : Rec} (h : r ∈ expand x) :
    r.1 = x.1 ∧ r.2.1 = x.2.1 ∧ r.2.2.1 = x.2.2 ∧ (x.2.2 = true → r.2.2.2 < 64) ∧ (x.2.2 = false → r.2.2.2 = 0) := by
  unfold expand at h; split at h
  · rename_i hx; simp at h; obtain ⟨p, hp, rfl⟩ := h; simp [hx, hp]
  · rename_i hx; simp at h; subst h; simp at hx; simp [hx]

theorem expand_adj (n : Nat) (x : Nat × Nat × Bool) : Adj2 (MAdj n) (expand x) := by
  unfold expand; split
  · apply Adj2.of_get
    intro q hq
    simp at hq
    simp only [List.getElem_map, List.getElem_range]
    refine ⟨fun _ _ => rfl, fun h => ?_, fun h => ?_⟩ <;>
    · rcases h with h | h
      · simp at h
      · simp at h; omega
  · trivial

variable (n : Nat)

theorem level_recs : ∀ f j0, 1 ≤ size n j0 → size n j0 ≤ f → j0 + 1 + f ≤ n + 2 →
    Adj2 (MAdj n) ((mrkLevels f (j0 + 1) (size n j0)).flatMap expand) ∧
    (∀ r ∈ (mrkLevels f (j0 + 1) (size n j0)).flatMap expand, RecOk n r) ∧
    ((mrkLevels f (j0 + 1) (size n j0)).flatMap expand).head? =
      some (j0 + 1, 0, decide (1 < size n j0), 0) ∧
    ∃ r, ((mrkLevels f (j0 + 1) (size n j0)).flatMap expand).getLast? = some r ∧
      size n r.1 = 1 ∧ r.2.1 = 0 ∧ EndOf r
  | 0, _, h1, h2, _ => absurd h2 (by omega)
  | f + 1, j0, h1, h2, h3 => by
    have hs : size n (j0 + 1) = (size n j0 + 1) / 2 := rfl
    have hs1 : 1 ≤ size n (j0 + 1) := by omega
    simp only [mrkLevels, ← hs]
    -- the level
    have adjL : Adj2 (MAdj n) (((List.range (size n (j0 + 1))).map fun i =>
        (j0 + 1, i, decide (2 * i + 1 < size n j0))).flatMap expand) := by
      apply Adj2.flatMap expand (fun x _ => expand_adj n x) _ (fun x _ => expand_ne x)
      apply Adj2.of_get
      intro q hq a b ha hb
      simp at hq
      simp only [List.getElem_map, List.getElem_range, expand_last, expand_head] at ha hb
      cases ha; cases hb
      refine ⟨fun h1 h2 => ?_, fun _ _ => rfl, fun _ h => by simp at h; omega⟩
      simp at h1; simp [h1] at h2
    have okL : ∀ r ∈ ((List.range (size n (j0 + 1))).map fun i =>
        (j0 + 1, i, decide (2 * i + 1 < size n j0))).flatMap expand, RecOk n r := by
      intro r hr
      simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hr
      obtain ⟨x, ⟨i, hi, rfl⟩, hx⟩ := hr
      obtain ⟨e1, e2, e3, e4, e5⟩ := expand_mem hx
      exact ⟨by simp [e1], by simp [e1]; omega, by simp [e1, e2]; omega, by simp [e1, e2, e3],
        fun h => e4 (by rw [← e3]; exact h), fun h => e5 (by rw [← e3]; exact h)⟩
    have headL : (((List.range (size n (j0 + 1))).map fun i =>
        (j0 + 1, i, decide (2 * i + 1 < size n j0))).flatMap expand).head? =
        some (j0 + 1, 0, decide (1 < size n j0), 0) := by
      obtain ⟨s', hs'⟩ : ∃ s', size n (j0 + 1) = s' + 1 := ⟨size n (j0 + 1) - 1, by omega⟩
      rw [hs', List.range_succ_eq_map]
      simp [expand_head]
    split
    · rename_i hs1'
      rw [List.append_nil]
      refine ⟨adjL, okL, headL, ?_⟩
      rw [hs1', show (1 : Nat) = 0 + 1 from rfl, List.range_succ]
      simp only [List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, expand_last]
      refine ⟨_, rfl, by simpa using hs1', rfl, ?_⟩
      simp only [EndOf]; by_cases hh : 2 * 0 + 1 < size n j0 <;> simp [hh]
    · rename_i hs1'
      obtain ⟨i1, i2, i3, i4⟩ := level_recs f (j0 + 1) hs1 (by omega) (by omega)
      rw [List.flatMap_append]
      refine ⟨Adj2.append adjL i1 ?_, ?_, ?_, ?_⟩
      · intro a b ha hb
        rw [i3] at hb; cases hb
        obtain ⟨s', hs'⟩ : ∃ s', size n (j0 + 1) = s' + 1 := ⟨size n (j0 + 1) - 1, by omega⟩
        rw [hs', List.range_succ] at ha
        simp only [List.map_append, List.map_cons, List.map_nil, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.getLast?_append, expand_last] at ha
        simp only [Option.some_or] at ha
        cases ha
        refine ⟨fun h1 h2 => ?_, fun _ h => by simp at h; omega, fun _ _ => ⟨by simpa using hs1', by simp⟩⟩
        simp at h1; simp [h1] at h2
      · intro r hr
        rcases List.mem_append.1 hr with hr | hr
        · exact okL r hr
        · exact i2 r hr
      · rw [List.head?_append, headL]; rfl
      · obtain ⟨r, hr1, hr2⟩ := i4
        refine ⟨r, ?_, hr2⟩
        rw [List.getLast?_append, hr1]; rfl

theorem getLast_flatMap_expand : ∀ (l : List (Nat × Nat × Bool)),
    ((l.flatMap expand).getLast?).map (·.1) = (l.getLast?).map (·.1)
  | [] => rfl
  | [x] => by simp [expand_last]
  | x :: y :: l => by
    rw [List.flatMap_cons, List.getLast?_append, List.getLast?_cons_cons]
    have ih := getLast_flatMap_expand (y :: l)
    cases h : ((y :: l).flatMap expand).getLast? with
    | none => simp [List.flatMap_cons, expand_ne] at h
    | some a => rw [h] at ih; simp only [Option.some_or]; exact ih

/-- **The records of `n ≥ 1` leaves.** -/
theorem recs_facts (hn : 1 ≤ n) :
    Adj2 (MAdj n) (recs n) ∧ (∀ r ∈ recs n, RecOk n r) ∧
    (recs n).head? = some (1, 0, decide (1 < n), 0) ∧
    ∃ r, (recs n).getLast? = some r ∧ size n r.1 = 1 ∧ r.2.1 = 0 ∧ EndOf r ∧ r.1 = topJ n := by
  have := level_recs n (n + 1) 0 hn (by simp [size]) (by omega)
  rw [show mrkLevels (n + 1) (0 + 1) (size n 0) = mrkShape n from rfl, ← recs_eq] at this
  obtain ⟨h1, h2, h3, r, hr, hr2⟩ := this
  refine ⟨h1, h2, h3, r, hr, hr2.1, hr2.2.1, hr2.2.2, ?_⟩
  have := getLast_flatMap_expand (mrkShape n)
  rw [← recs_eq, hr] at this
  simp only [topJ, ← this, Option.map_some, Option.getD_some]

theorem size_pos (hn : 1 ≤ n) : ∀ j, 1 ≤ size n j
  | 0 => hn
  | j + 1 => by have := size_pos hn j; simp only [size]; omega

theorem size_le : ∀ j, size n j ≤ n
  | 0 => Nat.le_refl _
  | j + 1 => by have := size_le j; simp only [size]; omega

end MrkGen

end ZkFormal.Near.Render
