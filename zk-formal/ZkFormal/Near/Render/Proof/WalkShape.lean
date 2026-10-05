import ZkFormal.Near.Render.Proof.WalkOk
import ZkFormal.Near.Spec.CompleteAcct

/-!
# ZkFormal.Near.Render.Proof.WalkShape — shape of the generator's walk rows

Every walk of a `Good` batch is `START :: rest` with `rest` the
`walkFrom` steps over `keySyms`; consecutive rows of the walk table are
related by `StepAdj` (same walk: chained edges, symbol index `+1`; after a
walk's last step: a `START` row), every row satisfies `StepOk`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

/-- `R` holds between consecutive elements. -/
def Adj2 {α : Type} (R : α → α → Prop) : List α → Prop
  | a :: b :: l => R a b ∧ Adj2 R (b :: l)
  | _ => True

theorem Adj2.get {α : Type} {R : α → α → Prop} : ∀ {l : List α}, Adj2 R l →
    ∀ q (h : q + 1 < l.length), R l[q] l[q + 1]
  | a :: b :: l, ⟨h1, h2⟩, 0, _ => h1
  | a :: b :: l, ⟨_, h2⟩, q + 1, h => Adj2.get h2 q (by simp at h ⊢; omega)
  | [], _, q, h => absurd h (by simp)
  | [_], _, q, h => absurd h (by simp)

theorem Adj2.append {α : Type} {R : α → α → Prop} : ∀ {l₁ l₂ : List α}, Adj2 R l₁ → Adj2 R l₂ →
    (∀ a b, l₁.getLast? = some a → l₂.head? = some b → R a b) → Adj2 R (l₁ ++ l₂)
  | [], _, _, h2, _ => h2
  | [a], [], _, _, _ => trivial
  | [a], b :: l, _, h2, hb => ⟨hb a b rfl rfl, h2⟩
  | a :: a' :: l, l₂, ⟨h1, h1'⟩, h2, hb => by
    refine ⟨h1, ?_⟩
    have := Adj2.append (l₁ := a' :: l) h1' h2 (fun x y hx hy => hb x y (by
      rw [List.getLast?_cons_cons]; exact hx) hy)
    simpa using this

theorem Adj2.map {α β : Type} {R : β → β → Prop} (f : α → β) : ∀ {l : List α},
    Adj2 (fun a b => R (f a) (f b)) l → Adj2 R (l.map f)
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: l, ⟨h1, h2⟩ => ⟨h1, Adj2.map f (l := b :: l) h2⟩

/-- Row facts of one step. -/
def StepOk (s : WStep) : Prop :=
  s.edge = [s.edge.getD 0 0, s.edge.getD 1 0, s.sym, s.edge.getD 3 0, s.edge.getD 4 0] ∧
  (s.t = none → s.sym = SYM_START ∧ s.edge.getD 0 0 = 0 ∧ s.edge.getD 1 0 = 0 ∧ s.last = false)

/-- Facts linking consecutive rows. -/
def StepAdj (p p' : Nat × WStep) : Prop :=
  (p.2.last = false → p'.1 = p.1 ∧ p'.2.t = some (p.2.t.getD 0 + (if p.2.t.isNone then 0 else 1)) ∧
    p'.2.edge.getD 0 0 = p.2.edge.getD 3 0 ∧ p'.2.edge.getD 1 0 = p.2.edge.getD 4 0) ∧
  (p.2.last = true → p'.2.t = none)

/-! ## `walkFrom` -/

section
variable {I : Info}

theorem walkFrom_shape : ∀ (syms : List Nat) (st : Nat × Nat) (tt : Nat) (rest : List WStep),
    walkFrom I st syms tt = .ok rest → (∀ x ∈ syms.dropLast, x ≠ SYM_END) →
    rest.length = syms.length ∧ (∀ s ∈ rest, StepOk s ∧ s.t.isSome) ∧
    (∀ s, rest.head? = some s → s.t = some tt ∧ s.edge.getD 0 0 = st.1 ∧ s.edge.getD 1 0 = st.2) ∧
    (∀ s, rest.getLast? = some s → s.last = decide (syms.getLast? = some SYM_END)) ∧
    (∀ r, Adj2 (fun a b => StepAdj (r, a) (r, b)) rest) ∧
    (∀ j (h : j < rest.length), rest[j].t = some (tt + j) ∧ rest[j].sym = syms.getD j 0 ∧
      rest[j].last = decide (syms.getD j 0 = SYM_END))
  | [], st, tt, rest, h, _ => by
    simp only [walkFrom] at h; cases h; simp [Adj2]
  | sym :: syms, st, tt, rest, h, hend => by
    simp only [walkFrom, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i st' hst
      split at h
      · cases h
      · rename_i rest' hrest
        cases h
        have hend' : ∀ x ∈ syms.dropLast, x ≠ SYM_END := fun x hx => hend x (by
          cases syms with
          | nil => simp at hx
          | cons y ys => simp only [List.dropLast_cons₂, List.mem_cons] at hx ⊢; exact Or.inr hx)
        obtain ⟨l1, l2, l3, l4, l5, l6⟩ := walkFrom_shape syms st' (tt + 1) rest' hrest hend'
        refine ⟨by simp [l1], ?_, ?_, ?_, ?_, ?_⟩
        · intro s hs
          rcases List.mem_cons.1 hs with rfl | hs
          · exact ⟨⟨rfl, by simp⟩, rfl⟩
          · exact l2 s hs
        · intro s hs; cases hs; simp
        · intro s hs
          cases rest' with
          | nil =>
            cases syms with
            | nil => simp at hs; subst hs; simp
            | cons y ys => simp at l1
          | cons r0 rr =>
            rw [List.getLast?_cons_cons] at hs
            have := l4 s hs
            cases syms with
            | nil => simp at l1
            | cons y ys => rw [this]; simp
        · cases rest' with
          | nil => intro _; trivial
          | cons r0 rr =>
            intro r
            refine ⟨?_, l5 r⟩
            obtain ⟨g1, g2, g3⟩ := l3 r0 rfl
            refine ⟨fun _ => ⟨rfl, by simp [g1], g2, g3⟩, fun hl => ?_⟩
            exfalso
            cases syms with
            | nil => simp at l1
            | cons y ys =>
              have : sym ≠ SYM_END := hend sym (by simp)
              simp [this] at hl
        · intro j hj
          cases j with
          | zero => simp
          | succ j =>
            obtain ⟨g1, g2, g3⟩ := l6 j (by simpa using hj)
            simp only [List.getElem_cons_succ, List.getD_cons_succ]
            refine ⟨by rw [g1]; congr 1; omega, g2, g3⟩

end

/-- A walk of the honest table. -/
structure WalkGood (w : List WStep) : Prop where
  ne : w ≠ []
  ok : ∀ s ∈ w, StepOk s
  head : ∀ s, w.head? = some s → s.t = none
  last : ∀ s, w.getLast? = some s → s.last = true
  adj : ∀ r, Adj2 (fun a b => StepAdj (r, a) (r, b)) w

theorem stepsFrom_good : ∀ (ws : List (List WStep)) (r : Nat), (∀ w ∈ ws, WalkGood w) →
    Adj2 StepAdj (stepsFrom ws r) ∧ (∀ p ∈ stepsFrom ws r, StepOk p.2) ∧
    (∀ p, (stepsFrom ws r).head? = some p → p.2.t = none) ∧
    (∀ p, (stepsFrom ws r).getLast? = some p → p.2.last = true)
  | [], _, _ => ⟨trivial, by simp [stepsFrom], by simp [stepsFrom], by simp [stepsFrom]⟩
  | w :: ws, r, h => by
    have hw := h w (by simp)
    obtain ⟨i1, i2, i3, i4⟩ := stepsFrom_good ws (r + 1) (fun w' hw' => h w' (by simp [hw']))
    simp only [stepsFrom]
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine Adj2.append (Adj2.map _ (hw.adj r)) i1 ?_
      intro a b ha hb
      have hl : a.2.last = true := by
        rw [List.getLast?_map] at ha
        cases h' : w.getLast? with
        | none => rw [h'] at ha; cases ha
        | some s => rw [h'] at ha; cases ha; exact hw.last s h'
      exact ⟨(fun h0 => by rw [hl] at h0; cases h0), fun _ => i3 b hb⟩
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hp; exact hw.ok s hs
      · exact i2 p hp
    · intro p hp
      cases w with
      | nil => exact absurd rfl hw.ne
      | cons s w' => simp at hp; subst hp; exact hw.head s rfl
    · intro p hp
      cases h' : stepsFrom ws (r + 1) with
      | nil =>
        rw [h', List.append_nil, List.getLast?_map] at hp
        cases h'' : w.getLast? with
        | none => rw [h''] at hp; cases hp
        | some s => rw [h''] at hp; cases hp; exact hw.last s h''
      | cons q qs =>
        rw [h', List.getLast?_append] at hp
        have : (q :: qs).getLast? = some ((q :: qs).getLast (by simp)) := List.getLast?_eq_getLast _
        rw [this] at hp; simp only [Option.some_or] at hp; cases hp
        exact i4 _ (by rw [h']; exact this)

theorem stepsFrom_length : ∀ (ws : List (List WStep)) (r : Nat), (stepsFrom ws r).length = (ws.map List.length).sum
  | [], _ => rfl
  | w :: ws, r => by simp [stepsFrom, stepsFrom_length ws (r + 1)]

/-! ## The walks of a `Good` batch -/

section
variable {c : Claim} {e : Ext} (hg : Good c e)
include hg

theorem keySyms_facts (rc : Receipt) :
    (∀ x ∈ (keySyms rc).dropLast, x ≠ SYM_END) ∧ (keySyms rc).getLast? = some SYM_END := by
  refine ⟨fun x hx => ?_, by simp [keySyms]⟩
  simp only [keySyms, List.dropLast_concat] at hx
  have := nibbles_lt _ x hx
  simp [SYM_END]; omega

theorem walk_of_index {r : Nat} (hr : r < e.rs.length) : ∃ rest,
    (walksOf (mkInfo c e)).getD r [] = ⟨none, SYM_START, [0, 0, SYM_START, R e.ns 0, 0], false⟩ :: rest ∧
    walkFrom (mkInfo c e) (R e.ns 0, 0) (keySyms (e.rc r)) 0 = .ok rest ∧
    (rest.getLast?.map fun st => st.edge.getD 3 0) = some (e.slot r) := by
  obtain ⟨rest, h1, h2, h3⟩ := walkOf_ok hg hr
  refine ⟨rest, ?_, h2, h3⟩
  have : e.rc r = e.rs[r] := by simp [Ext.rc, List.getD_eq_getElem?_getD, hr]
  simp only [walksOf, mkInfo_e, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hr,
    Option.map_some, Option.getD_some]
  rw [← this, h1]

theorem walkGood_of {r : Nat} (hr : r < e.rs.length) : WalkGood ((walksOf (mkInfo c e)).getD r []) := by
  obtain ⟨rest, h1, h2, _⟩ := walk_of_index hg hr
  rw [h1]
  obtain ⟨kd, kl⟩ := keySyms_facts hg (e.rc r)
  obtain ⟨l1, l2, l3, l4, l5, _⟩ := walkFrom_shape _ _ _ _ h2 kd
  have hne : rest ≠ [] := by
    intro h; rw [h] at l1; simp [keySyms] at l1
  refine ⟨by simp, ?_, by simp, ?_, ?_⟩
  · intro s hs
    rcases List.mem_cons.1 hs with rfl | hs
    · exact ⟨rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
    · exact (l2 s hs).1
  · intro s hs
    rw [List.getLast?_cons] at hs
    cases h : rest.getLast? with
    | none => simp [List.getLast?_eq_none_iff] at h; exact absurd h hne
    | some s' => rw [h] at hs; simp at hs; subst hs; rw [l4 _ h, kl]; rfl
  · intro r'
    cases h : rest with
    | nil => exact absurd h hne
    | cons s0 rs =>
      refine ⟨?_, by rw [← h]; exact l5 r'⟩
      obtain ⟨g1, g2, g3⟩ := l3 s0 (by rw [h]; rfl)
      exact ⟨fun _ => ⟨rfl, by simp [g1], g2, g3⟩, fun h' => by cases h'⟩

theorem walksOf_len : (walksOf (mkInfo c e)).length = e.rs.length := by simp [walksOf, mkInfo_e]

theorem walks_good : ∀ w ∈ walksOf (mkInfo c e), WalkGood w := by
  intro w hw
  obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hw
  have hr' : r < e.rs.length := by rw [← walksOf_len hg]; exact hr
  have := walkGood_of hg hr'
  simpa [List.getD_eq_getElem?_getD, hr] using this

theorem walk_len_le : ∀ w ∈ walksOf (mkInfo c e), w.length ≤ 132 := by
  intro w hw
  obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hw
  have hr' : r < e.rs.length := by rw [← walksOf_len hg]; exact hr
  obtain ⟨rest, h1, h2, _⟩ := walk_of_index hg hr'
  obtain ⟨kd, _⟩ := keySyms_facts hg (e.rc r)
  obtain ⟨l1, _⟩ := walkFrom_shape _ _ _ _ h2 kd
  have h1' := h1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some] at h1'
  rw [h1', List.length_cons, l1]
  have hin : (e.rc r).inSlice = true := by
    have : e.rc r ∈ e.rs := by simp [Ext.rc, List.getD_eq_getElem?_getD, hr']
    exact List.all_eq_true.1 hg.inSlice _ this
  have := Prune.inSlice_receiver_length hin
  simp [keySyms, accountKeyPath, Prune.nibbles_length]; omega

end

end ZkFormal.Near.Render
