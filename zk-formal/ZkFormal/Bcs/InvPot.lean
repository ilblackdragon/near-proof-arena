import ZkFormal.Bcs.Statements

/-!
# ZkFormal.Bcs.InvPot — the inversion potential (`InvPotStmt`)

`InvBad` (Bcs/Wide.lean): the fresh answer `y` to one half `x = whq m j` of
`WH(m)`, the other half being already answered (`y'`), completes `WH(m)` to
a digest `mkWide j y y'` that is already *used* (in `slots`) by an earlier
query or by `x` itself.

Per fresh query the number of bad answers is the number of used digests
whose other half is `y'`, which the adversary can make large (learn `y'`,
then use many digests `(guess, y')`).  The potential therefore pays in
advance, when a digest is *used*, for every *pending* half:

* an entry `e = (whq m j', a)` of the log is *pending* while half `1 - j'`
  of `m` is unanswered; its term is the number of used digests (with
  multiplicity) of the form `mkWide (1 - j') _ a` (`itemTerm`, `psi`);
* a use of a digest `u` raises `psi` by the number of pending entries
  matching `u`; with `c = eqPairs` (pairs of log entries with equal
  answers) this is at most `2 (1 + c)` per digest, prepaid by
  `514 · (N - |log|) · c` (`c` grows by `≤ |log|/2^256` in expectation per
  fresh query);
* completing `WH(m)` removes the pending term `T`, and the bad answers are
  at most `T + |slots x| ≤ T + 257` out of `2^256`.

`invPot N` is all of this, scaled (`2^256·[BadHist InvBad] + psi + prepay`)
and frozen after `N` entries as `pairPot`.  Per fresh query it rises by at
most `771 + (514 N + 514 N²)/2^256 ≤ 1024` (scaled), for `N ≤ 2^100`.
-/

namespace ZkFormal.Bcs

open ArenaCore ArenaCore.Security ZkFormal

/-! ## Generic counting -/

theorem count_false {α : Type} (l : List α) : count l (fun _ => False) = 0 := by
  simp [count]

theorem count_eq_sum {α : Type} (l : List α) (P : α → Prop) :
    count l P = (l.map fun a => open Classical in if P a then 1 else 0).sum := by
  rw [sum_map_ite, Nat.mul_one]

/-- Swapping a sum of counts. -/
theorem sum_count_comm {α β : Type} (L : List α) (S : List β) (Q : α → β → Prop) :
    (L.map fun e => count S (Q e)).sum = (S.map fun u => count L (fun e => Q e u)).sum := by
  classical
  simp only [count_eq_sum]
  exact sum_map_sum_comm L S (fun e u => open Classical in if Q e u then 1 else 0)

/-- `∑_{v<R} count A (P v) ≤ |A| · B` if each `u` is hit by at most `B` values. -/
theorem sum_count_le (R : Nat) {β : Type} (A : List β) (P : Nat → β → Prop) (B : Nat)
    (h : ∀ u ∈ A, count (List.range R) (fun v => P v u) ≤ B) :
    ((List.range R).map fun v => count A (P v)).sum ≤ A.length * B := by
  rw [sum_count_comm]
  refine Nat.le_trans (sum_map_le _ _ (fun _ => B) h) ?_
  rw [Security.sum_map_const]; exact Nat.le_refl _

/-- `∑ f + d ≤ ∑ g` if `f ≤ g` pointwise with slack `d` at one member. -/
theorem sum_add_le_of_mem {α : Type} (f g : α → Nat) (d : Nat) (a : α) :
    ∀ (l : List α), a ∈ l → (∀ b ∈ l, f b ≤ g b) → f a + d ≤ g a →
      (l.map f).sum + d ≤ (l.map g).sum
  | [], h, _, _ => by simp at h
  | b :: l, hmem, hle, ha => by
    simp only [List.map_cons, List.sum_cons]
    have hl : (l.map f).sum ≤ (l.map g).sum :=
      sum_map_le _ _ _ fun c hc => hle c (List.mem_cons_of_mem _ hc)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · omega
    · have := sum_add_le_of_mem f g d a l hmem (fun c hc => hle c (List.mem_cons_of_mem _ hc)) ha
      have := hle b List.mem_cons_self
      omega

/-! ## Matching digests -/

/-- `u` is `WH(m)` for some value `a` (32 bytes) of half `j`, the other
half being `y'`. -/
def Match (j : Nat) (y' u : Bytes) : Prop := ∃ a : Bytes, a.length = 32 ∧ u = mkWide j a y'

theorem match_unique {j : Nat} {b₁ b₂ u : Bytes} (h₁ : Match j b₁ u) (h₂ : Match j b₂ u) :
    b₁ = b₂ := by
  obtain ⟨a₁, ha₁, rfl⟩ := h₁
  obtain ⟨a₂, ha₂, e⟩ := h₂
  unfold mkWide at e
  by_cases hj : j = 0
  · simp only [hj, ite_true] at e
    exact (List.append_inj e (by rw [ha₁, ha₂])).2
  · simp only [hj, ite_false] at e
    exact (List.append_inj' e (by rw [ha₁, ha₂])).1

theorem mkWide_inj {j : Nat} {a₁ a₂ y' : Bytes} (h₁ : a₁.length = 32) (h₂ : a₂.length = 32)
    (e : mkWide j a₁ y' = mkWide j a₂ y') : a₁ = a₂ := by
  unfold mkWide at e
  by_cases hj : j = 0
  · simp only [hj, ite_true] at e
    exact (List.append_inj e (by rw [h₁, h₂])).1
  · simp only [hj, ite_false] at e
    exact (List.append_inj' e (by rw [h₁, h₂])).2

/-- At most one oracle answer is the known half of a match with `u`. -/
theorem count_match_answer_le (j : Nat) (u : Bytes) :
    count (List.range roRange) (fun v => Match j (LazyRO.answer v) u) ≤ 1 := by
  by_cases h : ∃ b, Match j b u
  · obtain ⟨b, hb⟩ := h
    exact Nat.le_trans (count_mono _ fun v hv => match_unique hv hb) (answer_count_le_one b)
  · refine Nat.le_trans (count_mono (F := fun _ => False) _ fun v hv => h ⟨_, hv⟩) ?_
    rw [count_false]; exact Nat.zero_le _

/-- At most one oracle answer, as the unknown half, completes to `u`. -/
theorem count_mkWide_le (j : Nat) (y' u : Bytes) :
    count (List.range roRange) (fun v => u = mkWide j (LazyRO.answer v) y') ≤
      (open Classical in if Match j y' u then 1 else 0) := by
  classical
  by_cases h : Match j y' u
  · rw [ite_eq_left h]
    obtain ⟨a, ha, rfl⟩ := h
    refine Nat.le_trans (count_mono _ fun v hv => ?_) (answer_count_le_one a)
    exact (mkWide_inj ha (answer_length v) hv).symm
  · rw [ite_eq_right h]
    refine Nat.le_trans (count_mono (F := fun _ => False) _ fun v hv => h ⟨_, answer_length v, hv⟩) ?_
    rw [count_false]; exact Nat.le_refl _

theorem count_exists_mkWide_le (j : Nat) (y' : Bytes) :
    ∀ S : List Bytes, count (List.range roRange) (fun v => ∃ u ∈ S, u = mkWide j (LazyRO.answer v) y') ≤
      count S (Match j y')
  | [] => by
    refine Nat.le_trans (count_mono (F := fun _ => False) _ fun v ⟨u, hu, _⟩ => by simp at hu) ?_
    rw [count_false]; exact Nat.zero_le _
  | u :: S => by
    have ih := count_exists_mkWide_le j y' S
    have h1 := count_mkWide_le j y' u
    refine Nat.le_trans (count_mono _ (F := fun v => u = mkWide j (LazyRO.answer v) y' ∨
      ∃ u ∈ S, u = mkWide j (LazyRO.answer v) y') fun v ⟨u', hu', e⟩ => ?_) ?_
    · rcases List.mem_cons.mp hu' with rfl | hu'
      · exact Or.inl e
      · exact Or.inr ⟨u', hu', e⟩
    · refine Nat.le_trans (count_or_le _ _ _) ?_
      rw [count_cons]
      omega

/-! ## Equal-answer pairs -/

/-- Pairs of log entries with equal answers. -/
noncomputable def eqPairs : Table → Nat
  | [] => 0
  | e :: L => count L (fun e' => e'.2 = e.2) + eqPairs L

theorem count_val_le (a : Bytes) : ∀ L : Table, count L (fun e => e.2 = a) ≤ 1 + eqPairs L
  | [] => by simp [count]
  | e :: L => by
    classical
    have ih := count_val_le a L
    rw [count_cons]
    simp only [eqPairs]
    by_cases h : e.2 = a
    · subst h; rw [ite_eq_left rfl]; omega
    · rw [ite_eq_right h]; omega

theorem count_match_entries_le (j : Nat) (u : Bytes) (L : Table) :
    count L (fun e => Match j e.2 u) ≤ 1 + eqPairs L := by
  by_cases h : ∃ b, Match j b u
  · obtain ⟨b, hb⟩ := h
    exact Nat.le_trans (count_mono _ fun e he => match_unique he hb) (count_val_le b L)
  · refine Nat.le_trans (count_mono (F := fun _ => False) _ fun e he => h ⟨_, he⟩) ?_
    rw [count_false]; exact Nat.zero_le _

end ZkFormal.Bcs
