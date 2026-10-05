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

`invPhi N` is all of this, scaled (`2^256·[BadHist InvBad] + psi + prepay`)
and frozen after `N` entries as `pairPot`.  Per fresh query it rises by at
most `771 + (257 (N + 1) + 514 N²)/2^256 ≤ 1024` (scaled), for `N ≤ 2^100`
(`invPhi0_step`, `invPot`).
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

/-! ## Decoding half queries -/

theorem whDec_some {k m : Bytes} {j : Nat} (h : whDec k = some (m, j)) : k = whq m j ∧ j < 2 := by
  match k, h with
  | [b], h =>
    simp only [whDec] at h
    by_cases h1 : b = 1
    · rw [ite_eq_left h1] at h; cases h; subst h1; exact ⟨rfl, by omega⟩
    · rw [ite_eq_right h1] at h
      by_cases h2 : b = 2
      · rw [ite_eq_left h2] at h; cases h; subst h2; exact ⟨rfl, by omega⟩
      · rw [ite_eq_right h2] at h; cases h
  | t :: b :: p, h =>
    simp only [whDec] at h
    by_cases h1 : b = 1
    · rw [ite_eq_left h1] at h; cases h; subst h1; exact ⟨rfl, by omega⟩
    · rw [ite_eq_right h1] at h
      by_cases h2 : b = 2
      · rw [ite_eq_left h2] at h; cases h; subst h2; exact ⟨rfl, by omega⟩
      · rw [ite_eq_right h2] at h; cases h

theorem whDec_of_eq {x m : Bytes} {j : Nat} (hj : j < 2) (h : x = whq m j) :
    whDec x = some (m, j) := h ▸ whDec_whq m j hj

theorem whq_other_ne {m : Bytes} {j : Nat} (hj : j < 2) : whq m (1 - j) ≠ whq m j := by
  intro h; have := (whq_inj (by omega) hj h).2; omega

/-! ## Used digests -/

/-- Digests used by the log (with multiplicity). -/
def uses (T : Table) : List Bytes := T.flatMap fun e => slots e.1

theorem uses_cons (x y : Bytes) (T : Table) : uses ((x, y) :: T) = slots x ++ uses T := by
  simp [uses]

theorem mem_uses {u : Bytes} {T : Table} : u ∈ uses T ↔ ∃ e ∈ T, u ∈ slots e.1 := by
  simp [uses]

theorem uses_length_le : ∀ T : Table, (uses T).length ≤ 257 * T.length
  | [] => by simp [uses]
  | (x, y) :: T => by
    rw [uses_cons, List.length_append, List.length_cons]
    have := uses_length_le T
    have := slots_length_le x
    omega

/-! ## The pending potential -/

/-- Term of a log entry `e = (whq m j, a)`: while half `1 - j` of `m` is
unanswered, the number of used digests (`U`) completing `a` as half `j`. -/
noncomputable def pterm (T : Table) (U : List Bytes) (e : Bytes × Bytes) : Nat :=
  match whDec e.1 with
  | some (m, j) => if T.lookup (whq m (1 - j)) = none then count U (Match (1 - j) e.2) else 0
  | none => 0

noncomputable def psi (T : Table) : Nat := (T.map (pterm T (uses T))).sum

/-- Matches of entry `e` among the digests used by a new query `x`. -/
noncomputable def gx (x : Bytes) (e : Bytes × Bytes) : Nat :=
  count (slots x) (fun u => ∃ m j, whDec e.1 = some (m, j) ∧ Match (1 - j) e.2 u)

theorem psi_cons (x a : Bytes) (T : Table) :
    psi ((x, a) :: T) = pterm ((x, a) :: T) (slots x ++ uses T) (x, a) +
      (T.map (pterm ((x, a) :: T) (slots x ++ uses T))).sum := by
  simp only [psi, uses_cons, List.map_cons, List.sum_cons]

theorem pterm_cons_le (x a : Bytes) (T : Table) (e : Bytes × Bytes) :
    pterm ((x, a) :: T) (slots x ++ uses T) e ≤ pterm T (uses T) e + gx x e := by
  unfold pterm
  cases hd : whDec e.1 with
  | none => simp
  | some p =>
    obtain ⟨m, j⟩ := p
    simp only
    by_cases h1 : ((x, a) :: T).lookup (whq m (1 - j)) = none
    · have h2 : T.lookup (whq m (1 - j)) = none := by
        rw [lookup_cons] at h1
        by_cases hx : whq m (1 - j) = x
        · rw [ite_eq_left hx] at h1; cases h1
        · rwa [ite_eq_right hx] at h1
      rw [ite_eq_left h1, ite_eq_left h2, count_append, Nat.add_comm]
      refine Nat.add_le_add_left (count_mono _ fun u hu => ⟨m, j, hd, hu⟩) _
    · rw [ite_eq_right h1]; exact Nat.zero_le _

theorem gx_sum_le (x : Bytes) (T : Table) : (T.map (gx x)).sum ≤ 514 * (1 + eqPairs T) := by
  unfold gx
  rw [sum_count_comm]
  refine Nat.le_trans (sum_map_le _ _ (fun _ => (1 + eqPairs T) + (1 + eqPairs T)) fun u _ => ?_) ?_
  · refine Nat.le_trans (count_mono _ (F := fun e => Match 0 e.2 u ∨ Match 1 e.2 u)
      fun e ⟨m, j, _, hm⟩ => ?_) (Nat.le_trans (count_or_le _ _ _) (Nat.add_le_add
        (count_match_entries_le 0 u T) (count_match_entries_le 1 u T)))
    rcases (by omega : 1 - j = 0 ∨ 1 - j = 1) with h | h
    · rw [h] at hm; exact Or.inl hm
    · rw [h] at hm; exact Or.inr hm
  · rw [Security.sum_map_const]
    have := slots_length_le x
    have := Nat.mul_le_mul_right ((1 + eqPairs T) + (1 + eqPairs T)) this
    omega

/-! ## One fresh query -/

/-- The pending term of the other half of `x` (removed when `x` is answered). -/
noncomputable def deficit (x : Bytes) (T : Table) : Nat :=
  match whDec x with
  | some (m, j) =>
    match T.lookup (whq m (1 - j)) with
    | some y' => count (uses T) (Match j y')
    | none => 0
  | none => 0

/-- Old entries: new uses are paid by `gx`, and the other half of `x` (if
answered) loses its pending term `deficit x T`. -/
theorem psi_tail_le (x a : Bytes) (T : Table) (hx : T.lookup x = none) :
    (T.map (pterm ((x, a) :: T) (slots x ++ uses T))).sum + deficit x T ≤
      psi T + 514 * (1 + eqPairs T) := by
  have hg := gx_sum_le x T
  have key : (T.map (pterm ((x, a) :: T) (slots x ++ uses T))).sum + deficit x T ≤
      (T.map fun e => pterm T (uses T) e + gx x e).sum := by
    unfold deficit
    cases hd : whDec x with
    | none => simpa using sum_map_le _ _ _ fun e _ => pterm_cons_le x a T e
    | some p =>
      obtain ⟨m, j⟩ := p
      obtain ⟨rfl, hj⟩ := whDec_some hd
      simp only
      cases hl : T.lookup (whq m (1 - j)) with
      | none => simpa using sum_map_le _ _ _ fun e _ => pterm_cons_le (whq m j) a T e
      | some y' =>
        simp only
        refine sum_add_le_of_mem _ _ _ (whq m (1 - j), y') T (lookup_mem_pair hl)
          (fun e _ => pterm_cons_le (whq m j) a T e) ?_
        have hd' : whDec (whq m (1 - j)) = some (m, 1 - j) := whDec_whq m (1 - j) (by omega)
        have e1 : 1 - (1 - j) = j := by omega
        unfold pterm
        simp only [hd', e1]
        simp [hx]
  rw [sum_map_add] at key
  unfold psi
  omega

theorem invBad_count_le (x : Bytes) (T : Table) :
    count (List.range roRange) (fun v => InvBad T x (LazyRO.answer v)) ≤ deficit x T + 257 := by
  unfold deficit
  cases hd : whDec x with
  | none =>
    refine Nat.le_trans (count_mono (F := fun _ => False) _ fun v ⟨m, j, _, _, hj, hxm, _⟩ => ?_)
      (by rw [count_false]; exact Nat.zero_le _)
    rw [whDec_of_eq hj hxm] at hd; cases hd
  | some p =>
    obtain ⟨m, j⟩ := p
    obtain ⟨rfl, hj⟩ := whDec_some hd
    simp only
    cases hl : T.lookup (whq m (1 - j)) with
    | none =>
      refine Nat.le_trans (count_mono (F := fun _ => False) _
        fun v ⟨m', j', y', _, hj', hxm, hl', _⟩ => ?_) (by rw [count_false]; exact Nat.zero_le _)
      obtain ⟨rfl, rfl⟩ := whq_inj hj hj' hxm
      rw [hl] at hl'; cases hl'
    | some y' =>
      simp only
      refine Nat.le_trans (count_mono (F := fun v => ∃ u ∈ slots (whq m j) ++ uses T,
        u = mkWide j (LazyRO.answer v) y') _ fun v ⟨m', j', y'', u, hj', hxm, hl', hu, he⟩ => ?_) ?_
      · obtain ⟨rfl, rfl⟩ := whq_inj hj hj' hxm
        rw [hl] at hl'; cases hl'
        refine ⟨u, ?_, he⟩
        rcases hu with hu | hu
        · exact List.mem_append_left _ hu
        · exact List.mem_append_right _ (mem_uses.mpr hu)
      · refine Nat.le_trans (count_exists_mkWide_le j y' _) ?_
        rw [count_append]
        have := Nat.le_trans (count_le_length (slots (whq m j)) (Match j y')) (slots_length_le (whq m j))
        omega

theorem pterm_of_none {T : Table} {U : List Bytes} {e : Bytes × Bytes} (hd : whDec e.1 = none) :
    pterm T U e = 0 := by
  unfold pterm; rw [hd]

theorem pterm_le_of_some {T : Table} {U : List Bytes} {e : Bytes × Bytes} {m : Bytes} {j : Nat}
    (hd : whDec e.1 = some (m, j)) : pterm T U e ≤ count U (Match (1 - j) e.2) := by
  unfold pterm; rw [hd]
  dsimp only
  by_cases h : T.lookup (whq m (1 - j)) = none
  · rw [ite_eq_left h]; exact Nat.le_refl _
  · rw [ite_eq_right h]; exact Nat.zero_le _

/-- The new entry itself, if pending: in expectation at most the number of
used digests. -/
theorem newterm_sum_le (x : Bytes) (T : Table) :
    ((List.range roRange).map fun v =>
      pterm ((x, LazyRO.answer v) :: T) (slots x ++ uses T) (x, LazyRO.answer v)).sum ≤
      257 * (T.length + 1) := by
  have hU : (slots x ++ uses T).length ≤ 257 * (T.length + 1) := by
    rw [List.length_append]; have := slots_length_le x; have := uses_length_le T; omega
  cases hd : whDec x with
  | none =>
    refine Nat.le_trans (sum_map_le _ _ (fun _ => 0) fun v _ => Nat.le_of_eq (pterm_of_none hd)) ?_
    rw [Security.sum_map_const, Nat.mul_zero]; exact Nat.zero_le _
  | some p =>
    obtain ⟨m, j⟩ := p
    refine Nat.le_trans (sum_map_le _ _
      (fun v => count (slots x ++ uses T) (Match (1 - j) (LazyRO.answer v))) fun v _ =>
        pterm_le_of_some (e := (x, LazyRO.answer v)) hd) ?_
    refine Nat.le_trans (sum_count_le roRange _ (fun v u => Match (1 - j) (LazyRO.answer v) u) 1
      fun u _ => count_match_answer_le (1 - j) u) ?_
    rw [Nat.mul_one]; exact hU

theorem eqPairs_sum_le (x : Bytes) (T : Table) :
    ((List.range roRange).map fun v => eqPairs ((x, LazyRO.answer v) :: T)).sum ≤
      roRange * eqPairs T + T.length := by
  simp only [eqPairs]
  rw [sum_map_add, Security.sum_map_const, List.length_range]
  have := sum_count_le roRange T (fun v e => e.2 = LazyRO.answer v) 1 fun e _ =>
    Nat.le_trans (count_mono _ fun v h => h.symm) (answer_count_le_one e.2)
  omega

theorem badPot_cons_le (x a : Bytes) (T : Table) :
    badPot InvBad ((x, a) :: T) ≤
      badPot InvBad T + (open Classical in if InvBad T x a then roRange else 0) := by
  classical
  unfold badPot
  by_cases hb : BadHist InvBad T
  · rw [ite_eq_left (show BadHist InvBad ((x, a) :: T) from Or.inr hb), ite_eq_left hb]
    exact Nat.le_add_right _ _
  · by_cases h : InvBad T x a
    · rw [ite_eq_left h, ite_eq_right hb]; split <;> omega
    · rw [ite_eq_right (show ¬ BadHist InvBad ((x, a) :: T) from fun h' => h'.elim h hb),
        ite_eq_right h]
      exact Nat.zero_le _

theorem badPot_sum_le (x : Bytes) (T : Table) :
    ((List.range roRange).map fun v => badPot InvBad ((x, LazyRO.answer v) :: T)).sum ≤
      roRange * badPot InvBad T +
        count (List.range roRange) (fun v => InvBad T x (LazyRO.answer v)) * roRange := by
  refine Nat.le_trans (sum_map_le _ _ _ fun v _ => badPot_cons_le x (LazyRO.answer v) T) ?_
  rw [sum_map_add, Security.sum_map_const, List.length_range, sum_map_ite]
  exact Nat.le_refl _

/-- The final arithmetic of the step bound. -/
theorem invPot_arith (R b p c D cnt L N Bsum Psum Esum : Nat) (hR : R = 2 ^ 256) (hN : N ≤ 2 ^ 100)
    (hL : L < N) (h1 : Bsum ≤ R * b + cnt * R) (h2 : cnt ≤ D + 257)
    (h3 : Psum + R * D ≤ R * (p + 514 * (1 + c)) + 257 * (L + 1)) (h4 : Esum ≤ R * c + L) :
    Bsum + Psum + 514 * (N - (L + 1)) * Esum ≤ R * (b + p + 514 * (N - L) * c + 1024) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 + L := ⟨N - (L + 1), by omega⟩
  have e1 : n + 1 + L - (L + 1) = n := by omega
  have e2 : n + 1 + L - L = n + 1 := by omega
  rw [e1, e2]
  have hnL : n * L ≤ 2 ^ 100 * 2 ^ 100 := Nat.mul_le_mul (by omega) (by omega)
  have hR' : R = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    rw [hR]
  have h2' := Nat.mul_le_mul_right R h2
  have h4' := Nat.mul_le_mul_left (514 * n) h4
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_one] at h2' h3 h4' ⊢
  have e3 : (2:Nat) ^ 100 * 2 ^ 100 = 1606938044258990275541962092341162602522202993782792835301376 := rfl
  rw [e3] at hnL
  have e4 : n * (R * c) = R * (n * c) := Nat.mul_left_comm _ _ _
  have e5 : c * R = R * c := Nat.mul_comm _ _
  have e6 : D * R = R * D := Nat.mul_comm _ _
  rw [e4] at h4'
  subst hR'
  omega

/-! ## The potential -/

/-- `2^256·[inversion] + pending terms + prepaid uses`. -/
noncomputable def invPhi0 (N : Nat) (T : Table) : Nat :=
  badPot InvBad T + psi T + 514 * (N - T.length) * eqPairs T

/-- Frozen after `N` entries. -/
noncomputable def invPhi (N : Nat) (T : Table) : Nat := invPhi0 N (oldest N T)

theorem invPhi0_step (N : Nat) (hN : N ≤ 2 ^ 100) (T : Table) (hT : T.length < N) (x : Bytes)
    (hx : T.lookup x = none) :
    ((List.range roRange).map fun v => invPhi0 N ((x, LazyRO.answer v) :: T)).sum ≤
      roRange * (invPhi0 N T + 1024) := by
  unfold invPhi0
  simp only [List.length_cons]
  rw [sum_map_add, sum_map_add, sum_map_mul_left]
  have hb := badPot_sum_le x T
  have hc := invBad_count_le x T
  have he := eqPairs_sum_le x T
  have hp : ((List.range roRange).map fun v => psi ((x, LazyRO.answer v) :: T)).sum +
      roRange * deficit x T ≤ roRange * (psi T + 514 * (1 + eqPairs T)) + 257 * (T.length + 1) := by
    simp only [psi_cons]
    rw [sum_map_add]
    have h1 := newterm_sum_le x T
    have h2 : ((List.range roRange).map fun v =>
        (T.map (pterm ((x, LazyRO.answer v) :: T) (slots x ++ uses T))).sum + deficit x T).sum ≤
        ((List.range roRange).map fun _ => psi T + 514 * (1 + eqPairs T)).sum :=
      sum_map_le _ _ _ fun v _ => psi_tail_le x (LazyRO.answer v) T hx
    rw [sum_map_add, Security.sum_map_const, Security.sum_map_const, List.length_range] at h2
    omega
  exact invPot_arith roRange _ _ _ _ _ T.length N _ _ _ rfl hN hT hb hc hp he

theorem invPhi_step (N : Nat) (hN : N ≤ 2 ^ 100) : StepBound (invPhi N) unitWeight 1024 := by
  intro tbl x hx
  simp only [unitWeight, Nat.mul_one]
  by_cases hge : N ≤ tbl.length
  · -- frozen
    have e : ∀ v, invPhi N ((x, LazyRO.answer v) :: tbl) = invPhi N tbl := by
      intro v; unfold invPhi; rw [oldest_cons_of_ge hge]
    simp only [e, Security.sum_map_const, List.length_range]
    exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  · have hlt : tbl.length < N := by omega
    have e : ∀ v, invPhi N ((x, LazyRO.answer v) :: tbl) = invPhi0 N ((x, LazyRO.answer v) :: tbl) := by
      intro v; unfold invPhi; rw [oldest_cons_of_lt hlt]
    have e0 : invPhi N tbl = invPhi0 N tbl := by unfold invPhi; rw [oldest_of_le (by omega)]
    simp only [e, e0]
    exact invPhi0_step N hN tbl hlt x hx

theorem invPhi_nil (N : Nat) : invPhi N [] = 0 := by
  simp [invPhi, invPhi0, oldest, badPot, BadHist, psi, eqPairs]

theorem invPhi_bad (N : Nat) (tbl : Table) (h : tbl.length ≤ N) (hb : BadHist InvBad tbl) :
    roRange ≤ invPhi N tbl := by
  unfold invPhi invPhi0
  rw [oldest_of_le h]
  have : badPot InvBad tbl = roRange := by unfold badPot; rw [ite_eq_left hb]
  omega

/-- **The inversion potential.** -/
theorem invPot : InvPotStmt := fun N hN =>
  ⟨invPhi N, invPhi_step N hN, invPhi_nil N, fun tbl h hb => invPhi_bad N tbl h hb⟩

end ZkFormal.Bcs
