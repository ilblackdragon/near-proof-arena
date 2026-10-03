import ArenaCore.Security.ROM

/-!
# ArenaCore.Security.ROMLemmas — reusable facts about the lazy random oracle

* counting over tapes: a fixed coordinate hits a set of density `k/R` with
  probability exactly `k/R`; union bound over coordinates;
* the lazy-oracle invariant: every answer ever returned is the encoding of a
  tape symbol at an index below the number of fresh queries so far, and a
  `q`-query adversary consumes at most `q` tape symbols;
* the **preimage-guessing bound**: an adversary making at most `q` random
  oracle queries outputs a point whose oracle value equals a fixed target
  with probability at most `(q+1)/2^256`.

The last theorem is the basic step of Fiat–Shamir soundness arguments
(a cheating prover must "hit" a bad challenge) and witnesses that the ROM
game of `ArenaCore.Security.ROM` is usable, not merely stated.
-/

namespace ArenaCore.Security

/-! ## Counting -/

theorem count_mono_mem {α : Type} (l : List α) {E F : α → Prop} (h : ∀ x ∈ l, E x → F x) :
    count l E ≤ count l F := by
  classical
  unfold count
  apply List.countP_mono_left
  intro x hx hEx
  simp only [decide_eq_true_eq] at hEx ⊢
  exact h x hx hEx

theorem count_cons {α : Type} (a : α) (l : List α) (E : α → Prop) :
    count (a :: l) E = count l E + (open Classical in if E a then 1 else 0) := by
  classical
  unfold count
  rw [List.countP_cons]
  simp

theorem count_append {α : Type} (l₁ l₂ : List α) (E : α → Prop) :
    count (l₁ ++ l₂) E = count l₁ E + count l₂ E := by
  classical
  unfold count
  exact List.countP_append

theorem count_map {α β : Type} (f : α → β) (l : List α) (E : β → Prop) :
    count (l.map f) E = count l (fun a => E (f a)) := by
  classical
  unfold count
  rw [List.countP_map]
  rfl

theorem count_const {α : Type} (l : List α) (P : Prop) :
    count l (fun _ => P) = (open Classical in if P then l.length else 0) := by
  classical
  induction l with
  | nil => simp [count]
  | cons a l ih =>
    rw [count_cons, ih]
    by_cases hP : P <;> simp [hP]

theorem count_or_le {α : Type} (l : List α) (E F : α → Prop) :
    count l (fun x => E x ∨ F x) ≤ count l E + count l F := by
  classical
  induction l with
  | nil => simp [count]
  | cons a l ih =>
    rw [count_cons, count_cons, count_cons]
    by_cases hE : E a <;> by_cases hF : F a <;> simp [hE, hF] <;> omega

theorem count_flatMap_cons (n R : Nat) (E : List Nat → Prop) (l : List Nat) :
    count (l.flatMap fun a => (allTapes n R).map (a :: ·)) E =
      (l.map fun a => count (allTapes n R) (fun t => E (a :: t))).sum := by
  induction l with
  | nil => simp [count]
  | cons a l ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
    rw [count_append, count_map, ih]

/-- Counting tapes through the first symbol. -/
theorem count_allTapes_succ (n R : Nat) (E : List Nat → Prop) :
    count (allTapes (n + 1) R) E =
      ((List.range R).map fun a => count (allTapes n R) (fun t => E (a :: t))).sum :=
  count_flatMap_cons n R E (List.range R)

theorem sum_map_ite {α : Type} (l : List α) (P : α → Prop) (c : Nat) :
    (l.map fun a => (open Classical in if P a then c else 0)).sum = count l P * c := by
  classical
  induction l with
  | nil => simp [count]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, count_cons]
    by_cases hP : P a <;> simp [hP, Nat.add_mul, Nat.add_comm]

theorem sum_map_const {α : Type} (l : List α) (c : Nat) :
    (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.add_mul, Nat.add_comm]

/-- A fixed coordinate of a uniform tape is uniform. -/
theorem count_coord (P : Nat → Prop) (R : Nat) :
    ∀ (n j : Nat), j < n →
      count (allTapes n R) (fun t => P (t.getD j 0)) = count (List.range R) P * R ^ (n - 1)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, _ => by
    rw [count_allTapes_succ]
    simp only [List.getD_cons_zero]
    simp only [count_const, allTapes_length]
    rw [sum_map_ite]
    rfl
  | n + 1, j + 1, h => by
    rw [count_allTapes_succ]
    simp only [List.getD_cons_succ]
    have ih := count_coord P R n j (by omega)
    simp only [ih, sum_map_const, List.length_range]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.pow_succ]
    rw [Nat.mul_comm R, Nat.mul_assoc]

/-- Union bound over the first `m` coordinates. -/
theorem count_exists_lt_le {α : Type} (l : List α) (E : Nat → α → Prop) (B : Nat) :
    ∀ m, (∀ j, j < m → count l (E j) ≤ B) →
      count l (fun x => ∃ j, j < m ∧ E j x) ≤ m * B
  | 0, _ => by
    have : count l (fun x => ∃ j, j < 0 ∧ E j x) ≤ count l (fun _ => False) :=
      count_mono _ fun _ ⟨_, hj, _⟩ => absurd hj (Nat.not_lt_zero _)
    rw [count_const] at this
    simpa using this
  | m + 1, hB => by
    have h1 : count l (fun x => ∃ j, j < m + 1 ∧ E j x) ≤
        count l (fun x => (∃ j, j < m ∧ E j x) ∨ E m x) := by
      apply count_mono
      rintro x ⟨j, hj, hE⟩
      by_cases hjm : j = m
      · exact Or.inr (hjm ▸ hE)
      · exact Or.inl ⟨j, by omega, hE⟩
    have h2 := count_or_le l (fun x => ∃ j, j < m ∧ E j x) (E m)
    have h3 := count_exists_lt_le l E B m (fun j hj => hB j (by omega))
    have h4 := hB m (by omega)
    rw [Nat.succ_mul]
    omega

/-- Probability that some coordinate `j < n` of a uniform tape lands in a set
of size `≤ k`: at most `n·k/R`. -/
theorem tape_hit_bound (n R k : Nat) (P : Nat → Prop) (hk : count (List.range R) P ≤ k) :
    count (allTapes n R) (fun t => ∃ j, j < n ∧ P (t.getD j 0)) * R ≤ n * k * R ^ n := by
  cases n with
  | zero =>
    have := count_exists_lt_le (allTapes 0 R) (fun j t => P (t.getD j 0)) 0 0
      (fun _ h => absurd h (Nat.not_lt_zero _))
    simp only [Nat.zero_mul, Nat.le_zero] at this
    simp only [Nat.zero_mul, Nat.le_zero, Nat.mul_eq_zero]
    exact Or.inl this
  | succ n =>
    have hB : ∀ j, j < n + 1 → count (allTapes (n + 1) R) (fun t => P (t.getD j 0)) ≤ k * R ^ n := by
      intro j hj
      rw [count_coord P R (n + 1) j hj, Nat.add_sub_cancel]
      exact Nat.mul_le_mul_right _ hk
    have := count_exists_lt_le (allTapes (n + 1) R) (fun j t => P (t.getD j 0)) _ (n + 1) hB
    calc count (allTapes (n + 1) R) (fun t => ∃ j, j < n + 1 ∧ P (t.getD j 0)) * R
        ≤ (n + 1) * (k * R ^ n) * R := Nat.mul_le_mul_right _ this
      _ = (n + 1) * k * R ^ (n + 1) := by
        rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]

/-! ## Uniqueness of preimages of the answer encoding -/

theorem count_eq_le_one {l : List Nat} (hl : l.Nodup) (c : Nat) :
    count l (fun v => v = c) ≤ 1 := by
  classical
  induction l with
  | nil => simp [count]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [count_cons]
    by_cases hac : a = c
    · subst hac
      have : count l (fun v => v = a) ≤ count l (fun _ => False) :=
        count_mono_mem l fun v hv hva => hl.1 (hva ▸ hv)
      rw [count_const] at this
      simp at this
      simp [this]
    · simp [hac, ih hl.2]

theorem roRange_eq : roRange = 256 ^ 32 := by decide

/-- At most one tape symbol in `[0, 2^256)` encodes to a given 32-byte value. -/
theorem answer_count_le_one (target : Bytes) :
    count (List.range roRange) (fun v => LazyRO.answer v = target) ≤ 1 := by
  refine Nat.le_trans (count_mono_mem _ (F := fun v => v = Bytes.beToNat target) ?_)
    (count_eq_le_one List.nodup_range _)
  intro v hv hans
  rw [List.mem_range, roRange_eq] at hv
  rw [← hans, LazyRO.answer, Bytes.beToNat_beN, Nat.mod_eq_of_lt hv]

/-! ## The lazy-oracle invariant -/

/-- Signature of a hash-only adversary. -/
abbrev hashSpec : OracleSpec := ⟨Bytes, fun _ => Bytes⟩

def hashImpl : (q : hashSpec.Query) → LazyRO → hashSpec.Resp q × LazyRO :=
  fun x s => LazyRO.query s x

/-- Every query costs one. -/
def unitWeight : hashSpec.Query → Nat := fun _ => 1

/-- After `k` fresh queries on `tape`: the remaining tape is `tape.drop k`,
no overflow, and every recorded answer encodes a tape symbol below `k`. -/
def LazyInv (tape : List Nat) (k : Nat) (s : LazyRO) : Prop :=
  s.tape = tape.drop k ∧ s.overflow = false ∧
  ∀ e ∈ s.table, ∃ j, j < k ∧ e.2 = LazyRO.answer (tape.getD j 0)

theorem lookup_mem {x y : Bytes} : ∀ {l : List (Bytes × Bytes)},
    l.lookup x = some y → ∃ e ∈ l, e.2 = y
  | [], h => by simp [List.lookup] at h
  | (k, v) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · exact ⟨(k, v), List.mem_cons_self, Option.some.inj h⟩
    · obtain ⟨e, he, hy⟩ := lookup_mem h
      exact ⟨e, List.mem_cons_of_mem _ he, hy⟩

theorem LazyInv.init (tape : List Nat) : LazyInv tape 0 (LazyRO.init tape) :=
  ⟨rfl, rfl, by simp [LazyRO.init]⟩

theorem getD_of_lt {tape : List Nat} {k : Nat} (hk : k < tape.length) :
    tape.getD k 0 = tape[k] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem LazyInv.query {tape : List Nat} {k : Nat} {s : LazyRO} (h : LazyInv tape k s)
    (hk : k < tape.length) (x : Bytes) :
    ∃ k', k' ≤ k + 1 ∧ LazyInv tape k' (LazyRO.query s x).2 ∧
      ∃ j, j < k' ∧ (LazyRO.query s x).1 = LazyRO.answer (tape.getD j 0) := by
  obtain ⟨htape, hov, htab⟩ := h
  unfold LazyRO.query
  cases hl : s.table.lookup x with
  | some y =>
    obtain ⟨e, he, rfl⟩ := lookup_mem hl
    obtain ⟨j, hj, hjv⟩ := htab e he
    exact ⟨k, by omega, ⟨htape, hov, htab⟩, j, hj, hjv⟩
  | none =>
    have hd : tape.drop k = tape[k] :: tape.drop (k + 1) := List.drop_eq_getElem_cons hk
    simp only [htape, hd]
    refine ⟨k + 1, Nat.le_refl _, ⟨rfl, hov, ?_⟩, k, Nat.lt_succ_self k, by rw [getD_of_lt hk]⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨k, Nat.lt_succ_self k, by rw [getD_of_lt hk]⟩
    · obtain ⟨j, hj, hv⟩ := htab e he
      exact ⟨j, by omega, hv⟩

/-- A `q`-query computation consumes at most `q` tape symbols and preserves
the invariant (provided the tape is long enough). -/
theorem LazyInv.simulate {α : Type} {tape : List Nat} {A : OracleComp hashSpec α} {q : Nat}
    (hA : OracleComp.QueryBound unitWeight A q) :
    ∀ {k : Nat} {s : LazyRO}, LazyInv tape k s → k + q ≤ tape.length →
      ∃ k', k' ≤ k + q ∧ LazyInv tape k' (OracleComp.simulate hashImpl A s).2 := by
  induction hA with
  | pure a n =>
    intro k s h _
    exact ⟨k, by omega, h⟩
  | query x cont n hw _ ih =>
    intro k s h hlen
    simp only [unitWeight] at hw
    obtain ⟨k1, hk1, h1, -⟩ := h.query (by omega) x
    simp only [OracleComp.simulate]
    obtain ⟨k', hk', h'⟩ := ih (LazyRO.query s x).1 h1 (by simp only [unitWeight]; omega)
    exact ⟨k', by simp only [unitWeight] at hk'; omega, h'⟩

/-! ## Preimage guessing in the ROM -/

/-- The adversary wins if the random oracle maps its output to `target`. -/
noncomputable def guessWins (A : OracleComp hashSpec Bytes) (target : Bytes)
    (tape : List Nat) : Prop :=
  let r := OracleComp.simulate hashImpl A (LazyRO.init tape)
  (LazyRO.query r.2 r.1).1 = target

theorem guessWins_hit {A : OracleComp hashSpec Bytes} {q : Nat}
    (hA : OracleComp.QueryBound unitWeight A q) (target : Bytes) (tape : List Nat)
    (hlen : tape.length = q + 1) (hw : guessWins A target tape) :
    ∃ j, j < q + 1 ∧ LazyRO.answer (tape.getD j 0) = target := by
  obtain ⟨k, hk, hinv⟩ := LazyInv.simulate hA (LazyInv.init tape) (by omega)
  obtain ⟨k', hk', -, j, hj, hans⟩ := hinv.query (by omega)
    (OracleComp.simulate hashImpl A (LazyRO.init tape)).1
  exact ⟨j, by omega, hans ▸ hw⟩

/-- **Preimage-guessing bound.** Any adversary making at most `q` random
oracle queries outputs a point whose oracle value is a fixed `target` with
probability at most `(q+1)/2^256`. -/
theorem rom_guess_bound (A : OracleComp hashSpec Bytes) (q : Nat)
    (hA : OracleComp.QueryBound unitWeight A q) (target : Bytes) :
    PrLE (q + 1) roRange (guessWins A target) (q + 1) roRange := by
  refine ⟨by rw [roRange_eq]; exact Nat.pow_pos (by decide), ?_⟩
  have hmono : count (allTapes (q + 1) roRange) (guessWins A target) ≤
      count (allTapes (q + 1) roRange)
        (fun t => ∃ j, j < q + 1 ∧ LazyRO.answer (t.getD j 0) = target) :=
    count_mono_mem _ fun t ht hw =>
      guessWins_hit hA target t (mem_allTapes_length ht) hw
  have hb := tape_hit_bound (q + 1) roRange 1 (fun v => LazyRO.answer v = target)
    (answer_count_le_one target)
  rw [Nat.mul_one] at hb
  exact Nat.le_trans (Nat.mul_le_mul_right _ hmono) hb

end ArenaCore.Security
