import ZkFormal.NearV3.Sched.Link.MemSim
import ZkFormal.NearV3.Sched.Spec.Granted

/-!
# ZkFormal.NearV3.Sched.Link.MemRun — the replay state at every time (stage B step 2)

The simulated memory of instance τ: `stAt t` is the spec state before time `t` — `st` for
`t ≤ T0`, then each entry slot `(i, j)` at time `T_i + j` applies its `tryGrant`
(`entAt t` finds the slot). Its arrays are the replay state `stepSt i j` at `t = T_i + j`
(**`stAt_slot`**), stay `≤ 4,500,000` and keep their sizes.

* `tryGrant_get`: what `tryGrant` writes (only `allowance[l]`, `senderBudget[l / n]`,
  `receiverBudget[l % n]`);
* `slot_unique`, `entAt_slot`, `entAt_some`, `entAt_lt`: entry slots have distinct times
  `T0 ≤ T_i + j`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open NearSpecV3 NearSpecV3.Scheduler

/-! ## `tryGrant` on the arrays -/

/-- The arrays the memory holds. -/
def Arr (S : St) : Array Nat × Array Nat × Array Nat := (S.senderBudget, S.receiverBudget, S.allowance)

section
variable (n : Nat) (allowed : Array Bool)

theorem tryGrant_arr {S S' : St} (h : Arr S = Arr S') (l bw : Nat) :
    Arr (tryGrant n allowed S l bw).2 = Arr (tryGrant n allowed S' l bw).2 := by
  obtain ⟨sb, rb, al, g, rg⟩ := S
  obtain ⟨sb', rb', al', g', rg'⟩ := S'
  simp only [Arr, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  unfold tryGrant grantMore
  split
  · rfl
  · simp only
    split <;> rfl

theorem tryGrant_bnd {B : Nat} {S : St} (h : ABnd B S) (l bw : Nat) :
    ABnd B (tryGrant n allowed S l bw).2 := by
  unfold tryGrant grantMore
  split
  · exact h
  · simp only
    split
    · exact h
    · intro x
      simp only
      rw [getElem!_set!_eq, getElem!_set!_eq, getElem!_set!_eq]
      obtain ⟨h1, h2, h3⟩ := h x
      refine ⟨?_, ?_, ?_⟩ <;> split
      · have := (h (l / n)).1; omega
      · exact h1
      · have := (h (l % n)).2.1; omega
      · exact h2
      · have := (h l).2.2; omega
      · exact h3

/-- Sizes of the arrays. -/
def SzA (n : Nat) (S : St) : Prop :=
  S.senderBudget.size = n ∧ S.receiverBudget.size = n ∧ S.allowance.size = n * n

theorem tryGrant_sz {S : St} (h : SzA n S) (l bw : Nat) : SzA n (tryGrant n allowed S l bw).2 := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold tryGrant grantMore
  split
  · exact ⟨h1, h2, h3⟩
  · simp only
    split
    · exact ⟨h1, h2, h3⟩
    · simp [SzA, Array.set!_eq_setIfInBounds, h1, h2, h3]

/-- **What `tryGrant` writes.** -/
theorem tryGrant_get {S : St} (hS : SzA n S) {l : Nat} (hl : l < n * n) (bw x : Nat) :
    let d := allowed[l]! && decide (bw ≤ S.senderBudget[l / n]!) && decide (bw ≤ S.receiverBudget[l % n]!)
    (tryGrant n allowed S l bw).2.senderBudget[x]! =
        (if d = true ∧ x = l / n then S.senderBudget[x]! - bw else S.senderBudget[x]!) ∧
      (tryGrant n allowed S l bw).2.receiverBudget[x]! =
        (if d = true ∧ x = l % n then S.receiverBudget[x]! - bw else S.receiverBudget[x]!) ∧
      (tryGrant n allowed S l bw).2.allowance[x]! =
        (if d = true ∧ x = l then S.allowance[x]! - bw else S.allowance[x]!) := by
  intro d
  obtain ⟨h1, h2, h3⟩ := hS
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with e | e
    · subst e; simp at hl
    · exact e
  have hs : l / n < n := Nat.div_lt_of_lt_mul hl
  have hr : l % n < n := Nat.mod_lt _ hn
  unfold tryGrant grantMore
  by_cases ha : allowed[l]! = true
  · simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases hb : S.senderBudget[l / n]! < bw ∨ S.receiverBudget[l % n]! < bw
    · rw [if_pos hb]
      have hd : d = false := by
        simp only [d, ha, Bool.true_and, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      simp [hd]
    · rw [if_neg hb]
      have hd : d = true := by
        simp only [d, ha, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega
      simp only [hd, true_and]
      rw [getElem!_set!_eq, getElem!_set!_eq, getElem!_set!_eq]
      refine ⟨?_, ?_, ?_⟩
      · by_cases e : x = l / n
        · subst e; simp [h1, hs]
        · rw [if_neg (fun c => e c.1.symm), if_neg e]
      · by_cases e : x = l % n
        · subst e; simp [h2, hr]
        · rw [if_neg (fun c => e c.1.symm), if_neg e]
      · by_cases e : x = l
        · subst e; simp [h3, hl]
        · rw [if_neg (fun c => e c.1.symm), if_neg e]
  · have hd : d = false := by simp [d, ha]
    simp [ha, hd]

end

/-! ## Entry slots -/

section
variable {tr : Trace Fp} {tp f m : Nat}

/-- The entry slots `(i, j)` of the instance. -/
def entPairs (tr : Trace Fp) (tp f m : Nat) : List (Nat × Nat) :=
  (List.range m).flatMap fun i => (List.range (cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr)).map fun j => (i, j)

/-- The slot processed at time `t`. -/
def entAt (tr : Trace Fp) (tp f m t : Nat) : Option (Nat × Nat) :=
  (entPairs tr tp f m).find? fun p => cv tr tp (Proc.hdrAt tr tp f p.1) Proc.T + p.2 == t

theorem mem_entPairs {p : Nat × Nat} :
    p ∈ entPairs tr tp f m ↔ p.1 < m ∧ p.2 < cv tr tp (Proc.hdrAt tr tp f p.1) Proc.Lr := by
  obtain ⟨i, j⟩ := p
  simp only [entPairs, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi', j', hj', rfl, rfl⟩; exact ⟨hi', hj'⟩
  · rintro ⟨hi, hj⟩; exact ⟨i, hi, j, hj, rfl, rfl⟩

theorem T_ge {pub : List Fp} (hL : Proc.PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22)
    (I : Proc.Inst tr tp f m) {i : Nat} (hi : i < m) : T0 ≤ cv tr tp (Proc.hdrAt tr tp f i) Proc.T := by
  have h0 := (I.first (by omega)).1
  rcases Nat.eq_zero_or_pos i with e | e
  · subst e; omega
  · have := Proc.T_strict hL hH I (i := 0) e hi; omega

theorem T_after (I : Proc.Inst tr tp f m) {i : Nat} :
    ∀ {i'}, i < i' → i' < m →
      cv tr tp (Proc.hdrAt tr tp f i) Proc.T + cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr ≤
        cv tr tp (Proc.hdrAt tr tp f i') Proc.T
  | 0, h, _ => by omega
  | i' + 1, h, hm => by
    have hc := (I.chain i' hm).1
    rcases Nat.lt_or_ge i i' with e | e
    · have := T_after I e (by omega); omega
    · have : i = i' := by omega
      subst this; omega

theorem slot_unique (I : Proc.Inst tr tp f m) {i j i' j' : Nat} (hi : i < m)
    (hj : j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr) (hi' : i' < m)
    (hj' : j' < cv tr tp (Proc.hdrAt tr tp f i') Proc.Lr)
    (he : cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j = cv tr tp (Proc.hdrAt tr tp f i') Proc.T + j') :
    i = i' ∧ j = j' := by
  rcases Nat.lt_trichotomy i i' with e | e | e
  · have := T_after I e hi'; omega
  · subst e; omega
  · have := T_after I e hi; omega

theorem entAt_some {t i j : Nat} (h : entAt tr tp f m t = some (i, j)) :
    i < m ∧ j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr ∧ cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j = t := by
  have hp := List.find?_some h
  have hm := mem_entPairs.1 (List.mem_of_find?_eq_some h)
  simp only [beq_iff_eq] at hp
  exact ⟨hm.1, hm.2, hp⟩

theorem entAt_slot (I : Proc.Inst tr tp f m) {i j : Nat} (hi : i < m)
    (hj : j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr) :
    entAt tr tp f m (cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j) = some (i, j) := by
  cases h : entAt tr tp f m (cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j) with
  | none =>
    have := (List.find?_eq_none.1 h) (i, j) (mem_entPairs.2 ⟨hi, hj⟩)
    simp at this
  | some p =>
    obtain ⟨i', j'⟩ := p
    obtain ⟨hi', hj', he⟩ := entAt_some h
    obtain ⟨rfl, rfl⟩ := slot_unique I hi' hj' hi hj he
    rfl

theorem entAt_lt {pub : List Fp} (hL : Proc.PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22)
    (I : Proc.Inst tr tp f m) {t : Nat} (ht : t < T0) : entAt tr tp f m t = none := by
  cases h : entAt tr tp f m t with
  | none => rfl
  | some p =>
    obtain ⟨i, j⟩ := p
    obtain ⟨hi, -, he⟩ := entAt_some h
    have := T_ge hL hH I hi; omega

end

/-! ## The state at every time -/

section
variable (n : Nat) (allowed : Array Bool) (tr : Trace Fp) (tp f m : Nat) (st : St)

/-- **The spec state before time `t`.** -/
def stAt : Nat → St
  | 0 => st
  | t + 1 => match entAt tr tp f m t with
    | some (i, j) => (tryGrant n allowed (stAt t) (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link)
        (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc)).2
    | none => stAt t

theorem stAt_none {t : Nat} (h : entAt tr tp f m t = none) :
    stAt n allowed tr tp f m st (t + 1) = stAt n allowed tr tp f m st t := by
  simp only [stAt, h]

theorem stAt_some {t i j : Nat} (h : entAt tr tp f m t = some (i, j)) :
    stAt n allowed tr tp f m st (t + 1) =
      (tryGrant n allowed (stAt n allowed tr tp f m st t) (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link)
        (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc)).2 := by
  simp only [stAt, h]

theorem stAt_bnd {B : Nat} (h : ABnd B st) : ∀ t, ABnd B (stAt n allowed tr tp f m st t)
  | 0 => h
  | t + 1 => by
    simp only [stAt]
    split
    · exact tryGrant_bnd n allowed (stAt_bnd h t) _ _
    · exact stAt_bnd h t

theorem stAt_sz (h : SzA n st) : ∀ t, SzA n (stAt n allowed tr tp f m st t)
  | 0 => h
  | t + 1 => by
    simp only [stAt]
    split
    · exact tryGrant_sz n allowed (stAt_sz h t) _ _
    · exact stAt_sz h t

end

theorem stAt_pre {pub : List Fp} {n : Nat} {allowed : Array Bool} {tr : Trace Fp} {tp f m : Nat} {st : St}
    (hL : Proc.PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) (I : Proc.Inst tr tp f m) :
    ∀ t, t ≤ T0 → stAt n allowed tr tp f m st t = st
  | 0, _ => rfl
  | t + 1, h => by
    rw [stAt_none n allowed tr tp f m st (entAt_lt hL hH I (by omega)), stAt_pre hL hH I t (by omega)]

/-! ## The replay states -/

theorem stepE_fst (n : Nat) (allowed : Array Bool) (reqs : List Req) (K z t v : Nat) (S : St)
    {inc l : Nat} {rest : List Nat} (hi : (reqAt reqs v).incs = inc :: rest) (hl : (reqAt reqs v).link = l) :
    (stepE n allowed reqs K z t v S).1 = (tryGrant n allowed S l inc).2 := by
  unfold stepE
  rw [hi]
  simp only [hl]
  split <;> rfl

section
variable (n : Nat) (allowed : Array Bool) (reqs : List Req) (tr : Trace Fp) (tp f : Nat) (st : St)

/-- The state after round `i` is the state after its last entry. -/
theorem specSt_succ (i : Nat) :
    specSt n allowed reqs tr tp f st (i + 1) =
      stepSt n allowed reqs tr tp f st i (cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr) := by
  have := runL_iter n allowed reqs (rOf tr tp f i).key (rOf tr tp f i).z
    (cv tr tp (Proc.hdrAt tr tp f i) Proc.T) (fun j => cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout)
    (stepSt n allowed reqs tr tp f st i) (fun j => rfl) (cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr) 0
  simp only [Nat.add_zero, Nat.zero_add] at this
  rw [← List.range_eq_range'] at this
  show (specRound n allowed reqs tr tp f i (specSt n allowed reqs tr tp f st i)).1 = _
  unfold specRound
  rw [show eoutsOf tr tp f i = (List.range (cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr)).map
    (fun j => cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout) from rfl]
  rw [show ({ specSt n allowed reqs tr tp f st i with
      rng := rngAt (procKey tr tp f) (cv tr tp (Proc.hdrAt tr tp f i) Proc.kend) } : St) =
      stepSt n allowed reqs tr tp f st i 0 from rfl, this]

end

section
variable {pub : List Fp} {n : Nat} {allowed : Array Bool} {reqs : List Req} {tr : Trace Fp} {tp f m : Nat}
  {st : St}

/-- **The replay state at every entry slot.** -/
theorem stAt_slot (hL : Proc.PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) (I : Proc.Inst tr tp f m)
    (hE : ∀ i, i < m → ∀ j, j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr →
      (∃ rest, (reqAt reqs (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout)).incs =
        cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc :: rest) ∧
      (reqAt reqs (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout)).link =
        cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link) :
    ∀ i, i < m → ∀ j, j ≤ cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr →
      Arr (stAt n allowed tr tp f m st (cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j)) =
        Arr (stepSt n allowed reqs tr tp f st i j) := by
  intro i
  induction i with
  | zero =>
    intro hi j
    induction j with
    | zero =>
      intro _
      rw [Nat.add_zero, (I.first hi).1, stAt_pre hL hH I T0 (Nat.le_refl _)]
      rfl
    | succ j ih =>
      intro hj
      obtain ⟨⟨rest, hinc⟩, hlk⟩ := hE 0 hi j (by omega)
      rw [← Nat.add_assoc, stAt_some n allowed tr tp f m st (entAt_slot I hi (by omega))]
      show _ = Arr (stepE n allowed reqs _ _ _ _ _).1
      rw [stepE_fst n allowed reqs _ _ _ _ _ hinc hlk]
      exact tryGrant_arr n allowed (ih (by omega)) _ _
  | succ i ihi =>
    intro hi j
    induction j with
    | zero =>
      intro _
      rw [Nat.add_zero, (I.chain i hi).1, ihi (by omega) _ (Nat.le_refl _)]
      show _ = Arr (specSt n allowed reqs tr tp f st (i + 1))
      rw [specSt_succ]
    | succ j ih =>
      intro hj
      obtain ⟨⟨rest, hinc⟩, hlk⟩ := hE (i + 1) hi j (by omega)
      rw [← Nat.add_assoc, stAt_some n allowed tr tp f m st (entAt_slot I hi (by omega))]
      show _ = Arr (stepE n allowed reqs _ _ _ _ _).1
      rw [stepE_fst n allowed reqs _ _ _ _ _ hinc hlk]
      exact tryGrant_arr n allowed (ih (by omega)) _ _

end

end ZkFormal.NearV3.Sched
