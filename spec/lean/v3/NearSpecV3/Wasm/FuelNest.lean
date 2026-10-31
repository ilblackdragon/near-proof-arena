import Lean.Elab.Tactic
import NearSpecV3.Wasm.FuelDefs
/-!
# Fuel sufficiency (W02): block nesting of prepared bodies

Structural facts about prepared function bodies, against the interface of `Wasm/FuelDefs.lean`.

* `nestOK_of_wellNested`: on a well-nested body, `openAt` (the `open_` stack of `matchBlocks`) is
  a nesting in the sense of `NestOK`, and `matchBlocks`' `endOf`/`elseOf` agree with it.
* `freeCount_le_of_wellNested`: `#free ≤ 2 · #openers + 1` (`#end = #openers + 1`, `#else ≤ #if`).
* `validateBody_wellNested`: `validateBody`'s control stack tracks `nestScan`'s stack, so an
  accepted body is well nested.
* `prepare_funcs`: every function `prepare` outputs is well nested, carries `matchBlocks`' tables
  and `gasTable`, and has at most `max_blocks_per_function` openers. The early pass keeps the
  invariant "every function in the module under construction passed `validateBody`" (only the code
  section writes `m.funcs`).

`Lean.Elab.Tactic` is imported only for the `gen_forIn` proof helper (abstracts a `forIn` term).
-/
namespace NearSpecV3.Wasm
namespace FuelNest

/-! ## Pairwise relation on two stacks -/

/-- Two stacks of equal length whose entries are related pointwise. -/
def Pair2 (P : Bool → Nat → Prop) : List Bool → List Nat → Prop
  | [], [] => True
  | b :: bs, o :: os => P b o ∧ Pair2 P bs os
  | _, _ => False

theorem Pair2.length {P} : ∀ {bs : List Bool} {os : List Nat}, Pair2 P bs os → bs.length = os.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [Pair2.length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem Pair2.cons {P : Bool → Nat → Prop} {b : Bool} {o : Nat} {bs : List Bool} {os : List Nat}
    (h : P b o) (t : Pair2 P bs os) : Pair2 P (b :: bs) (o :: os) := ⟨h, t⟩

theorem Pair2.imp {P Q : Bool → Nat → Prop} (hPQ : ∀ b o, P b o → Q b o) :
    ∀ {bs : List Bool} {os : List Nat}, Pair2 P bs os → Pair2 Q bs os
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨hPQ _ _ h.1, Pair2.imp hPQ h.2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem Pair2.imp_mem {P Q : Bool → Nat → Prop} :
    ∀ {bs : List Bool} {os : List Nat}, (∀ b o, o ∈ os → P b o → Q b o) →
      Pair2 P bs os → Pair2 Q bs os
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, hPQ, h =>
    ⟨hPQ _ _ (List.mem_cons_self ..) h.1,
      Pair2.imp_mem (fun b o ho => hPQ b o (List.mem_cons_of_mem _ ho)) h.2⟩
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

/-! ## The opener stack -/

theorem openAt_zero (code : Array Instr) : openAt code 0 = [] := rfl

theorem openAt_succ (code : Array Instr) (pc : Nat) :
    openAt code (pc + 1) = match code[pc]? with
      | some i => openStep (openAt code pc) pc i
      | none => openAt code pc := by
  unfold openAt
  rw [List.range_succ, List.foldl_append]
  rfl

theorem openAt_succ_some {code : Array Instr} {pc : Nat} {i : Instr} (h : code[pc]? = some i) :
    openAt code (pc + 1) = openStep (openAt code pc) pc i := by
  rw [openAt_succ, h]

theorem openAt_succ_none {code : Array Instr} {pc : Nat} (h : code[pc]? = none) :
    openAt code (pc + 1) = openAt code pc := by
  rw [openAt_succ, h]

theorem openStep_opener {os : List Nat} {pc : Nat} {i : Instr} (h : isOpener i = true) :
    openStep os pc i = pc :: os := by
  cases i <;> simp_all [isOpener, openStep]

theorem openStep_other {os : List Nat} {pc : Nat} {i : Instr} (h : isOpener i = false)
    (he : i ≠ .else_) (hn : i ≠ .end_) : openStep os pc i = os := by
  cases i <;> simp_all [isOpener, openStep]

theorem openAt_lt (code : Array Instr) : ∀ (p o : Nat), o ∈ openAt code p → o < p := by
  intro p
  induction p with
  | zero => simp [openAt_zero]
  | succ q ih =>
    intro o ho
    rw [openAt_succ] at ho
    split at ho
    · rename_i i _
      by_cases hop : isOpener i = true
      · rw [openStep_opener hop] at ho
        rcases List.mem_cons.1 ho with rfl | ho
        · omega
        · exact Nat.lt_succ_of_lt (ih o ho)
      · by_cases he : i = .else_
        · subst he; exact Nat.lt_succ_of_lt (ih o ho)
        by_cases hn : i = .end_
        · subst hn
          exact Nat.lt_succ_of_lt (ih o (List.mem_of_mem_tail ho))
        · rw [openStep_other (by simpa using hop) he hn] at ho
          exact Nat.lt_succ_of_lt (ih o ho)
    · exact Nat.lt_succ_of_lt (ih o ho)

theorem openAt_not_mem_self (code : Array Instr) (o : Nat) : o ∉ openAt code o :=
  fun h => Nat.lt_irrefl _ (openAt_lt code o o h)

/-- The chain property of the opener stack (no well-nestedness needed). -/
theorem openAt_chain (code : Array Instr) : ∀ (p o : Nat) (rest : List Nat),
    openAt code p = o :: rest →
    o < p ∧ openAt code o = rest ∧ (code[o]?.map isOpener) = some true := by
  intro p
  induction p using Nat.strongRecOn with
  | _ p ih =>
  intro o rest h
  cases p with
  | zero => simp [openAt_zero] at h
  | succ q =>
    rw [openAt_succ] at h
    split at h
    · rename_i i hi
      by_cases hop : isOpener i = true
      · rw [openStep_opener hop] at h
        cases h
        exact ⟨Nat.lt_succ_self _, rfl, by simp [hi, hop]⟩
      · by_cases he : i = .else_
        · subst he
          obtain ⟨h1, h2, h3⟩ := ih q (Nat.lt_succ_self _) o rest h
          exact ⟨Nat.lt_succ_of_lt h1, h2, h3⟩
        by_cases hn : i = .end_
        · subst hn
          simp only [openStep] at h
          cases hq : openAt code q with
          | nil => rw [hq] at h; simp at h
          | cons x xs =>
            rw [hq] at h
            simp only [List.tail_cons] at h
            subst h
            obtain ⟨hx1, hx2, _⟩ := ih q (Nat.lt_succ_self _) x _ hq
            obtain ⟨h1, h2, h3⟩ := ih x (by omega) o rest hx2
            exact ⟨by omega, h2, h3⟩
        · rw [openStep_other (by simpa using hop) he hn] at h
          obtain ⟨h1, h2, h3⟩ := ih q (Nat.lt_succ_self _) o rest h
          exact ⟨Nat.lt_succ_of_lt h1, h2, h3⟩
    · obtain ⟨h1, h2, h3⟩ := ih q (Nat.lt_succ_self _) o rest h
      exact ⟨Nat.lt_succ_of_lt h1, h2, h3⟩

/-- Once popped, an opener never re-enters the stack. -/
theorem openAt_not_mem_mono (code : Array Instr) (o p : Nat) (hop : o < p)
    (hn : o ∉ openAt code p) : ∀ q, p ≤ q → o ∉ openAt code q := by
  intro q hq
  induction q with
  | zero => omega
  | succ q ih =>
    rcases Nat.eq_or_lt_of_le hq with rfl | hlt
    · exact hn
    have ih := ih (by omega)
    intro hm
    rw [openAt_succ] at hm
    split at hm
    · rename_i i _
      by_cases hopn : isOpener i = true
      · rw [openStep_opener hopn] at hm
        rcases List.mem_cons.1 hm with rfl | hm
        · omega
        · exact ih hm
      · by_cases he : i = .else_
        · subst he; exact ih hm
        by_cases hnd : i = .end_
        · subst hnd; exact ih (List.mem_of_mem_tail hm)
        · rw [openStep_other (by simpa using hopn) he hnd] at hm; exact ih hm
    · exact ih hm

/-! ## The scan stack -/

/-- One step of `nestScan`'s stack (total: a failing step is never taken on a well-nested body). -/
def bStep (st : List Bool) : Instr → List Bool
  | .block _ | .loop _ => false :: st
  | .if_ _ => true :: st
  | .else_ => match st with
    | _ :: st' => false :: st'
    | [] => []
  | .end_ => st.tail
  | _ => st

def bAt (code : Array Instr) (pc : Nat) : List Bool :=
  (code.toList.take pc).foldl bStep []

theorem bAt_succ (code : Array Instr) (pc : Nat) :
    bAt code (pc + 1) = match code[pc]? with
      | some i => bStep (bAt code pc) i
      | none => bAt code pc := by
  simp only [bAt, List.take_add_one, List.foldl_append, Array.getElem?_toList]
  cases code[pc]? <;> rfl

theorem bStep_other {st : List Bool} {i : Instr} (h : isOpener i = false)
    (he : i ≠ .else_) (hn : i ≠ .end_) : bStep st i = st := by
  cases i <;> simp_all [isOpener, bStep]

/-- What `nestScan` succeeding says about every position. -/
def ScanProps (l : List Instr) (st : List Bool) : Prop :=
  (∀ k (hk : k < l.length), l[k] = .else_ → ∃ s, (l.take k).foldl bStep st = true :: s) ∧
  (∀ k (hk : k < l.length), l[k] = .end_ → (l.take k).foldl bStep st = [] → k + 1 = l.length) ∧
  l.foldl bStep st = []

theorem scanProps_lift {i : Instr} {rest : List Instr} {st : List Bool}
    (h0 : i = .else_ → ∃ s, st = true :: s) (h1 : i = .end_ → st = [] → rest = [])
    (P : ScanProps rest (bStep st i)) : ScanProps (i :: rest) st := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk hel
    cases k with
    | zero => simpa using h0 (by simpa using hel)
    | succ k =>
      simp only [List.take_succ_cons, List.foldl_cons]
      exact P.1 k (by simpa using hk) (by simpa using hel)
  · intro k hk hen hnil
    cases k with
    | zero =>
      simp only [List.take_zero, List.foldl_nil] at hnil
      simp [h1 (by simpa using hen) hnil]
    | succ k =>
      simp only [List.take_succ_cons, List.foldl_cons] at hnil
      simpa using P.2.1 k (by simpa using hk) (by simpa using hen) hnil
  · simpa only [List.foldl_cons] using P.2.2

theorem nestScan_cons_other {i : Instr} {rest : List Instr} {st : List Bool}
    (he : i ≠ .else_) (hn : i ≠ .end_) : nestScan (i :: rest) st = nestScan rest (bStep st i) := by
  cases i <;> simp_all [nestScan, bStep]

theorem nestScan_props : ∀ (l : List Instr) (st : List Bool), nestScan l st = true → ScanProps l st
  | [], _, h => by simp [nestScan] at h
  | i :: rest, st, h => by
    by_cases he : i = .else_
    · subst he
      match st, h with
      | true :: st', h =>
        exact scanProps_lift (fun _ => ⟨st', rfl⟩) (by simp)
          (nestScan_props rest _ (by simpa [nestScan, bStep] using h))
      | false :: _, h => simp [nestScan] at h
      | [], h => simp [nestScan] at h
    by_cases hn : i = .end_
    · subst hn
      match st, h with
      | [], h =>
        have hr : rest = [] := by simpa [nestScan] using h
        subst hr
        refine ⟨?_, ?_, ?_⟩
        · intro k hk hel; simp at hk; subst hk; simp at hel
        · intro k hk _ _; simp at hk; subst hk; rfl
        · rfl
      | b :: st', h =>
        exact scanProps_lift (by simp) (by simp)
          (nestScan_props rest _ (by simpa [nestScan, bStep] using h))
    · rw [nestScan_cons_other he hn] at h
      exact scanProps_lift (by simp [he]) (by simp [hn]) (nestScan_props rest _ h)

theorem wellNested_else {code : Array Instr} (h : WellNested code) {pc : Nat}
    (hpc : code[pc]? = some .else_) : ∃ s, bAt code pc = true :: s := by
  obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.1 hpc
  exact (nestScan_props _ _ h).1 pc (by simpa using hlt) (by simpa using heq)

theorem wellNested_end {code : Array Instr} (h : WellNested code) {pc : Nat}
    (hpc : code[pc]? = some .end_) (hnil : bAt code pc = []) : pc + 1 = code.size := by
  obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.1 hpc
  simpa using (nestScan_props _ _ h).2.1 pc (by simpa using hlt) (by simpa using heq) hnil

theorem wellNested_final {code : Array Instr} (h : WellNested code) : bAt code code.size = [] := by
  have := (nestScan_props _ _ h).2.2
  unfold bAt
  rw [← Array.length_toList, List.take_length]
  exact this


theorem bAt_succ_some {code : Array Instr} {pc : Nat} {i : Instr} (h : code[pc]? = some i) :
    bAt code (pc + 1) = bStep (bAt code pc) i := by
  rw [bAt_succ, h]

theorem bAt_succ_none {code : Array Instr} {pc : Nat} (h : code[pc]? = none) :
    bAt code (pc + 1) = bAt code pc := by
  rw [bAt_succ, h]

/-! ## `matchBlocks` as a fold -/

abbrev MB := Array Nat × Array Nat × List Nat

/-- One iteration of `matchBlocks`' loop, on `(endOf, elseOf, open_)`. -/
def mbStep (code : Array Instr) (s : MB) (i : Nat) : MB :=
  match code[i]? with
  | some (.block _) | some (.loop _) | some (.if_ _) => (s.1, s.2.1, i :: s.2.2)
  | some .else_ => match s.2.2 with
    | o :: _ => (s.1, s.2.1.set! o i, s.2.2)
    | [] => (s.1, s.2.1, s.2.2)
  | some .end_ => match s.2.2 with
    | o :: rest =>
      if s.2.1[o]? = some 0 then (s.1.set! o i, s.2.1.set! o i, rest)
      else (s.1.set! o i, s.2.1, rest)
    | [] => (s.1, s.2.1, s.2.2)
  | _ => (s.1, s.2.1, s.2.2)

def mbInit (code : Array Instr) : MB :=
  (Array.replicate code.size 0, Array.replicate code.size 0, [])

/-- The state of `matchBlocks` after `k` iterations. -/
def mbFold (code : Array Instr) (k : Nat) : MB := (List.range k).foldl (mbStep code) (mbInit code)

theorem forIn'_yield_foldl {β : Type} : ∀ (l : List Nat) (f : (a : Nat) → a ∈ l → β → Id (ForInStep β))
    (g : β → Nat → β) (_hf : ∀ a h b, f a h b = pure (.yield (g b a))) (init : β),
    forIn' l init f = pure (l.foldl g init)
  | [], _, _, _, _ => rfl
  | x :: xs, f, g, hf, init => by
    rw [List.forIn'_cons, hf]
    simp only [pure_bind, List.foldl_cons]
    exact forIn'_yield_foldl xs _ g (fun a h b => hf a _ b) _

theorem matchBlocks_eq (code : Array Instr) :
    matchBlocks code = ((mbFold code code.size).1, (mbFold code code.size).2.1) := by
  unfold matchBlocks
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  rw [forIn'_yield_foldl _ _ (mbStep code)]
  · simp [mbFold, mbInit, List.range_eq_range']
  · intro a h b
    have ha : a < code.size := by
      simp [List.mem_range'] at h; omega
    simp only [mbStep, Array.getElem?_eq_getElem ha]
    cases hc : code[a] <;> simp only [] <;> (try rfl) <;>
      (rcases b with ⟨E, L, S⟩; cases S <;> (try rfl) <;>
        (rename_i o rest; dsimp only; by_cases hz : L[o]? = some 0 <;> simp [hz]))

theorem mbFold_succ (code : Array Instr) (k : Nat) :
    mbFold code (k + 1) = mbStep code (mbFold code k) k := by
  simp only [mbFold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

section steps
variable {code : Array Instr} {k : Nat} {E L : Array Nat} {S : List Nat}

theorem mbStep_none (hc : code[k]? = none) : mbStep code (E, L, S) k = (E, L, S) := by
  simp [mbStep, hc]

theorem mbStep_opener {i : Instr} (hc : code[k]? = some i) (hop : isOpener i = true) :
    mbStep code (E, L, S) k = (E, L, k :: S) := by
  cases i <;> simp_all [mbStep, isOpener]

theorem mbStep_other {i : Instr} (hc : code[k]? = some i) (hop : isOpener i = false)
    (he : i ≠ .else_) (hn : i ≠ .end_) : mbStep code (E, L, S) k = (E, L, S) := by
  cases i <;> simp_all [mbStep, isOpener]

theorem mbStep_else {o : Nat} {r : List Nat} (hc : code[k]? = some .else_) :
    mbStep code (E, L, o :: r) k = (E, L.set! o k, o :: r) := by
  simp [mbStep, hc]

theorem mbStep_end {o : Nat} {r : List Nat} (hc : code[k]? = some .end_) :
    mbStep code (E, L, o :: r) k = (E.set! o k, if L[o]? = some 0 then L.set! o k else L, r) := by
  simp only [mbStep, hc]
  by_cases hz : L[o]? = some 0 <;> simp [hz]

theorem mbStep_end_nil (hc : code[k]? = some .end_) : mbStep code (E, L, []) k = (E, L, []) := by
  simp [mbStep, hc]

end steps

theorem mbFold_stack (code : Array Instr) : ∀ k, (mbFold code k).2.2 = openAt code k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [mbFold_succ]
    generalize mbFold code k = s at ih ⊢
    obtain ⟨E, L, S⟩ := s
    dsimp only at ih
    subst ih
    cases hc : code[k]? with
    | none => rw [mbStep_none hc, openAt_succ_none hc]
    | some i =>
      rw [openAt_succ_some hc]
      by_cases hop : isOpener i = true
      · rw [mbStep_opener hc hop, openStep_opener hop]
      by_cases he : i = .else_
      · subst he
        cases hS : openAt code k with
        | nil => simp [mbStep, hc, openStep]
        | cons o r => rw [mbStep_else hc]; rfl
      by_cases hn : i = .end_
      · subst hn
        cases hS : openAt code k with
        | nil => rw [mbStep_end_nil hc]; rfl
        | cons o r => rw [mbStep_end hc]; rfl
      · rw [mbStep_other hc (by simpa using hop) he hn, openStep_other (by simpa using hop) he hn]

theorem set_get_ne {a : Array Nat} {o x v : Nat} (h : o ≠ x) : (a.set! o v)[x]? = a[x]? := by
  simp [Array.getElem?_setIfInBounds, h]

theorem set_get_eq {a : Array Nat} {o v : Nat} (h : o < a.size) : (a.set! o v)[o]? = some v := by
  simp [Array.getElem?_setIfInBounds, h]

/-! ## The loop invariant of `matchBlocks` -/

/-- An `if` at `o` whose `else` is at `v`. -/
def ElseAt (code : Array Instr) (o v : Nat) : Prop :=
  o < v ∧ code[v]? = some .else_ ∧ openAt code v = o :: openAt code o

def IsIf (code : Array Instr) (o : Nat) : Prop := ∃ bt, code[o]? = some (.if_ bt)

structure InvS (code : Array Instr) (k : Nat) (E L : Array Nat) : Prop where
  sizeE : E.size = code.size
  sizeL : L.size = code.size
  /-- open blocks: `true` marks an `if` with no `else` yet; a `false` `if` has seen its `else` -/
  stack : Pair2 (fun b o => (b = true → IsIf code o ∧ L[o]? = some 0) ∧
      (b = false → IsIf code o → ∃ v, L[o]? = some v ∧ v < k ∧ ElseAt code o v))
    (bAt code k) (openAt code k)
  elses : ∀ j o r, j < k → code[j]? = some .else_ → openAt code j = o :: r → L[o]? = some j
  ends : ∀ j o r, j < k → code[j]? = some .end_ → openAt code j = o :: r → E[o]? = some j
  closed : ∀ o, o < k → code[o]?.map isOpener = some true → o ∉ openAt code k →
    ∃ e, o < e ∧ e < k ∧ code[e]? = some .end_ ∧ openAt code e = o :: openAt code o ∧
      (IsIf code o → L[o]? = some e ∨ ∃ v, L[o]? = some v ∧ v < e ∧ ElseAt code o v)
  fresh : ∀ o, k ≤ o → o < code.size → L[o]? = some 0

theorem lt_size_of_some {code : Array Instr} {k : Nat} {i : Instr} (h : code[k]? = some i) :
    k < code.size := (Array.getElem?_eq_some_iff.1 h).1

theorem not_opener_of {code : Array Instr} {k : Nat} {i : Instr} (h : code[k]? = some i)
    (hop : isOpener i = false) : ¬ (code[k]?.map isOpener = some true) := by
  simp [h, hop]

theorem invS_step {code : Array Instr} (hw : WellNested code) {k : Nat} {E L : Array Nat}
    (I : InvS code k E L) :
    InvS code (k + 1) (mbStep code (E, L, openAt code k) k).1 (mbStep code (E, L, openAt code k) k).2.1 := by
  obtain ⟨hEs, hLs, hP, hC, hC', hD, hZ⟩ := I
  -- monotonicity of the stack predicate in `k`
  have mono : ∀ b o, (b = true → IsIf code o ∧ L[o]? = some 0) ∧
      (b = false → IsIf code o → ∃ v, L[o]? = some v ∧ v < k ∧ ElseAt code o v) →
      (b = true → IsIf code o ∧ L[o]? = some 0) ∧
      (b = false → IsIf code o → ∃ v, L[o]? = some v ∧ v < k + 1 ∧ ElseAt code o v) :=
    fun b o ⟨h1, h2⟩ => ⟨h1, fun hb hi => let ⟨v, a, c, d⟩ := h2 hb hi; ⟨v, a, by omega, d⟩⟩
  cases hc : code[k]? with
  | none =>
    rw [mbStep_none hc]
    refine ⟨hEs, hLs, ?_, ?_, ?_, ?_, ?_⟩
    · rw [openAt_succ_none hc, bAt_succ_none hc]; exact Pair2.imp mono hP
    · intro j o r hj hcj hoj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact hC j o r hj hcj hoj
      · simp [hc] at hcj
    · intro j o r hj hcj hoj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact hC' j o r hj hcj hoj
      · simp [hc] at hcj
    · intro o ho hop hno
      rw [openAt_succ_none hc] at hno
      rcases Nat.lt_succ_iff_lt_or_eq.1 ho with ho | rfl
      · obtain ⟨e, h1, h2, h3⟩ := hD o ho hop hno
        exact ⟨e, h1, by omega, h3⟩
      · simp [hc] at hop
    · intro o ho hon; exact hZ o (by omega) hon
  | some i =>
    have hk := lt_size_of_some hc
    by_cases hop : isOpener i = true
    · -- an opener is pushed
      rw [mbStep_opener hc hop]
      dsimp only
      refine ⟨hEs, hLs, ?_, ?_, ?_, ?_, ?_⟩
      · rw [openAt_succ_some hc, openStep_opener hop, bAt_succ_some hc]
        have hP' := Pair2.imp mono hP
        cases i with
        | block bt =>
          exact Pair2.cons ⟨by simp, fun _ ⟨bt', h⟩ => by simp [hc] at h⟩ hP'
        | loop bt =>
          exact Pair2.cons ⟨by simp, fun _ ⟨bt', h⟩ => by simp [hc] at h⟩ hP'
        | if_ bt =>
          exact Pair2.cons ⟨fun _ => ⟨⟨_, hc⟩, hZ k (Nat.le_refl _) hk⟩, by simp⟩ hP'
        | _ => simp [isOpener] at hop
      · intro j o r hj hcj hoj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact hC j o r hj hcj hoj
        · rw [hc] at hcj; cases hcj; simp [isOpener] at hop
      · intro j o r hj hcj hoj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact hC' j o r hj hcj hoj
        · rw [hc] at hcj; cases hcj; simp [isOpener] at hop
      · intro o ho hop' hno
        rw [openAt_succ_some hc, openStep_opener hop] at hno
        have hne : o ≠ k := fun h => hno (by simp [h])
        have hno' : o ∉ openAt code k := fun h => hno (List.mem_cons_of_mem _ h)
        obtain ⟨e, h1, h2, h3⟩ := hD o (by omega) hop' hno'
        exact ⟨e, h1, by omega, h3⟩
      · intro o ho hon; exact hZ o (by omega) hon
    have hop : isOpener i = false := by simpa using hop
    by_cases he : i = .else_
    · subst he
      obtain ⟨s0, hs0⟩ := wellNested_else hw hc
      have hP0 := hP
      rw [hs0] at hP0
      cases hS : openAt code k with
      | nil => rw [hS] at hP0; exact hP0.elim
      | cons o r =>
        rw [hS] at hP0
        obtain ⟨_, hL0⟩ := hP0.1.1 rfl
        obtain ⟨hok, hor, _⟩ := openAt_chain code k o r hS
        have hoL : o < L.size := by omega
        have hrlt : ∀ x ∈ r, x ≠ o := fun x hx hxo => by
          rw [← hor] at hx; exact openAt_not_mem_self code o (hxo ▸ hx)
        rw [mbStep_else hc]
        dsimp only
        refine ⟨hEs, by simp [hLs], ?_, ?_, ?_, ?_, ?_⟩
        · rw [openAt_succ_some hc, hS, bAt_succ_some hc, hs0]
          simp only [openStep, bStep]
          refine Pair2.cons
            ⟨by simp, fun _ _ => ⟨k, set_get_eq hoL, by omega, hok, hc, by rw [hS, hor]⟩⟩ ?_
          refine Pair2.imp_mem (fun b x hx hb => ?_) hP0.2
          rw [set_get_ne (Ne.symm (hrlt x hx))]
          exact mono b x hb
        · intro j o2 r2 hj hcj hoj
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · by_cases ho2 : o2 = o
            · subst ho2
              have := hC j o2 r2 hj hcj hoj
              rw [hL0] at this; cases this
              have := (openAt_chain code 0 o2 r2 hoj).1; omega
            · rw [set_get_ne (Ne.symm ho2)]; exact hC j o2 r2 hj hcj hoj
          · rw [hS] at hoj; cases hoj; exact set_get_eq hoL
        · intro j o2 r2 hj hcj hoj
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact hC' j o2 r2 hj hcj hoj
          · rw [hc] at hcj; cases hcj
        · intro o2 ho2 hop2 hno
          rw [openAt_succ_some hc] at hno
          simp only [openStep] at hno
          have hne : o2 ≠ k := fun h => not_opener_of hc hop (h ▸ hop2)
          obtain ⟨e, h1, h2, h3, h4, h5⟩ := hD o2 (by omega) hop2 hno
          have hneo : o ≠ o2 := fun h => hno (by rw [hS, h]; simp)
          refine ⟨e, h1, by omega, h3, h4, ?_⟩
          rw [set_get_ne hneo]; exact h5
        · intro o2 ho2 hon
          rw [set_get_ne (by omega)]; exact hZ o2 (by omega) hon
    by_cases hn : i = .end_
    · subst hn
      cases hS : openAt code k with
      | nil =>
        have hb : bAt code k = [] := by
          have := hP.length; rw [hS] at this; exact List.eq_nil_of_length_eq_zero this
        rw [mbStep_end_nil hc]
        refine ⟨hEs, hLs, ?_, ?_, ?_, ?_, ?_⟩
        · rw [openAt_succ_some hc, hS, bAt_succ_some hc, hb]; exact trivial
        · intro j o r hj hcj hoj
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact hC j o r hj hcj hoj
          · rw [hc] at hcj; cases hcj
        · intro j o r hj hcj hoj
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact hC' j o r hj hcj hoj
          · rw [hS] at hoj; cases hoj
        · intro o ho hop2 hno
          have hne : o ≠ k := fun h => not_opener_of hc hop (h ▸ hop2)
          obtain ⟨e, h1, h2, h3⟩ := hD o (by omega) hop2 (by rw [hS]; simp)
          exact ⟨e, h1, by omega, h3⟩
        · intro o ho hon; exact hZ o (by omega) hon
      | cons o r =>
        have hP0 := hP
        rw [hS] at hP0
        cases hb : bAt code k with
        | nil => rw [hb] at hP0; exact hP0.elim
        | cons b s0 =>
        rw [hb] at hP0
        obtain ⟨⟨H1, H2⟩, hPt⟩ := hP0
        obtain ⟨hok, hor, _⟩ := openAt_chain code k o r hS
        have hoL : o < L.size := by omega
        have hoE : o < E.size := by omega
        have hrlt : ∀ x ∈ r, x ≠ o := fun x hx hxo => by
          rw [← hor] at hx; exact openAt_not_mem_self code o (hxo ▸ hx)
        have hL'ne : ∀ x, o ≠ x →
            (if L[o]? = some 0 then L.set! o k else L)[x]? = L[x]? := by
          intro x hx; split
          · exact set_get_ne hx
          · rfl
        rw [mbStep_end hc]
        dsimp only
        refine ⟨by simp [hEs], by split <;> simp [hLs], ?_, ?_, ?_, ?_, ?_⟩
        · rw [openAt_succ_some hc, hS, bAt_succ_some hc, hb]
          simp only [openStep, bStep, List.tail_cons]
          refine Pair2.imp_mem (fun b x hx hb => ?_) hPt
          rw [hL'ne x (Ne.symm (hrlt x hx))]
          exact mono b x hb
        · intro j o2 r2 hj hcj hoj
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · have hj' := hC j o2 r2 hj hcj hoj
            by_cases ho2 : o2 = o
            · subst ho2
              have : o2 < j := (openAt_chain code j o2 r2 hoj).1
              have hz : ¬ L[o2]? = some 0 := by rw [hj']; simp; omega
              simp only [hz, ite_false]; exact hj'
            · rw [hL'ne o2 (Ne.symm ho2)]; exact hj'
          · rw [hc] at hcj; cases hcj
        · intro j o2 r2 hj hcj hoj
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · by_cases ho2 : o2 = o
            · subst ho2
              exfalso
              obtain ⟨_, hjo, _⟩ := openAt_chain code j o2 r2 hoj
              have h1 : o2 ∉ openAt code (j + 1) := by
                rw [openAt_succ_some hcj, hoj]; simp only [openStep, List.tail_cons]
                rw [← hjo]; exact openAt_not_mem_self code o2
              have := openAt_not_mem_mono code o2 (j + 1)
                (by have := (openAt_chain code j o2 r2 hoj).1; omega) h1 k (by omega)
              rw [hS] at this; simp at this
            · rw [set_get_ne (Ne.symm ho2)]; exact hC' j o2 r2 hj hcj hoj
          · rw [hS] at hoj; cases hoj; exact set_get_eq hoE
        · intro o2 ho2 hop2 hno
          rw [openAt_succ_some hc, hS] at hno
          simp only [openStep, List.tail_cons] at hno
          by_cases heq : o2 = o
          · subst heq
            refine ⟨k, hok, by omega, hc, by rw [hS, hor], fun hif => ?_⟩
            cases b with
            | true =>
              obtain ⟨_, hz⟩ := H1 rfl
              left; simp only [hz, ite_true]; exact set_get_eq hoL
            | false =>
              obtain ⟨v, hv, hvk, hev⟩ := H2 rfl hif
              have hz : ¬ L[o2]? = some 0 := by rw [hv]; have := hev.1; simp; omega
              right; simp only [hz, ite_false]; exact ⟨v, hv, hvk, hev⟩
          · have hne : o2 ≠ k := fun h => not_opener_of hc hop (h ▸ hop2)
            have hno' : o2 ∉ openAt code k := by
              rw [hS]; simp [heq, hno]
            obtain ⟨e, h1, h2, h3, h4, h5⟩ := hD o2 (by omega) hop2 hno'
            refine ⟨e, h1, by omega, h3, h4, ?_⟩
            rw [hL'ne o2 (Ne.symm heq)]; exact h5
        · intro o2 ho2 hon
          rw [hL'ne o2 (by omega)]; exact hZ o2 (by omega) hon
    · -- any other instruction leaves everything alone
      rw [mbStep_other hc hop he hn]
      refine ⟨hEs, hLs, ?_, ?_, ?_, ?_, ?_⟩
      · rw [openAt_succ_some hc, openStep_other hop he hn, bAt_succ_some hc, bStep_other hop he hn]
        exact Pair2.imp mono hP
      · intro j o r hj hcj hoj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact hC j o r hj hcj hoj
        · rw [hc] at hcj; cases hcj; exact absurd rfl he
      · intro j o r hj hcj hoj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact hC' j o r hj hcj hoj
        · rw [hc] at hcj; cases hcj; exact absurd rfl hn
      · intro o ho hop2 hno
        rw [openAt_succ_some hc, openStep_other hop he hn] at hno
        have hne : o ≠ k := fun h => not_opener_of hc hop (h ▸ hop2)
        obtain ⟨e, h1, h2, h3⟩ := hD o (by omega) hop2 hno
        exact ⟨e, h1, by omega, h3⟩
      · intro o ho hon; exact hZ o (by omega) hon

theorem invS_all {code : Array Instr} (hw : WellNested code) :
    ∀ k, InvS code k (mbFold code k).1 (mbFold code k).2.1 := by
  intro k
  induction k with
  | zero =>
    refine ⟨by simp [mbFold, mbInit], by simp [mbFold, mbInit], trivial, ?_, ?_, ?_, ?_⟩
    · intro j _ _ hj; omega
    · intro j _ _ hj; omega
    · intro o ho; omega
    · intro o _ ho; simp [mbFold, mbInit, ho]
  | succ k ih =>
    rw [mbFold_succ]
    have e : mbFold code k = ((mbFold code k).1, (mbFold code k).2.1, openAt code k) := by
      rw [← mbFold_stack code k]
    rw [e]
    exact invS_step hw ih

/-! ## (A) `NestOK` from well-nestedness -/

theorem nestOK_of_wellNested (pf : PFunc) (h : WellNested pf.code)
    (he : matchBlocks pf.code = (pf.endOf, pf.elseOf)) : NestOK pf (openAt pf.code) := by
  have hmb := matchBlocks_eq pf.code
  rw [he] at hmb
  have hE : pf.endOf = (mbFold pf.code pf.code.size).1 := congrArg Prod.fst hmb
  have hL : pf.elseOf = (mbFold pf.code pf.code.size).2.1 := congrArg Prod.snd hmb
  have Iall := invS_all h
  have IN := Iall pf.code.size
  rw [← hE, ← hL] at IN
  obtain ⟨hEs, hLs, _, hC, hC', hD, _⟩ := IN
  have hfin : openAt pf.code pf.code.size = [] := by
    have := (Iall pf.code.size).stack.length
    rw [wellNested_final h] at this
    exact List.eq_nil_of_length_eq_zero this.symm
  -- every opener is closed by the `end` that `endOf` records
  have closed : ∀ o, o < pf.code.size → pf.code[o]?.map isOpener = some true →
      ∃ e, o < e ∧ e < pf.code.size ∧ pf.code[e]? = some .end_ ∧
        openAt pf.code e = o :: openAt pf.code o ∧ endAt pf o = e ∧
        (IsIf pf.code o → elseAt pf o = e ∨ (o < elseAt pf o ∧ elseAt pf o < e ∧
          ElseAt pf.code o (elseAt pf o))) := by
    intro o ho hop
    obtain ⟨e, h1, h2, h3, h4, h5⟩ := hD o ho hop (by rw [hfin]; simp)
    refine ⟨e, h1, h2, h3, h4, by simp [endAt, hC' e o _ h2 h3 h4], fun hif => ?_⟩
    rcases h5 hif with h5 | ⟨v, hv, hve, hev⟩
    · left; simp [elseAt, h5]
    · right; simp only [elseAt, hv, Option.getD_some]; exact ⟨hev.1, hve, hev⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro pc o rest _ hor; exact openAt_chain _ pc o rest hor
  · intro pc i hi hop
    have hpc := lt_size_of_some hi
    obtain ⟨e, hoe, _, hce, hoa, hend, _⟩ := closed pc hpc (by simp [hi, hop])
    rw [hend]
    refine ⟨?_, hoe, hce, by rw [openAt_succ_some hi, openStep_opener hop], hoa⟩
    rw [← hend]; simp [endAt, Array.getElem?_eq_getElem (show pc < pf.endOf.size by omega)]
  · intro pc hpc
    have hlt := lt_size_of_some hpc
    refine ⟨fun hnil => ?_, fun o rest hor => ?_⟩
    · apply wellNested_end h hpc
      have := (Iall pc).stack.length
      rw [hnil] at this
      exact List.eq_nil_of_length_eq_zero this
    · exact ⟨by simp [endAt, hC' pc o rest hlt hpc hor], by
        rw [openAt_succ_some hpc, hor]; rfl⟩
  · intro pc hpc
    have hlt := lt_size_of_some hpc
    obtain ⟨s, hs⟩ := wellNested_else h hpc
    have P := (Iall pc).stack
    rw [hs] at P
    cases hor : openAt pf.code pc with
    | nil => rw [hor] at P; exact P.elim
    | cons o rest =>
      rw [hor] at P
      obtain ⟨⟨bt, hbt⟩, _⟩ := P.1.1 rfl
      obtain ⟨hopc, _, hopn⟩ := openAt_chain _ pc o rest hor
      obtain ⟨e, hoe, _, hce, hoa, hend, _⟩ := closed o (by omega) hopn
      refine ⟨o, rest, bt, rfl, hbt, by simp [elseAt, hC pc o rest hlt hpc hor], ?_, by
        rw [openAt_succ_some hpc, hor]; rfl⟩
      rw [hend]
      refine Nat.lt_of_not_le fun hle => ?_
      rcases Nat.eq_or_lt_of_le hle with rfl | hlt'
      · rw [hce] at hpc; cases hpc
      · have h1 : o ∉ openAt pf.code (e + 1) := by
          rw [openAt_succ_some hce, hoa]; exact openAt_not_mem_self _ o
        have := openAt_not_mem_mono _ o (e + 1) (by omega) h1 pc (by omega)
        rw [hor] at this; simp at this
  · intro o bt hbt
    have hlt := lt_size_of_some hbt
    refine ⟨by simp [elseAt, Array.getElem?_eq_getElem (show o < pf.elseOf.size by omega)], ?_⟩
    obtain ⟨e, _, _, _, _, hend, hif⟩ := closed o hlt (by simp [hbt, isOpener])
    rw [hend]
    rcases hif ⟨bt, hbt⟩ with h1 | ⟨h1, h2, h3⟩
    · exact Or.inl h1
    · refine Or.inr ⟨h1, h2, h3.2.1, ?_⟩
      rw [openAt_succ_some h3.2.1]; exact h3.2.2
  · intro pc i hi hop he hn
    rw [openAt_succ_some hi, openStep_other hop he hn]


/-! ## (B) free instructions are bounded by the block count -/

/-- The block count `prepare` computes (`blocks`). -/
def blockCount (code : Array Instr) : Nat :=
  code.foldl (fun a i => match i with | .block _ | .loop _ | .if_ _ => a + 1 | _ => a) 0

def fw (i : Instr) : Nat := if isFreeInstr i then 1 else 0

def ow (i : Instr) : Nat := if isOpener i then 1 else 0

theorem foldl_add {f : Nat → Instr → Nat} (g : Instr → Nat) (hg : ∀ a x, f a x = a + g x) :
    ∀ (l : List Instr) (a : Nat), l.foldl f a = a + (l.map g).sum
  | [], a => by simp
  | x :: l, a => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, hg, foldl_add g hg l]; omega

theorem freeCount_eq (code : Array Instr) : freeCount code = (code.toList.map fw).sum := by
  rw [freeCount, ← Array.foldl_toList, foldl_add fw (fun a x => by unfold fw; split <;> rfl)]
  simp

theorem blockCount_eq (code : Array Instr) : blockCount code = (code.toList.map ow).sum := by
  rw [blockCount, ← Array.foldl_toList, foldl_add ow (fun a x => by cases x <;> rfl)]
  simp

theorem fw_ow_other {i : Instr} (hop : isOpener i = false) (he : i ≠ .else_) (hn : i ≠ .end_) :
    fw i = 0 ∧ ow i = 0 := by
  cases i <;> simp_all [fw, ow, isFreeInstr, isOpener]

theorem free_bound : ∀ (l : List Instr) (st : List Bool), nestScan l st = true →
    (l.map fw).sum ≤ 2 * (l.map ow).sum + st.length + st.count true + 1
  | [], _, h => by simp [nestScan] at h
  | i :: rest, st, h => by
    by_cases he : i = .else_
    · subst he
      match st, h with
      | true :: st', h =>
        have := free_bound rest (false :: st') (by simpa [nestScan] using h)
        simp [fw, ow, isFreeInstr, isOpener] at this ⊢; omega
      | false :: _, h => simp [nestScan] at h
      | [], h => simp [nestScan] at h
    by_cases hn : i = .end_
    · subst hn
      match st, h with
      | [], h =>
        have hr : rest = [] := by simpa [nestScan] using h
        subst hr
        simp [fw, isFreeInstr]
      | b :: st', h =>
        have := free_bound rest st' (by simpa [nestScan] using h)
        simp only [List.map_cons, List.sum_cons, List.length_cons, List.count_cons] at this ⊢
        simp only [fw, ow, isFreeInstr, isOpener] at this ⊢
        split at * <;> simp at * <;> omega
    · rw [nestScan_cons_other he hn] at h
      have ih := free_bound rest _ h
      by_cases hop : isOpener i = true
      · cases i <;> simp_all [isOpener, bStep, fw, ow, isFreeInstr] <;> omega
      · have hop : isOpener i = false := by simpa using hop
        rw [bStep_other hop he hn] at ih
        obtain ⟨h1, h2⟩ := fw_ow_other hop he hn
        simp only [List.map_cons, List.sum_cons, h1, h2]; omega

theorem freeCount_le_of_wellNested (code : Array Instr) (h : WellNested code) :
    freeCount code ≤ 2 * code.foldl (fun a i => match i with
      | .block _ | .loop _ | .if_ _ => a + 1
      | _ => a) 0 + 1 := by
  have := free_bound _ _ h
  have hb := blockCount_eq code
  unfold blockCount at hb
  rw [freeCount_eq, hb]
  simpa using this


def K (s : VS) : List CK := s.ctrls.map (·.kind)

theorem run_bind_ok {α β : Type} {x : V α} {f : α → V β} {s s' : VS} {b : β}
    (h : (x >>= f).run s = .ok (b, s')) :
    ∃ a s1, x.run s = .ok (a, s1) ∧ (f a).run s1 = .ok (b, s') := by
  rw [StateT.run_bind] at h
  cases hx : x.run s with
  | error e => rw [hx] at h; cases h
  | ok p =>
    rw [hx] at h
    exact ⟨p.1, p.2, rfl, h⟩

def Pres {α : Type} (x : V α) : Prop := ∀ s a s', x.run s = .ok (a, s') → K s' = K s

theorem pres_bind {α β : Type} {x : V α} {f : α → V β} (hx : Pres x) (hf : ∀ a, Pres (f a)) :
    Pres (x >>= f) := by
  intro s b s' h
  obtain ⟨a, s1, h1, h2⟩ := run_bind_ok h
  rw [hf a s1 b s' h2, hx s a s1 h1]

theorem pres_pure {α : Type} (a : α) : Pres (pure a : V α) := by
  intro s b s' h; cases h; rfl

theorem pres_throw {α : Type} (e : String) : Pres (throw e : V α) := by
  intro s b s' h; cases h

theorem pres_get : Pres (get : V VS) := by
  intro s b s' h; cases h; rfl

theorem pres_modify {f : VS → VS} (hf : ∀ s, K (f s) = K s) : Pres (modify f : V Unit) := by
  intro s b s' h; cases h; exact hf s

theorem pres_restore {α β : Type} (x : V α) (r : β) :
    Pres (do let saved ← (MonadState.get : V VS); let _ ← x; set saved; Pure.pure r : V β) := by
  intro s b s' h
  obtain ⟨a, s1, h1, h2⟩ := run_bind_ok h
  cases h1
  obtain ⟨a2, s2, h3, h4⟩ := run_bind_ok h2
  obtain ⟨a3, s3, h5, h6⟩ := run_bind_ok h4
  cases h5; cases h6; rfl

theorem pres_forIn_list {β γ : Type} {f : β → γ → V (ForInStep γ)} (hf : ∀ b c, Pres (f b c)) :
    ∀ (l : List β) (init : γ), Pres (forIn l init f)
  | [], init => pres_pure init
  | b :: l, init => by
    rw [List.forIn_cons]
    refine pres_bind (hf b init) fun r => ?_
    split
    · exact pres_pure _
    · exact pres_forIn_list hf l _

theorem pres_forIn_array {β γ : Type} {f : β → γ → V (ForInStep γ)} (hf : ∀ b c, Pres (f b c))
    (a : Array β) (init : γ) : Pres (forIn a init f) := by
  rw [← Array.forIn_toList]; exact pres_forIn_list hf _ _


theorem pres_getBind {α : Type} {f : VS → V α}
    (hf : ∀ s0 a s', (f s0).run s0 = .ok (a, s') → K s' = K s0) : Pres (get >>= f) := by
  intro s b s' h
  obtain ⟨a, s1, h1, h2⟩ := run_bind_ok h
  cases h1
  exact hf s b s' h2

theorem pres_vPush (t : Option VT) : Pres (vPush t) := pres_modify fun _ => rfl

theorem pres_vPop : Pres vPop := by
  unfold vPop
  refine pres_getBind fun s0 a s' h => ?_
  split at h
  · cases h
  · split at h
    · split at h
      · cases h; rfl
      · cases h
    · obtain ⟨_, s1, h1, h2⟩ := run_bind_ok h
      cases h1; cases h2; rfl

theorem pres_vPopT (w : VT) : Pres (vPopT w) := by
  unfold vPopT
  refine pres_bind pres_vPop fun t => ?_
  split
  · exact pres_pure _
  · split
    · exact pres_pure _
    · exact pres_throw _

theorem pres_vPopVals (ts : Array VT) : Pres (vPopVals ts) := by
  unfold vPopVals
  exact pres_bind (pres_forIn_array (fun t _ => pres_bind (pres_vPopT t) fun _ => pres_pure _) _ _) fun _ => pres_pure _

theorem pres_vPushVals (ts : Array VT) : Pres (vPushVals ts) := by
  unfold vPushVals
  exact pres_bind (pres_forIn_array (fun t _ => pres_bind (pres_vPush _) fun _ => pres_pure _) _ _) fun _ => pres_pure _

theorem pres_vUnreachable : Pres vUnreachable := by
  unfold vUnreachable
  refine pres_modify fun s => ?_
  split <;> simp_all [K]

theorem pres_vLabel (l : Nat) : Pres (vLabel l) := by
  unfold vLabel
  refine pres_bind pres_get fun s => ?_
  split
  · exact pres_pure _
  · exact pres_throw _

theorem pres_needMem (c : Ctx) : Pres (needMem c) := by
  unfold needMem
  split
  · exact pres_throw _
  · exact pres_pure _

theorem pres_tableTy (c : Ctx) (t : Nat) : Pres (tableTy c t) := by
  unfold tableTy
  split
  · exact pres_pure _
  · exact pres_throw _

macro "pres_tac" : tactic => `(tactic| repeat' (with_reducible first
  | exact pres_pure _ | exact pres_throw _ | exact pres_vPush _ | exact pres_vPop
  | exact pres_vPopT _ | exact pres_vPopVals _ | exact pres_vPushVals _ | exact pres_vUnreachable
  | exact pres_vLabel _ | exact pres_needMem _ | exact pres_tableTy _ _ | exact pres_get
  | exact pres_restore _ _
  | apply pres_forIn_array | apply pres_bind | (intro _) | split))

theorem pres_checkInstr_other (c : Ctx) (L R : Array VT) {i : Instr} (hop : isOpener i = false)
    (he : i ≠ .else_) (hn : i ≠ .end_) : Pres (checkInstr c L R i) := by
  cases i
  case select t => cases t <;> simp only [checkInstr] <;> pres_tac
  all_goals (try simp [isOpener] at hop) <;> (try exact absurd rfl he) <;>
    (try exact absurd rfl hn) <;> simp only [checkInstr] <;> pres_tac


/-! ### Control-stack effect of the structured instructions -/

theorem vPushCtrl_spec {k : CK} {rs : Array VT} {s s' : VS} {a : Unit}
    (h : (vPushCtrl k rs).run s = .ok (a, s')) : K s' = k :: K s := by
  cases h; rfl

theorem vPopCtrl_spec {s s' : VS} {f : Ctrl} (h : vPopCtrl.run s = .ok (f, s')) :
    K s = f.kind :: K s' := by
  unfold vPopCtrl at h
  obtain ⟨s0, s1, h1, h2⟩ := run_bind_ok h
  cases h1
  split at h2
  · cases h2
  · rename_i c cs hcs
    obtain ⟨_, s2, h3, h4⟩ := run_bind_ok h2
    have hK2 := pres_vPopVals _ _ _ _ h3
    obtain ⟨_, s3, h5, h6⟩ := run_bind_ok h4
    cases h5
    dsimp only at h6
    split at h6
    · obtain ⟨_, _, h7, _⟩ := run_bind_ok h6; cases h7
    obtain ⟨_, s5, h9, h10⟩ := run_bind_ok h6
    cases h9; cases h10
    simp only [K] at hK2 ⊢
    have ht : ∀ l : List Ctrl, l.tail.map (·.kind) = (l.map (·.kind)).tail := by
      intro l; cases l <;> rfl
    rw [ht, hK2, hcs]; rfl

theorem ci_block {c : Ctx} {L R : Array VT} {bt : BT} {s s' : VS} {a : Unit}
    (h : (checkInstr c L R (.block bt)).run s = .ok (a, s')) : K s' = .block :: K s :=
  vPushCtrl_spec h

theorem ci_loop {c : Ctx} {L R : Array VT} {bt : BT} {s s' : VS} {a : Unit}
    (h : (checkInstr c L R (.loop bt)).run s = .ok (a, s')) : K s' = .loop :: K s :=
  vPushCtrl_spec h

theorem ci_if {c : Ctx} {L R : Array VT} {bt : BT} {s s' : VS} {a : Unit}
    (h : (checkInstr c L R (.if_ bt)).run s = .ok (a, s')) : K s' = .if_ :: K s := by
  obtain ⟨_, s1, h1, h2⟩ := run_bind_ok h
  rw [vPushCtrl_spec h2, pres_vPopT _ _ _ _ h1]

theorem ci_else {c : Ctx} {L R : Array VT} {s s' : VS} {a : Unit}
    (h : (checkInstr c L R .else_).run s = .ok (a, s')) :
    ∃ rest, K s = .if_ :: rest ∧ K s' = .else_ :: rest := by
  obtain ⟨f, s1, h1, h2⟩ := run_bind_ok h
  have hK := vPopCtrl_spec h1
  dsimp only at h2
  split at h2
  · obtain ⟨_, _, h3, _⟩ := run_bind_ok h2; cases h3
  · rename_i hk
    have hk : f.kind = .if_ := by simpa using hk
    exact ⟨K s1, by rw [hK, hk], vPushCtrl_spec h2⟩

theorem ci_end {c : Ctx} {L R : Array VT} {s s' : VS} {a : Unit}
    (h : (checkInstr c L R .end_).run s = .ok (a, s')) : ∃ k, K s = k :: K s' := by
  obtain ⟨f, s1, h1, h2⟩ := run_bind_ok h
  have hK := vPopCtrl_spec h1
  dsimp only at h2
  have tail : ∀ s2 a2 s3, (if f.kind ≠ CK.func then vPushVals f.results else pure ()).run s2
      = .ok (a2, s3) → K s3 = K s2 := by
    intro s2 a2 s3 h; split at h
    · exact pres_vPushVals _ _ _ _ h
    · cases h; rfl
  split at h2
  · obtain ⟨_, _, h3, _⟩ := run_bind_ok h2; cases h3
  · exact ⟨f.kind, by rw [hK, tail _ _ _ h2]⟩

/-! ### The control stack tracks `nestScan`'s stack -/

/-- `validateBody`'s control kinds against `nestScan`'s stack: one frame per scan entry (`true`
exactly for an `if` frame), then the function frame. -/
def RelK : List Bool → List CK → Prop
  | [], ks => ks = [.func]
  | b :: bs, k :: ks => (b = true ↔ k = .if_) ∧ RelK bs ks
  | _ :: _, [] => False

theorem RelK.ne_nil : ∀ {st : List Bool} {ks : List CK}, RelK st ks → ks ≠ []
  | [], _, h => by simp [RelK] at h; simp [h]
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, _ => by simp

theorem isEmpty_iff_K (s : VS) : s.ctrls.isEmpty = true ↔ K s = [] := by
  simp [K]

theorem forIn_true_nil {body : Instr → Bool → V (ForInStep Bool)}
    (hT : ∀ i s r s', (body i true).run s = .ok (r, s') → False) :
    ∀ (l : List Instr) (s s' : VS) (b : Bool), (forIn l true body).run s = .ok (b, s') → l = []
  | [], _, _, _, _ => rfl
  | i :: rest, s, s', b, h => by
    rw [List.forIn_cons] at h
    obtain ⟨_, _, h1, _⟩ := run_bind_ok h
    exact (hT _ _ _ _ h1).elim

theorem loop_scan (c : Ctx) (L R : Array VT) {body : Instr → Bool → V (ForInStep Bool)}
    (hT : ∀ i s r s', (body i true).run s = .ok (r, s') → False)
    (hF : ∀ i s r s', (body i false).run s = .ok (r, s') →
      (checkInstr c L R i).run s = .ok ((), s') ∧ r = .yield s'.ctrls.isEmpty) :
    ∀ (l : List Instr) (s s' : VS) (st : List Bool), RelK st (K s) →
      (forIn l false body).run s = .ok (true, s') → nestScan l st = true
  | [], s, s', st, _, h => by cases h
  | i :: rest, s, s', st, hR, h => by
    rw [List.forIn_cons] at h
    obtain ⟨r, s1, h1, h2⟩ := run_bind_ok h
    obtain ⟨hci, hr⟩ := hF _ _ _ _ h1
    subst hr
    simp only at h2
    by_cases hemp : s1.ctrls.isEmpty = true
    · rw [hemp] at h2
      have hrest := forIn_true_nil hT _ _ _ _ h2
      subst hrest
      have hK1 := (isEmpty_iff_K s1).1 hemp
      -- only the function's `end` empties the control stack
      by_cases hn : i = .end_
      · subst hn
        obtain ⟨k, hk⟩ := ci_end hci
        rw [hK1] at hk
        rw [hk] at hR
        match st, hR with
        | [], _ => rfl
        | _ :: bs, hR => exact absurd hR.2 (by intro h; exact RelK.ne_nil h rfl)
      exfalso
      by_cases he : i = .else_
      · subst he
        obtain ⟨_, _, h2'⟩ := ci_else hci
        rw [hK1] at h2'; cases h2'
      by_cases hop : isOpener i = true
      · cases i <;> simp [isOpener] at hop
        · rw [ci_block hci] at hK1; cases hK1
        · rw [ci_loop hci] at hK1; cases hK1
        · rw [ci_if hci] at hK1; cases hK1
      · have := pres_checkInstr_other c L R (by simpa using hop) he hn _ _ _ hci
        rw [hK1] at this
        exact RelK.ne_nil hR this.symm
    · have hemp' : s1.ctrls.isEmpty = false := by simpa using hemp
      rw [hemp'] at h2
      by_cases he : i = .else_
      · subst he
        obtain ⟨rest', hK, hK1⟩ := ci_else hci
        rw [hK] at hR
        match st, hR with
        | b :: bs, ⟨hb, hR⟩ =>
          have hb : b = true := hb.2 rfl
          subst hb
          exact loop_scan c L R hT hF rest s1 s' (false :: bs) (by rw [hK1]; exact ⟨by simp, hR⟩) h2
      by_cases hn : i = .end_
      · subst hn
        obtain ⟨k, hk⟩ := ci_end hci
        rw [hk] at hR
        match st, hR with
        | [], hR =>
          simp [RelK] at hR
          exact absurd ((isEmpty_iff_K s1).2 hR.2) hemp
        | b :: bs, ⟨_, hR⟩ => exact loop_scan c L R hT hF rest s1 s' bs hR h2
      rw [nestScan_cons_other he hn]
      by_cases hop : isOpener i = true
      · cases i <;> simp [isOpener] at hop
        · exact loop_scan c L R hT hF rest s1 s' _ (by rw [ci_block hci]; exact ⟨by simp, hR⟩) h2
        · exact loop_scan c L R hT hF rest s1 s' _ (by rw [ci_loop hci]; exact ⟨by simp, hR⟩) h2
        · exact loop_scan c L R hT hF rest s1 s' _ (by rw [ci_if hci]; exact ⟨by simp, hR⟩) h2
      · have hop : isOpener i = false := by simpa using hop
        rw [bStep_other hop he hn]
        exact loop_scan c L R hT hF rest s1 s' st
          (by rw [pres_checkInstr_other c L R hop he hn _ _ _ hci]; exact hR) h2

theorem exc_ok {α : Type} {x : Except String α} (h : (x >>= fun _ => pure ()) = Except.ok ()) :
    ∃ a, x = .ok a := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl⟩

/-- (C) a body that `validateBody` accepts is well nested. -/
theorem validateBody_wellNested (c : Ctx) (ft : FuncType) (locals : Array VT) (code : Array Instr)
    (h : validateBody c ft locals code = .ok ()) : WellNested code := by
  unfold validateBody at h
  obtain ⟨⟨_, s'⟩, hr⟩ := exc_ok h
  obtain ⟨_, s1, h1, h2⟩ := run_bind_ok hr
  have hK1 := vPushCtrl_spec h1
  obtain ⟨done, s2, h3, h4⟩ := run_bind_ok h2
  have hdone : done = true := by
    cases done
    · dsimp only at h4; cases h4
    · rfl
  subst hdone
  rw [← Array.forIn_toList] at h3
  refine loop_scan c (ft.params ++ locals) ft.results ?_ ?_ code.toList s1 s2 []
    (by rw [hK1]; rfl) h3
  · intro i s r s'' hb
    dsimp only at hb
    obtain ⟨_, _, h5, _⟩ := run_bind_ok hb
    cases h5
  · intro i s r s'' hb
    dsimp only at hb
    obtain ⟨_, s3, h5, h6⟩ := run_bind_ok hb
    obtain ⟨_, s4, h7, h8⟩ := run_bind_ok h6
    cases h7
    split at h8
    · rename_i he; cases h8; exact ⟨h5, by rw [he]⟩
    · rename_i he; cases h8; exact ⟨h5, by simpa using he⟩


/-! ## (D) the early pass keeps only validated bodies -/

/-- Every defined function of the module under construction is well nested. -/
def fval {β : Type} : ForInStep β → β
  | .done b => b
  | .yield b => b

def IW (s : PS) : Prop := ∀ f ∈ s.m.funcs.toList, WellNested f.code

def runPM {α : Type} (x : PM α) (s : PS) (b : ByteArray) (pos : Nat) :
    Except PE ((α × PS) × Nat) := ((x.run s).run b).run pos

/-- `x` keeps `IW` and its result satisfies `R`. -/
def PQ {α : Type} (x : PM α) (R : α → Prop) : Prop :=
  ∀ s b pos a s' pos', IW s → runPM x s b pos = .ok ((a, s'), pos') → IW s' ∧ R a

theorem pm_bind_ok {α β : Type} {x : PM α} {f : α → PM β} {s s' : PS} {b : ByteArray}
    {pos pos' : Nat} {c : β} (h : runPM (x >>= f) s b pos = .ok ((c, s'), pos')) :
    ∃ a s1 pos1, runPM x s b pos = .ok ((a, s1), pos1) ∧ runPM (f a) s1 b pos1 = .ok ((c, s'), pos') := by
  unfold runPM at *
  rw [StateT.run_bind, ReaderT.run_bind, StateT.run_bind] at h
  cases hx : ((x.run s).run b).run pos with
  | error e => rw [hx] at h; cases h
  | ok p =>
    rw [hx] at h
    exact ⟨p.1.1, p.1.2, p.2, rfl, h⟩

theorem pq_bind {α β : Type} {x : PM α} {f : α → PM β} {R1 : α → Prop} {R : β → Prop}
    (hx : PQ x R1) (hf : ∀ a, R1 a → PQ (f a) R) : PQ (x >>= f) R := by
  intro s b pos c s' pos' hs h
  obtain ⟨a, s1, pos1, h1, h2⟩ := pm_bind_ok h
  obtain ⟨hs1, ha⟩ := hx _ _ _ _ _ _ hs h1
  exact hf a ha _ _ _ _ _ _ hs1 h2

theorem pq_bindT {α β : Type} {x : PM α} {f : α → PM β} {R : β → Prop}
    (hx : PQ x (fun _ => True)) (hf : ∀ a, PQ (f a) R) : PQ (x >>= f) R :=
  pq_bind hx fun a _ => hf a

theorem pq_getBind {α : Type} {f : PS → PM α} {R : α → Prop}
    (hf : ∀ s0, IW s0 → PQ (f s0) R) : PQ (get >>= f) R := by
  intro s b pos c s' pos' hs h
  obtain ⟨a, s1, pos1, h1, h2⟩ := pm_bind_ok h
  cases h1
  exact hf s hs _ _ _ _ _ _ hs h2

theorem pq_pure {α : Type} {R : α → Prop} (a : α) (ha : R a) : PQ (pure a) R := by
  intro s b pos c s' pos' hs h
  cases h; exact ⟨hs, ha⟩

theorem pq_pureT {α : Type} (a : α) : PQ (pure a) (fun _ => True) := pq_pure a trivial

theorem pq_throw {α : Type} {R : α → Prop} (e : PE) : PQ (throw e : PM α) R := by
  intro s b pos c s' pos' hs h
  cases h

theorem pq_get : PQ (get : PM PS) (fun _ => True) := by
  intro s b pos c s' pos' hs h
  cases h; exact ⟨hs, trivial⟩

theorem pq_set {s0 : PS} (h0 : IW s0) : PQ (set s0 : PM PUnit) (fun _ => True) := by
  intro s b pos c s' pos' hs h
  cases h; exact ⟨h0, trivial⟩

theorem pq_modify {f : PS → PS} (hf : ∀ s, IW s → IW (f s)) :
    PQ (modify f : PM PUnit) (fun _ => True) := by
  intro s b pos c s' pos' hs h
  cases h; exact ⟨hf s hs, trivial⟩

theorem pq_getNat : PQ (getThe Nat : PM Nat) (fun _ => True) := by
  intro s b pos c s' pos' hs h
  cases h; exact ⟨hs, trivial⟩

theorem pq_setNat (n : Nat) : PQ (set (σ := Nat) n : PM PUnit) (fun _ => True) := by
  intro s b pos c s' pos' hs h
  cases h; exact ⟨hs, trivial⟩

theorem pq_read : PQ (readThe ByteArray : PM ByteArray) (fun _ => True) := by
  intro s b pos c s' pos' hs h
  cases h; exact ⟨hs, trivial⟩

theorem pq_liftP {α : Type} (x : P α) : PQ (liftP x) (fun _ => True) := by
  intro s b pos c s' pos' hs h
  unfold runPM liftP at h
  dsimp only [StateT.run, ReaderT.run] at h
  split at h
  · cases h; exact ⟨hs, trivial⟩
  · cases h

theorem pq_boundedP {α : Type} (stop : Nat) (x : P α) : PQ (boundedP stop x) (fun _ => True) :=
  pq_liftP _

theorem pq_deser {α : Type} {R : α → Prop} (w : String) : PQ (deser w : PM α) R := pq_throw _

theorem pq_prepFail {α : Type} {R : α → Prop} (v w : String) : PQ (prepFail v w : PM α) R :=
  pq_throw _

theorem pq_idxPM {α : Type} (a : Array α) (i : Nat) (w : String) : PQ (idxPM a i w) (fun _ => True) := by
  unfold idxPM
  split
  · exact pq_pureT _
  · exact pq_throw _

/-- A `for` loop whose body keeps `IW` and the loop-state invariant `A`. -/
theorem pq_forIn_list {β σ : Type} {body : β → σ → PM (ForInStep σ)} (A : σ → Prop)
    (hb : ∀ x c, A c → PQ (body x c) (fun r => A (fval r))) :
    ∀ (l : List β) (init : σ), A init → PQ (forIn l init body) A
  | [], init, hi => pq_pure _ hi
  | x :: l, init, hi => by
    rw [List.forIn_cons]
    refine pq_bind (hb x init hi) fun r hr => ?_
    cases r with
    | done c => exact pq_pure _ hr
    | yield c => exact pq_forIn_list A hb l c hr

theorem pq_forIn_listT {β σ : Type} {body : β → σ → PM (ForInStep σ)}
    (hb : ∀ x c, PQ (body x c) (fun _ => True)) (l : List β) (init : σ) :
    PQ (forIn l init body) (fun _ => True) :=
  pq_forIn_list (fun _ => True) (fun x c _ => by
    intro s b pos a s' pos' hs h; exact ⟨(hb x c _ _ _ _ _ _ hs h).1, trivial⟩) l init trivial

theorem pq_forIn_arrayT {β σ : Type} {body : β → σ → PM (ForInStep σ)}
    (hb : ∀ x c, PQ (body x c) (fun _ => True)) (l : Array β) (init : σ) :
    PQ (forIn l init body) (fun _ => True) := by
  rw [← Array.forIn_toList]; exact pq_forIn_listT hb _ _

theorem pq_forIn_rangeT {σ : Type} {body : Nat → σ → PM (ForInStep σ)}
    (hb : ∀ x c, PQ (body x c) (fun _ => True)) (r : Std.Legacy.Range) (init : σ) :
    PQ (forIn r init body) (fun _ => True) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']; exact pq_forIn_listT hb _ _

theorem pq_trivial {α : Type} {x : PM α} {R : α → Prop} (h : PQ x (fun _ => True))
    (hR : ∀ a, R a) : PQ x R := by
  intro s b pos a s' pos' hs hx; exact ⟨(h _ _ _ _ _ _ hs hx).1, hR a⟩

theorem pq_constOk (c : Ctx) (w : VT) (e : ConstE) : PQ (constOk c w e) (fun _ => True) := by
  unfold constOk
  split
  · split
    · exact pq_pureT _
    · exact pq_throw _
  · exact pq_throw _

def AllWN (fs : Array Func) : Prop := ∀ f ∈ fs.toList, WellNested f.code

theorem pq_forIn_bind_WN {β : Type} {body : Nat → Array Func → PM (ForInStep (Array Func))}
    {f : Array Func → PM β} {R : β → Prop} {r : Std.Legacy.Range} {init : Array Func}
    (hb : ∀ x c, AllWN c → PQ (body x c) (fun r => AllWN (fval r))) (hi : AllWN init)
    (hf : ∀ fs, AllWN fs → PQ (f fs) R) : PQ (forIn r init body >>= f) R := by
  refine pq_bind (R1 := AllWN) ?_ hf
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact pq_forIn_list AllWN hb _ _ hi

theorem allWN_empty : AllWN #[] := by simp [AllWN]

theorem allWN_push_of {c : Array Func} {f : Func} {cx : Ctx} {ft : FuncType} {locals : Array VT}
    (hc : AllWN c) (hv : validateBody cx ft locals f.code = .ok ()) :
    AllWN (fval (ForInStep.yield (c.push f))) := by
  intro g hg
  simp only [fval, Array.toList_push, List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact hc g hg
  · exact validateBody_wellNested _ _ _ _ hv

theorem pq_throw_bind {α β : Type} {R : β → Prop} (e : PE) (k : α → PM β) :
    PQ (throw e >>= k) R := by
  intro s b pos c s' pos' hs h
  obtain ⟨_, _, _, h1, _⟩ := pm_bind_ok h
  cases h1

theorem pq_deser_bind {α β : Type} {R : β → Prop} (w : String) (k : α → PM β) :
    PQ (deser w >>= k) R := pq_throw_bind _ _

theorem pq_prepFail_bind {α β : Type} {R : β → Prop} (v w : String) (k : α → PM β) :
    PQ (prepFail v w >>= k) R := pq_throw_bind _ _

macro "pq_step" : tactic => `(tactic| with_reducible first
  | exact pq_throw_bind _ _ | exact pq_deser_bind _ _ | exact pq_prepFail_bind _ _ _
  | exact pq_pureT _ | exact pq_throw _ | exact pq_deser _ | exact pq_prepFail _ _
  | exact pq_liftP _ | exact pq_boundedP _ _ | exact pq_idxPM _ _ _ | exact pq_get
  | exact pq_getNat | exact pq_setNat _ | exact pq_read
  | exact pq_modify (fun _ h => h)
  | apply pq_forIn_arrayT | apply pq_forIn_rangeT | apply pq_forIn_listT
  | apply pq_getBind | apply pq_forIn_bind_WN | apply pq_bindT | (intro _) | split)

macro "pq_tac" : tactic => `(tactic| repeat' (first | pq_step | exact pq_constOk _ _ _ | (dsimp only) | exact allWN_empty |
  (intro _ _ _ _ _ _ hs h; cases h; apply And.intro; assumption;
    first | trivial | (apply allWN_push_of <;> assumption))))

set_option maxHeartbeats 3000000 in
theorem pq_sectionBody (cfg : NearCfg) (id sEnd : Nat) :
    PQ (sectionBody cfg id sEnd) (fun _ => True) := by
  unfold sectionBody
  pq_tac
  done


theorem iw_of_section {cfg : NearCfg} {id e : Nat} {s0 s' : PS} {sub : ByteArray} {st pos' : Nat}
    {u : Unit} (h : (((sectionBody cfg id e).run s0).run sub).run st = .ok ((u, s'), pos'))
    (h0 : IW s0) : IW s' :=
  (pq_sectionBody cfg id e s0 sub st u s' pos' h0 h).1

set_option maxHeartbeats 3000000 in
theorem pq_earlyPass (cfg : NearCfg) : PQ (earlyPass cfg) (fun _ => True) := by
  unfold earlyPass
  pq_tac
  all_goals (apply pq_set; apply iw_of_section <;> assumption)

theorem earlyPass_funcs (cfg : NearCfg) (code : ByteArray) {u : Unit} {s : PS} {pos : Nat}
    (h : ((StateT.run (earlyPass cfg) { funcBudget := cfg.maxFunctions, localBudget := cfg.maxLocals }).run code).run 0
      = .ok ((u, s), pos)) : ∀ f ∈ s.m.funcs.toList, WellNested f.code :=
  (pq_earlyPass cfg _ code 0 u s pos (by simp [IW]) h).1

@[simp] theorem fval_done {β : Type} (b : β) : fval (pure (ForInStep.done b) : Id (ForInStep β)) = b := rfl
@[simp] theorem fval_yield {β : Type} (b : β) : fval (pure (ForInStep.yield b) : Id (ForInStep β)) = b := rfl

theorem forIn_inv {α σ : Type} (P : σ → Prop) (body : α → σ → Id (ForInStep σ)) :
    ∀ (fs : List α), (∀ a ∈ fs, ∀ st, P st → P (fval (body a st))) →
    ∀ init, P init → P (forIn fs init body)
  | [], _, init, hi => hi
  | a :: l, h, init, hi => by
    rw [List.forIn_cons]
    have h1 := h a (List.mem_cons_self ..) init hi
    cases hb : body a init with
    | done b => rw [hb] at h1; exact h1
    | yield b =>
      rw [hb] at h1
      exact forIn_inv P body l (fun x hx => h x (List.mem_cons_of_mem _ hx)) b h1

def Good (cfg : NearCfg) (bl : Bool) (pf : PFunc) : Prop :=
  WellNested pf.code ∧ matchBlocks pf.code = (pf.endOf, pf.elseOf) ∧
    pf.gas = gasTable cfg.gas pf.code bl ∧ blockCount pf.code ≤ cfg.maxBlocksPerFunction

def P2 (st : Option PrepResult × Unit) : Prop := ∀ q, st.1 ≠ some (PrepResult.ok q)

theorem id_pure {α : Type} (a : α) : (pure a : Id α) = a := rfl

theorem idb {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl

def P1 (cfg : NearCfg) (bl : Bool) (st : Option PrepResult × Nat × Nat × Array PFunc) : Prop :=
  (∀ q, st.1 ≠ some (PrepResult.ok q)) ∧ ∀ pf ∈ st.2.2.2.toList, Good cfg bl pf

open Lean Elab Tactic Meta in
/-- Abstract the first `forIn` in hypothesis `h` as `F`, with `hF : forIn … = F`. -/
elab "gen_forIn " h:ident " => " x:ident hx:ident : tactic => withMainContext do
  let ldecl ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars ldecl.type
  let some e := ty.find? (fun e => e.isAppOf ``ForIn.forIn) | throwError "no forIn"
  let g ← getMainGoal
  let (_, _, g') ← g.generalizeHyp #[{ expr := e, xName? := x.getId, hName? := hx.getId }] #[ldecl.fvarId]
  replaceMainGoal [g']

theorem prepare_good (cfg : NearCfg) (code : ByteArray) (bl : Bool) (p : Prepared)
    (h : prepare cfg code bl = .ok p) :
    ∀ pf ∈ p.funcs.toList, Good cfg bl pf := by
  unfold prepare at h
  dsimp only at h
  split at h
  · cases h
  · cases h
  · cases h
  · rename_i s _ hep
    have HW := earlyPass_funcs cfg code hep
    simp only [Id.run] at h
    split at h
    · cases h
    simp only [idb] at h
    gen_forIn h => F hF
    rw [← Array.forIn_toList] at hF
    have key : P1 cfg bl F := by
      rw [← hF]
      refine forIn_inv (P1 cfg bl) _ _ ?_ _ ⟨fun q hq => (by cases hq), fun pf hpf => (by simp at hpf)⟩
      intro f hf st hst
      repeat' split
      all_goals (try exact ⟨fun q => by simp [fval, id_pure], fun pf hpf => hst.2 pf (by simpa [fval, id_pure] using hpf)⟩)
      refine ⟨fun q => by simp [fval, id_pure], fun pf hpf => ?_⟩
      simp only [fval, id_pure, Array.toList_push, List.mem_append, List.mem_singleton] at hpf
      rcases hpf with hpf | rfl
      · exact hst.2 pf hpf
      · refine ⟨HW f hf, rfl, rfl, ?_⟩
        rename_i hbm _
        rw [← Array.foldl_toList, foldl_add ow (fun a x => by cases x <;> rfl)] at hbm
        rw [blockCount_eq]; simpa using hbm
    split at h
    · rename_i r heq
      exact absurd (heq.trans (congrArg some h)) (key.1 p)
    split at h
    · cases h
    gen_forIn h => F_1 hF1
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hF1
    have key2 : P2 F_1 := by
      rw [← hF1]
      refine forIn_inv P2 _ _ ?_ _ (by simp [P2])
      intro k _ st _
      repeat' split
      all_goals simp [fval, P2, id_pure]
    split at h
    · rename_i r heq
      exact absurd (heq.trans (congrArg some h)) (key2 p)
    split at h
    · cases h
    gen_forIn h => F_2 hF2
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hF2
    have key3 : P2 F_2 := by
      rw [← hF2]
      refine forIn_inv P2 _ _ ?_ _ (by simp [P2])
      intro k _ st _
      repeat' split
      all_goals simp [fval, P2, id_pure]
    split at h
    · rename_i r heq
      exact absurd (heq.trans (congrArg some h)) (key3 p)
    cases h
    exact key.2


/-- (D) every prepared function is well nested, carries `matchBlocks`' tables and `gasTable`, and
respects `max_blocks_per_function`. -/
theorem prepare_funcs (cfg : NearCfg) (code : ByteArray) (bl : Bool) (p : Prepared)
    (h : prepare cfg code bl = .ok p) :
    ∀ (i : Nat) (pf : PFunc), p.funcs[i]? = some pf →
      WellNested pf.code ∧ matchBlocks pf.code = (pf.endOf, pf.elseOf) ∧
      pf.gas = gasTable cfg.gas pf.code bl ∧
      pf.code.foldl (fun a i => match i with
        | .block _ | .loop _ | .if_ _ => a + 1
        | _ => a) 0 ≤ cfg.maxBlocksPerFunction := by
  intro i pf hpf
  have hmem : pf ∈ p.funcs.toList := by
    rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hpf
  obtain ⟨h1, h2, h3, h4⟩ := prepare_good cfg code bl p h pf hmem
  refine ⟨h1, h2, h3, ?_⟩
  rw [blockCount_eq] at h4
  rw [← Array.foldl_toList, foldl_add ow (fun a x => by cases x <;> rfl)]
  simpa using h4

end FuelNest
end NearSpecV3.Wasm

/-
#print axioms NearSpecV3.Wasm.FuelNest.nestOK_of_wellNested
#print axioms NearSpecV3.Wasm.FuelNest.freeCount_le_of_wellNested
#print axioms NearSpecV3.Wasm.FuelNest.validateBody_wellNested
#print axioms NearSpecV3.Wasm.FuelNest.prepare_funcs
-/
#print axioms NearSpecV3.Wasm.FuelNest.nestOK_of_wellNested
#print axioms NearSpecV3.Wasm.FuelNest.freeCount_le_of_wellNested
#print axioms NearSpecV3.Wasm.FuelNest.validateBody_wellNested
#print axioms NearSpecV3.Wasm.FuelNest.prepare_funcs
