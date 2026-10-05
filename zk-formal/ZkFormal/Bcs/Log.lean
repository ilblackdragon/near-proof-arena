import ZkFormal.Potential
import ZkFormal.BadQuery
import ZkFormal.Product

/-!
# ZkFormal.Bcs.Log — oracle logs as data

Deterministic facts about the lazy random oracle's query log (`LazyRO.table`,
most recent entry first) that the BCS extraction argument (DESIGN.md §6.3)
needs:

* `TableWF`: keys are distinct and every answer is 32 bytes.  Every log
  produced by `LazyRO` from an empty (or well-formed) log is well formed
  (`simulate_wf`).
* `evalT`: evaluating a hash-query tree *purely* against a log.  If a run
  did not overflow, the tree evaluates against its own final log to the
  same result (`simulate_evalT`).  This turns "the verifier accepted in the
  ROM game" into a statement about the final log alone.
* Entries with their histories: `tbl = pre ++ (x, y) :: hist` (`hist` is the
  log as it was when `x` was answered), `BadHist` on such splits, and
  `lookupHist` ↔ splits.
-/

set_option linter.unusedSimpArgs false

namespace ZkFormal.Bcs

open ArenaCore ArenaCore.Security ZkFormal

/-! ## Lookups -/

theorem lookup_append (l₁ l₂ : Table) (z : Bytes) :
    (l₁ ++ l₂).lookup z = ((l₁.lookup z).or (l₂.lookup z)) := List.lookup_append

theorem lookup_none_of_not_mem {z : Bytes} : ∀ {l : Table}, z ∉ l.map Prod.fst → l.lookup z = none
  | [], _ => rfl
  | (x, y) :: l, h => by
    rw [lookup_cons]
    have hz : z ≠ x := fun e => h (by simp [e])
    rw [ite_eq_right hz]
    exact lookup_none_of_not_mem (fun hm => h (List.mem_cons_of_mem _ hm))

theorem mem_keys_of_lookup {z y : Bytes} {l : Table} (h : l.lookup z = some y) : z ∈ l.map Prod.fst := by
  obtain ⟨y', hy'⟩ := lookup_some_mem h
  exact List.mem_map.mpr ⟨(z, y'), hy', rfl⟩

theorem lookup_of_mem_keys {z : Bytes} : ∀ {l : Table}, z ∈ l.map Prod.fst → ∃ y, l.lookup z = some y
  | [], h => by simp at h
  | (x, y) :: l, h => by
    rw [lookup_cons]
    by_cases hz : z = x
    · exact ⟨y, by rw [ite_eq_left hz]⟩
    · rw [ite_eq_right hz]
      rcases List.mem_cons.mp h with h | h
      · exact absurd h hz
      · exact lookup_of_mem_keys h

/-- Lookups in a suffix agree with lookups in the whole log, if keys are distinct. -/
theorem lookup_suffix {pre hist : Table} (hnd : ((pre ++ hist).map Prod.fst).Nodup) {z y : Bytes}
    (h : hist.lookup z = some y) : (pre ++ hist).lookup z = some y := by
  rw [lookup_append]
  have hz : z ∉ pre.map Prod.fst := by
    intro hm
    rw [List.map_append, List.nodup_append] at hnd
    exact hnd.2.2 z hm z (mem_keys_of_lookup h) rfl
  rw [lookup_none_of_not_mem hz]
  simpa using h

theorem lookup_suffix' {pre hist : Table} (hnd : ((pre ++ hist).map Prod.fst).Nodup) {z y : Bytes}
    (h : (pre ++ hist).lookup z = some y) (hz : z ∈ hist.map Prod.fst) : hist.lookup z = some y := by
  obtain ⟨y', hy'⟩ := lookup_of_mem_keys hz
  rw [lookup_suffix hnd hy'] at h
  rw [hy', h]

/-! ## Well-formed logs -/

/-- A well-formed log: distinct keys, 32-byte answers. -/
def TableWF (tbl : Table) : Prop :=
  (tbl.map Prod.fst).Nodup ∧ ∀ e ∈ tbl, e.2.length = 32

theorem TableWF.nil : TableWF [] := ⟨List.nodup_nil, by simp⟩

theorem TableWF.suffix {pre hist : Table} (h : TableWF (pre ++ hist)) : TableWF hist := by
  refine ⟨?_, fun e he => h.2 e (List.mem_append_right _ he)⟩
  have := h.1
  rw [List.map_append, List.nodup_append] at this
  exact this.2.1

theorem TableWF.lookup_length {tbl : Table} (h : TableWF tbl) {z y : Bytes} (hz : tbl.lookup z = some y) :
    y.length = 32 := by
  obtain ⟨e, he, rfl⟩ := ArenaCore.Security.lookup_mem hz
  exact h.2 e he

theorem answer_length (t : Nat) : (LazyRO.answer t).length = 32 := Bytes.beN_length 32 t

theorem query_wf (s : LazyRO) (x : Bytes) (h : TableWF s.table) :
    TableWF (LazyRO.query s x).2.table := by
  unfold LazyRO.query
  cases hl : s.table.lookup x with
  | some y => simpa [hl] using h
  | none =>
    cases ht : s.tape with
    | nil => simpa [hl, ht] using h
    | cons t ts =>
      simp only [hl, ht]
      refine ⟨?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨fun hm => ?_, h.1⟩
        obtain ⟨y, hy⟩ := lookup_of_mem_keys hm
        rw [hl] at hy; cases hy
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact answer_length t
        · exact h.2 e he

theorem simulate_wf {α : Type} (A : OracleComp hashSpec α) :
    ∀ (s : LazyRO), TableWF s.table → TableWF (OracleComp.simulate hashImpl A s).2.table := by
  induction A with
  | pure a => intro s h; exact h
  | query x k ih =>
    intro s h
    simp only [OracleComp.simulate, hashImpl]
    exact ih _ _ (query_wf s x h)

/-! ## Log growth -/

/-- A query only prepends to the log. -/
theorem query_ext (s : LazyRO) (x : Bytes) : ∃ pre, (LazyRO.query s x).2.table = pre ++ s.table := by
  unfold LazyRO.query
  cases hl : s.table.lookup x with
  | some y => exact ⟨[], by simp [hl]⟩
  | none =>
    cases ht : s.tape with
    | nil => exact ⟨[], by simp [hl, ht]⟩
    | cons t ts => exact ⟨[(x, LazyRO.answer t)], by simp [hl, ht]⟩

theorem simulate_ext {α : Type} (A : OracleComp hashSpec α) :
    ∀ (s : LazyRO), ∃ pre, (OracleComp.simulate hashImpl A s).2.table = pre ++ s.table := by
  induction A with
  | pure a => intro s; exact ⟨[], rfl⟩
  | query x k ih =>
    intro s
    simp only [OracleComp.simulate]
    obtain ⟨p1, h1⟩ := query_ext s x
    obtain ⟨p2, h2⟩ := ih (LazyRO.query s x).1 (LazyRO.query s x).2
    exact ⟨p2 ++ p1, by simp only [hashImpl]; rw [h2, h1, List.append_assoc]⟩

/-- Recorded answers never change. -/
theorem query_lookup_stable (s : LazyRO) (x z y : Bytes) (h : s.table.lookup z = some y) :
    (LazyRO.query s x).2.table.lookup z = some y := by
  unfold LazyRO.query
  cases hl : s.table.lookup x with
  | some y' => simpa [hl] using h
  | none =>
    cases ht : s.tape with
    | nil => simpa [hl, ht] using h
    | cons t ts =>
      simp only [hl, ht]
      rw [lookup_cons, ite_eq_right]
      · exact h
      · intro e; subst e; rw [hl] at h; cases h

theorem simulate_lookup_stable {α : Type} (A : OracleComp hashSpec α) :
    ∀ (s : LazyRO) (z y : Bytes), s.table.lookup z = some y →
      (OracleComp.simulate hashImpl A s).2.table.lookup z = some y := by
  induction A with
  | pure a => intro s z y h; exact h
  | query x k ih =>
    intro s z y h
    simp only [OracleComp.simulate, hashImpl]
    exact ih _ _ z y (query_lookup_stable s x z y h)

/-- Without overflow, the answer to a query is recorded in the log. -/
theorem query_recorded (s : LazyRO) (x : Bytes) (h : (LazyRO.query s x).2.overflow = false) :
    (LazyRO.query s x).2.table.lookup x = some (LazyRO.query s x).1 := by
  unfold LazyRO.query at h ⊢
  cases hl : s.table.lookup x with
  | some y => simp [hl]
  | none =>
    cases ht : s.tape with
    | nil => simp [hl, ht] at h
    | cons t ts => simp [hl, ht, lookup_cons]

/-! ## Pure evaluation against a log -/

/-- Evaluate a hash-query tree against a fixed log; `none` if it asks an
unrecorded query. -/
def evalT {α : Type} (tbl : Table) : OracleComp hashSpec α → Option α
  | .pure a => some a
  | .query x k =>
    match tbl.lookup x with
    | some y => evalT tbl (k y)
    | none => none

/-- **A run without overflow is a pure evaluation against its final log.** -/
theorem simulate_evalT {α : Type} (A : OracleComp hashSpec α) :
    ∀ (s : LazyRO), (OracleComp.simulate hashImpl A s).2.overflow = false →
      evalT (OracleComp.simulate hashImpl A s).2.table A = some (OracleComp.simulate hashImpl A s).1 := by
  induction A with
  | pure a => intro s _; rfl
  | query x k ih =>
    intro s hov
    simp only [OracleComp.simulate] at hov ⊢
    have hov1 : (LazyRO.query s x).2.overflow = false := by
      cases h1 : (LazyRO.query s x).2.overflow with
      | false => rfl
      | true =>
        have := simulate_overflow_mono (k (LazyRO.query s x).1) _ h1
        simp only [hashImpl] at hov
        rw [this] at hov; cases hov
    have hrec := simulate_lookup_stable (k (LazyRO.query s x).1) (LazyRO.query s x).2 x _
      (query_recorded s x hov1)
    simp only [hashImpl] at hrec ⊢
    simp only [evalT, hrec]
    exact ih _ _ hov

theorem evalT_bind {α β : Type} (tbl : Table) (oa : OracleComp hashSpec α)
    (f : α → OracleComp hashSpec β) :
    evalT tbl (OracleComp.bind oa f) = (evalT tbl oa).bind fun a => evalT tbl (f a) := by
  induction oa with
  | pure a => rfl
  | query x k ih =>
    simp only [OracleComp.bind, evalT]
    cases tbl.lookup x with
    | some y => exact ih y
    | none => rfl

/-! ## Entries and their histories -/

theorem badHist_of_split (Bad : Table → Bytes → Bytes → Prop) :
    ∀ (pre : Table) {x y : Bytes} {hist : Table}, Bad hist x y → BadHist Bad (pre ++ (x, y) :: hist)
  | [], _, _, _, h => Or.inl h
  | (_, _) :: pre, _, _, _, h => Or.inr (badHist_of_split Bad pre h)

theorem split_of_badHist (Bad : Table → Bytes → Bytes → Prop) :
    ∀ (tbl : Table), BadHist Bad tbl → ∃ pre x y hist, tbl = pre ++ (x, y) :: hist ∧ Bad hist x y
  | [], h => h.elim
  | (x, y) :: tbl, h => by
    rcases h with h | h
    · exact ⟨[], x, y, tbl, rfl, h⟩
    · obtain ⟨pre, x', y', hist, e, hb⟩ := split_of_badHist Bad tbl h
      exact ⟨(x, y) :: pre, x', y', hist, by rw [e]; rfl, hb⟩

theorem split_of_lookupHist {z y : Bytes} {hist : Table} :
    ∀ {tbl : Table}, lookupHist tbl z = some (y, hist) → ∃ pre, tbl = pre ++ (z, y) :: hist
  | [], h => by simp [lookupHist] at h
  | (x, v) :: tbl, h => by
    rw [lookupHist_cons] at h
    by_cases hz : z = x
    · rw [ite_eq_left hz] at h; cases h; subst hz; exact ⟨[], rfl⟩
    · rw [ite_eq_right hz] at h
      obtain ⟨pre, e⟩ := split_of_lookupHist h
      exact ⟨(x, v) :: pre, by rw [e]; rfl⟩

theorem lookupHist_of_split {z y : Bytes} {hist : Table} :
    ∀ (pre : Table), z ∉ pre.map Prod.fst → lookupHist (pre ++ (z, y) :: hist) z = some (y, hist)
  | [], _ => by simp [lookupHist]
  | (x, v) :: pre, h => by
    show lookupHist ((x, v) :: (pre ++ (z, y) :: hist)) z = _
    rw [lookupHist_cons]
    have hz : z ≠ x := fun e => h (by simp [e])
    rw [ite_eq_right hz]
    exact lookupHist_of_split pre (fun hm => h (List.mem_cons_of_mem _ hm))

/-- Every recorded query has a history. -/
theorem lookupHist_of_lookup {z y : Bytes} : ∀ {tbl : Table}, tbl.lookup z = some y →
    ∃ hist, lookupHist tbl z = some (y, hist)
  | [], h => by simp [List.lookup] at h
  | (x, v) :: tbl, h => by
    rw [lookup_cons] at h
    rw [lookupHist_cons]
    by_cases hz : z = x
    · rw [ite_eq_left hz] at h ⊢; cases h; exact ⟨tbl, rfl⟩
    · rw [ite_eq_right hz] at h ⊢; exact lookupHist_of_lookup h

theorem lookupHist_length {z y : Bytes} {hist tbl : Table} (h : lookupHist tbl z = some (y, hist)) :
    hist.length < tbl.length := by
  obtain ⟨pre, rfl⟩ := split_of_lookupHist h
  simp; omega

theorem nodup_split_not_mem {pre : Table} {z y : Bytes} {hist : Table}
    (hnd : ((pre ++ (z, y) :: hist).map Prod.fst).Nodup) : z ∉ pre.map Prod.fst := by
  intro hm
  rw [List.map_append, List.nodup_append] at hnd
  exact hnd.2.2 z hm z (by simp) rfl

theorem nodup_split_not_mem' {pre : Table} {z y : Bytes} {hist : Table}
    (hnd : ((pre ++ (z, y) :: hist).map Prod.fst).Nodup) : z ∉ hist.map Prod.fst := by
  intro hm
  rw [List.map_append, List.nodup_append] at hnd
  have := hnd.2.1
  simp only [List.map_cons, List.nodup_cons] at this
  exact this.1 hm

/-- The recorded answer at a split. -/
theorem lookup_split {pre : Table} {z y : Bytes} {hist : Table}
    (hnd : ((pre ++ (z, y) :: hist).map Prod.fst).Nodup) : (pre ++ (z, y) :: hist).lookup z = some y := by
  rw [lookup_append, lookup_none_of_not_mem (nodup_split_not_mem hnd)]
  simp [lookup_cons]

end ZkFormal.Bcs
