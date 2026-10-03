import ZkFormal.Potential

/-!
# ZkFormal.Product — multi-symbol events: the FRI query phase

The query phase of the STARK needs about 200 query positions of ~22 bits
each, i.e. far more randomness than one 256-bit oracle answer.  The
positions are therefore read from `k` oracle answers
`H(enc p j)`, `j < k`, where `p` is the (wide) transcript digest at the end
of the commit phase (DESIGN.md §5.3).  The adversary may ask these `k`
queries in any order, interleaved with anything else, for as many prefixes
`p` as it likes.

`product_step` is the potential for this situation.  If chunk `j` of prefix
`p` is "good for the adversary" for at most `g j` of the `2^256` answers,
whatever the oracle log `hist` at the moment it is asked (goodness may depend
on the oracles extracted from that log), then (with `prLE_of_potential`)
the probability that **some** prefix ends up with all `k` chunks answered
and good is at most
`q · ∏_j g_j / (2^256)^k`, where `q` counts only query-phase queries
(`qWeight`).  For FRI, chunk `j` encodes positions
`i_{j,1..m}` by disjoint bit slices, "good" means all of them fall in the
agreement set, and `∏_j g_j / 2^(256k) ≤ (1-θ)^s`.

The potential is `Φ(log) = ∑_{p touched} ∏_{j<k} f(p,j)` with
`f(p,j) = 2^256·[answer good]` if chunk `j` was answered and `g j` if not.
-/

namespace ZkFormal

open ArenaCore ArenaCore.Security

/-- Look up `x` in the log, returning its answer *and the log as it was
when `x` was first asked* (the entries older than it). -/
def lookupHist : Table → Bytes → Option (Bytes × Table)
  | [], _ => none
  | (x', y) :: tbl, x => if x = x' then some (y, tbl) else lookupHist tbl x

section
variable (k : Nat) (enc : Bytes → Nat → Bytes) (dec : Bytes → Option (Bytes × Nat))
  (Good : Table → Bytes → Nat → Bytes → Prop) (g : Nat → Nat)

/-- Contribution of chunk `j` of prefix `p` in log `tbl`.  Goodness of an
answered chunk is judged against the log *at the time it was answered*
(`Good hist p j y`), so that later queries cannot change it — this is where
the Merkle-extracted oracles enter. -/
noncomputable def chunkFactor (tbl : Table) (p : Bytes) (j : Nat) : Nat :=
  open Classical in
  match lookupHist tbl (enc p j) with
  | some (y, hist) => if Good hist p j y then roRange else 0
  | none => g j

/-- Contribution of prefix `p`: product over its `k` chunks. -/
noncomputable def prefixTerm (tbl : Table) (p : Bytes) : Nat :=
  ((List.range k).map (chunkFactor enc Good g tbl p)).prod

/-- Prefixes with at least one query-phase query in the log (no repeats). -/
def touched : Table → List Bytes
  | [] => []
  | (x, _) :: tbl =>
    match dec x with
    | some (p, _) => if p ∈ touched tbl then touched tbl else p :: touched tbl
    | none => touched tbl

/-- The query-phase potential. -/
noncomputable def queryPot (tbl : Table) : Nat :=
  ((touched dec tbl).map (prefixTerm k enc Good g tbl)).sum

/-- Weight: 1 for query-phase queries, 0 otherwise. -/
def qWeight (x : Bytes) : Nat := if (dec x).isSome then 1 else 0

/-- Success: some prefix has all `k` chunks answered with good answers. -/
def QuerySuccess (tbl : Table) : Prop :=
  ∃ p, ∀ j, j < k → ∃ y hist, lookupHist tbl (enc p j) = some (y, hist) ∧ Good hist p j y

end

/-! ## Lemmas -/

theorem lookup_cons (x y z : Bytes) (tbl : Table) :
    ((x, y) :: tbl).lookup z = if z = x then some y else tbl.lookup z := by
  by_cases h : z = x
  · subst h; simp [List.lookup]
  · have hb : (z == x) = false := by simp [h]
    simp only [List.lookup, hb, ite_eq_right h]

theorem lookup_some_mem {z y : Bytes} : ∀ {tbl : Table}, tbl.lookup z = some y → ∃ y', (z, y') ∈ tbl
  | [], h => by simp [List.lookup] at h
  | (x, v) :: tbl, h => by
    rw [lookup_cons] at h
    by_cases hz : z = x
    · subst hz; exact ⟨v, List.mem_cons_self⟩
    · rw [ite_eq_right hz] at h
      obtain ⟨y', hy'⟩ := lookup_some_mem h
      exact ⟨y', List.mem_cons_of_mem _ hy'⟩

theorem lookupHist_cons (x y z : Bytes) (tbl : Table) :
    lookupHist ((x, y) :: tbl) z = if z = x then some (y, tbl) else lookupHist tbl z := rfl

theorem lookupHist_none {x : Bytes} : ∀ {tbl : Table}, tbl.lookup x = none → lookupHist tbl x = none
  | [], _ => rfl
  | (x', y) :: tbl, h => by
    rw [lookup_cons] at h
    rw [lookupHist_cons]
    by_cases hx : x = x'
    · rw [ite_eq_left hx] at h; cases h
    · rw [ite_eq_right hx] at h ⊢; exact lookupHist_none h

theorem lookupHist_some_mem {z y : Bytes} {hist : Table} :
    ∀ {tbl : Table}, lookupHist tbl z = some (y, hist) → (z, y) ∈ tbl
  | [], h => by simp [lookupHist] at h
  | (x, v) :: tbl, h => by
    rw [lookupHist_cons] at h
    by_cases hz : z = x
    · rw [ite_eq_left hz] at h; cases h; subst hz; exact List.mem_cons_self
    · rw [ite_eq_right hz] at h; exact List.mem_cons_of_mem _ (lookupHist_some_mem h)

theorem mem_touched {dec : Bytes → Option (Bytes × Nat)} {p : Bytes} {j : Nat} :
    ∀ {tbl : Table} {x y : Bytes}, (x, y) ∈ tbl → dec x = some (p, j) → p ∈ touched dec tbl
  | [], _, _, h, _ => by simp at h
  | (x', y') :: tbl, x, y, h, hd => by
    simp only [touched]
    rcases List.mem_cons.mp h with h | h
    · cases h
      rw [hd]; simp only
      split
      · assumption
      · exact List.mem_cons_self
    · have ih := mem_touched h hd
      split
      · split <;> simp_all
      · exact ih

theorem sum_map_sum_comm {α β : Type} (l : List α) (m : List β) (f : α → β → Nat) :
    (l.map fun a => (m.map (f a)).sum).sum = (m.map fun b => (l.map fun a => f a b).sum).sum := by
  induction m with
  | nil => simp only [List.map_nil, List.sum_nil, Security.sum_map_const, Nat.mul_zero]
  | cons b m ih =>
    simp only [List.map_cons, List.sum_cons, sum_map_add, ih]

theorem sum_map_mul_left {α : Type} (l : List α) (f : α → Nat) (c : Nat) :
    (l.map fun a => c * f a).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

/-- Product over a duplicate-free index list in which only coordinate `j0`
depends on the random answer: the expectation contracts. -/
theorem prod_step (R : Nat) (P : Nat → Prop) (F : Nat → Nat) (Fv : Nat → Nat → Nat) (j0 : Nat)
    (hoff : ∀ v j, P j → j ≠ j0 → Fv v j = F j)
    (hon : ((List.range R).map fun v => Fv v j0).sum ≤ R * F j0) :
    ∀ (l : List Nat), l.Nodup → (∀ j ∈ l, P j) →
      ((List.range R).map fun v => (l.map (Fv v)).prod).sum ≤ R * (l.map F).prod := by
  intro l
  induction l with
  | nil => intro _ _; simp [Security.sum_map_const]
  | cons j l ih =>
    intro hnd hP
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.prod_cons]
    by_cases hj : j = j0
    · subst hj
      have hl : ∀ v, (l.map (Fv v)).prod = (l.map F).prod := by
        intro v; congr 1; apply List.map_congr_left
        intro i hi; exact hoff v i (hP i (List.mem_cons_of_mem _ hi)) (fun h => hnd.1 (h ▸ hi))
      simp only [hl, sum_map_mul_right]
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ hon
    · simp only [hoff _ _ (hP j List.mem_cons_self) hj, sum_map_mul_left]
      have := ih hnd.2 fun i hi => hP i (List.mem_cons_of_mem _ hi)
      rw [Nat.mul_left_comm]
      exact Nat.mul_le_mul_left _ this

theorem prod_replicate' (n a : Nat) : (List.replicate n a).prod = a ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.prod_cons, ih, Nat.pow_succ, Nat.mul_comm]

theorem le_sum_of_mem' {a : Nat} : ∀ {l : List Nat}, a ∈ l → a ≤ l.sum
  | [], h => by simp at h
  | b :: l, h => by
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (le_sum_of_mem' h) (Nat.le_add_left _ _)

theorem touched_cons_sub {dec : Bytes → Option (Bytes × Nat)} (x y : Bytes) (tbl : Table) :
    ∀ p ∈ touched dec ((x, y) :: tbl), p ∈ touched dec tbl ∨ ∃ j, dec x = some (p, j) := by
  intro p hp
  simp only [touched] at hp
  split at hp
  · rename_i p0 j0 hd
    split at hp
    · exact Or.inl hp
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact Or.inr ⟨j0, hd⟩
      · exact Or.inl hp
  · exact Or.inl hp

/-- **One-step bound for the query-phase potential.** -/
theorem product_step (k : Nat) (enc : Bytes → Nat → Bytes) (dec : Bytes → Option (Bytes × Nat))
    (hdec : ∀ p j, j < k → dec (enc p j) = some (p, j))
    (Good : Table → Bytes → Nat → Bytes → Prop) (g : Nat → Nat)
    (hg : ∀ hist p j, count (List.range roRange) (fun v => Good hist p j (LazyRO.answer v)) ≤ g j) :
    StepBound (queryPot k enc dec Good g) (qWeight dec) ((List.range k).map g).prod := by
  classical
  intro tbl x hx
  -- per-prefix contraction
  have hterm : ∀ p, ((List.range roRange).map fun v =>
      prefixTerm k enc Good g ((x, LazyRO.answer v) :: tbl) p).sum ≤
        roRange * prefixTerm k enc Good g tbl p := by
    intro p
    unfold prefixTerm
    by_cases hx' : ∃ j0, j0 < k ∧ x = enc p j0
    · obtain ⟨j0, hj0, rfl⟩ := hx'
      apply prod_step roRange (fun j => j < k) (chunkFactor enc Good g tbl p)
        (fun v => chunkFactor enc Good g ((enc p j0, LazyRO.answer v) :: tbl) p) j0
      · intro v j hjk hj
        unfold chunkFactor
        rw [lookupHist_cons, ite_eq_right]
        intro he
        have h1 := hdec p j0 hj0
        have h2 := hdec p j hjk
        rw [he, h1] at h2
        exact hj (by injection h2 with h; injection h with _ h; exact h.symm)
      · have e1 : chunkFactor enc Good g tbl p j0 = g j0 := by
          unfold chunkFactor; rw [lookupHist_none hx]
        have e2 : ∀ v, chunkFactor enc Good g ((enc p j0, LazyRO.answer v) :: tbl) p j0 =
            if Good tbl p j0 (LazyRO.answer v) then roRange else 0 := by
          intro v; unfold chunkFactor; rw [lookupHist_cons, ite_eq_left rfl]
        simp only [e2, e1, sum_map_ite]
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_left _ (hg tbl p j0)
      · exact List.nodup_range
      · intro j hj; exact List.mem_range.mp hj
    · -- `x` is not a chunk of `p`: the term does not depend on the answer
      have e : ∀ v, ((List.range k).map (chunkFactor enc Good g ((x, LazyRO.answer v) :: tbl) p)) =
          (List.range k).map (chunkFactor enc Good g tbl p) := by
        intro v
        apply List.map_congr_left
        intro j hj
        unfold chunkFactor
        rw [lookupHist_cons, ite_eq_right]
        intro he
        exact hx' ⟨j, List.mem_range.mp hj, he.symm⟩
      simp only [e, Security.sum_map_const, List.length_range]
      exact Nat.le_refl _
  -- the touched list after the query does not depend on the answer
  have ht : ∀ v, touched dec ((x, LazyRO.answer v) :: tbl) = touched dec ((x, []) :: tbl) := by
    intro v; simp only [touched]
  unfold queryPot
  simp only [ht]
  rw [← sum_map_sum_comm]
  -- bound each prefix term, then split the touched list
  have h1 : ((touched dec ((x, []) :: tbl)).map fun p => ((List.range roRange).map fun v =>
        prefixTerm k enc Good g ((x, LazyRO.answer v) :: tbl) p).sum).sum ≤
      ((touched dec ((x, []) :: tbl)).map fun p => roRange * prefixTerm k enc Good g tbl p).sum :=
    sum_map_le _ _ _ fun p _ => hterm p
  refine Nat.le_trans h1 ?_
  rw [sum_map_mul_left]
  apply Nat.mul_le_mul_left
  -- `touched` grows by at most the new prefix, whose term is `∏ g`
  simp only [touched]
  split
  · rename_i p0 j0 hd
    split
    · exact Nat.le_add_right _ _
    · simp only [List.map_cons, List.sum_cons, qWeight, hd, Option.isSome_some, ite_true, Nat.mul_one]
      rw [Nat.add_comm]
      apply Nat.add_le_add_left
      -- an untouched prefix has no answered chunk
      rename_i hnot
      unfold prefixTerm
      apply Nat.le_of_eq
      congr 1
      apply List.map_congr_left
      intro j _
      unfold chunkFactor
      cases hl : lookupHist tbl (enc p0 j) with
      | none => rfl
      | some yh =>
        exfalso
        obtain ⟨y, h⟩ := yh
        have hy' := lookupHist_some_mem hl
        have hj : j < k := List.mem_range.mp (by assumption)
        exact hnot (mem_touched hy' (hdec p0 j hj))
  · exact Nat.le_add_right _ _

/-- Success forces the query-phase potential to `(2^256)^k`. -/
theorem querySuccess_pot (k : Nat) (hk : 0 < k) (enc : Bytes → Nat → Bytes)
    (dec : Bytes → Option (Bytes × Nat)) (hdec : ∀ p j, j < k → dec (enc p j) = some (p, j))
    (Good : Table → Bytes → Nat → Bytes → Prop) (g : Nat → Nat) (tbl : Table)
    (hs : QuerySuccess k enc Good tbl) : roRange ^ k ≤ queryPot k enc dec Good g tbl := by
  classical
  obtain ⟨p, hp⟩ := hs
  have hterm : prefixTerm k enc Good g tbl p = roRange ^ k := by
    unfold prefixTerm
    have : ∀ j ∈ List.range k, chunkFactor enc Good g tbl p j = roRange := by
      intro j hj
      obtain ⟨y, hist, hy, hgood⟩ := hp j (List.mem_range.mp hj)
      unfold chunkFactor; rw [hy]; simp only [hgood, ite_true]
    rw [List.map_congr_left this, List.map_const', List.length_range, prod_replicate']
  have hmem : p ∈ touched dec tbl := by
    obtain ⟨y, hist, hy, _⟩ := hp 0 hk
    exact mem_touched (lookupHist_some_mem hy) (hdec p 0 hk)
  unfold queryPot
  rw [← hterm]
  exact le_sum_of_mem' (List.mem_map.mpr ⟨p, hmem, rfl⟩)

/-- **Query-phase bound.**  Any computation making at most `q` query-phase
queries (any number of other queries) completes some prefix with `k` good
chunks with probability at most `q · ∏_j g_j / (2^256)^k`. -/
theorem query_phase_bound (k : Nat) (hk : 0 < k) (enc : Bytes → Nat → Bytes)
    (dec : Bytes → Option (Bytes × Nat)) (hdec : ∀ p j, j < k → dec (enc p j) = some (p, j))
    (Good : Table → Bytes → Nat → Bytes → Prop) (g : Nat → Nat)
    (hg : ∀ hist p j, count (List.range roRange) (fun v => Good hist p j (LazyRO.answer v)) ≤ g j)
    {α : Type} (A : OracleComp hashSpec α) (q : Nat) (hA : OracleComp.QueryBound (qWeight dec) A q)
    (n : Nat) :
    PrLE n roRange (fun t => QuerySuccess k enc Good (finalTable A (LazyRO.init t)))
      (((List.range k).map g).prod * q) (roRange ^ k) := by
  have h := prLE_of_potential (product_step k enc dec hdec Good g hg) hA n [] false
    (fun t => QuerySuccess k enc Good (finalTable A (LazyRO.init t))) (roRange ^ k)
    (Nat.pow_pos (by rw [ArenaCore.Security.roRange_eq]; exact Nat.pow_pos (by decide)))
    (fun t _ hs => querySuccess_pot k hk enc dec hdec Good g _ hs)
  have e : queryPot k enc dec Good g [] = 0 := rfl
  rw [e, Nat.zero_add] at h
  exact h

end ZkFormal
