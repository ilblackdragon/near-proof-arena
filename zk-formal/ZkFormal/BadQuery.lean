import ZkFormal.Potential

/-!
# ZkFormal.BadQuery — adaptive, history-dependent bad-answer bound

The single-symbol instance of the potential lemma, and the shape in which
every *commit-phase* round of the STARK is used (DESIGN.md §6.3): a fresh
query `x`, asked when the oracle log is `tbl`, is *bad* if its answer `y`
satisfies `Bad tbl x y` — e.g. "`x` is the Fiat–Shamir query of a doomed
transcript prefix (whose committed oracles are extracted from `tbl`) and the
challenge decoded from `y` un-dooms it".  If for every `tbl, x` at most
`B · w x` of the `2^256` answers are bad, then a `w`-budget-`q` computation
produces a bad answer with probability at most `B·q / 2^256`.

This strictly generalises `ArenaCore.Security.rom_guess_bound` (a fixed
target, i.e. `Bad tbl x y := y = target`), which is re-derived below as a
check that nothing was lost.
-/

namespace ZkFormal

open ArenaCore ArenaCore.Security

/-- Some entry of the log was bad *with respect to the log before it*. -/
def BadHist (Bad : Table → Bytes → Bytes → Prop) : Table → Prop
  | [] => False
  | (x, y) :: tbl => Bad tbl x y ∨ BadHist Bad tbl

/-- Potential: `2^256` once a bad answer has occurred, `0` before. -/
noncomputable def badPot (Bad : Table → Bytes → Bytes → Prop) (tbl : Table) : Nat :=
  open Classical in if BadHist Bad tbl then roRange else 0

theorem badPot_step (Bad : Table → Bytes → Bytes → Prop) (w : Bytes → Nat) (B : Nat)
    (hB : ∀ tbl x, count (List.range roRange) (fun v => Bad tbl x (LazyRO.answer v)) ≤ B * w x) :
    StepBound (badPot Bad) w B := by
  classical
  intro tbl x _
  by_cases h : BadHist Bad tbl
  · have e : (List.range roRange).map (fun v => badPot Bad ((x, LazyRO.answer v) :: tbl)) =
        (List.range roRange).map (fun _ => roRange) :=
      List.map_congr_left fun v _ => by
        unfold badPot; rw [ite_eq_left (show BadHist Bad ((x, LazyRO.answer v) :: tbl) from Or.inr h)]
    have e2 : badPot Bad tbl = roRange := by unfold badPot; rw [ite_eq_left h]
    rw [e, Security.sum_map_const, List.length_range, e2]
    generalize roRange = R
    exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  · have e : (List.range roRange).map (fun v => badPot Bad ((x, LazyRO.answer v) :: tbl)) =
        (List.range roRange).map (fun v => if Bad tbl x (LazyRO.answer v) then roRange else 0) :=
      List.map_congr_left fun v _ => by
        unfold badPot
        by_cases hv : Bad tbl x (LazyRO.answer v)
        · rw [ite_eq_left (show BadHist Bad ((x, LazyRO.answer v) :: tbl) from Or.inl hv), ite_eq_left hv]
        · rw [ite_eq_right (show ¬ BadHist Bad ((x, LazyRO.answer v) :: tbl) from fun h' => h'.elim hv h),
            ite_eq_right hv]
    have e2 : badPot Bad tbl = 0 := by unfold badPot; rw [ite_eq_right h]
    rw [e, sum_map_ite, e2, Nat.zero_add]
    have := hB tbl x
    generalize roRange = R at this ⊢
    rw [Nat.mul_comm R (B * w x)]
    exact Nat.mul_le_mul_right _ this

/-- **Adaptive bad-answer bound.**  With a tape of any length `n`, a
computation of `w`-weighted budget `q` records a bad answer with probability
at most `B·q / 2^256`. -/
theorem bad_query_bound (Bad : Table → Bytes → Bytes → Prop) (w : Bytes → Nat) (B : Nat)
    (hB : ∀ tbl x, count (List.range roRange) (fun v => Bad tbl x (LazyRO.answer v)) ≤ B * w x)
    {α : Type} (A : OracleComp hashSpec α) (q : Nat) (hA : OracleComp.QueryBound w A q) (n : Nat) :
    PrLE n roRange (fun t => BadHist Bad (finalTable A (LazyRO.init t))) (B * q) roRange := by
  classical
  have h := prLE_of_potential (badPot_step Bad w B hB) hA n [] false
    (fun t => BadHist Bad (finalTable A (LazyRO.init t))) roRange
    (by rw [ArenaCore.Security.roRange_eq]; exact Nat.pow_pos (by decide))
    (fun t _ hbad => by
      show roRange ≤ badPot Bad (finalTable A (LazyRO.init t))
      unfold badPot; rw [ite_eq_left hbad]; exact Nat.le_refl _)
  have e : badPot Bad [] = 0 := by unfold badPot; rw [ite_eq_right (by simp [BadHist])]
  rw [e, Nat.zero_add] at h
  exact h

/-! ## Sanity: `rom_guess_bound` is the fixed-target instance -/

theorem badHist_of_mem (Bad : Table → Bytes → Bytes → Prop) (target : Bytes)
    (hBad : ∀ tbl x y, y = target → Bad tbl x y) :
    ∀ (tbl : Table) (x : Bytes), (x, target) ∈ tbl → BadHist Bad tbl
  | [], _, h => by simp at h
  | (x', y') :: tbl, x, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h; exact Or.inl (hBad _ _ _ rfl)
    · exact Or.inr (badHist_of_mem Bad target hBad tbl x h)

theorem lookup_mem_pair {x y : Bytes} : ∀ {l : Table}, l.lookup x = some y → (x, y) ∈ l
  | [], h => by simp [List.lookup] at h
  | (k, v) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      have : x = k := by simpa using hk
      subst this; cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem_pair h)

theorem simulate_table_mono {α : Type} (A : OracleComp hashSpec α) :
    ∀ (s : LazyRO) (e : Bytes × Bytes), e ∈ s.table → e ∈ (OracleComp.simulate hashImpl A s).2.table := by
  induction A with
  | pure a => intro s e h; exact h
  | query x k ih =>
    intro s e h
    simp only [OracleComp.simulate]
    apply ih
    unfold hashImpl LazyRO.query
    cases hl : s.table.lookup x with
    | some y => simpa [hl] using h
    | none =>
      cases ht : s.tape with
      | nil => simpa [hl, ht] using h
      | cons t ts => simp [h]

theorem simulate_overflow_mono {α : Type} (A : OracleComp hashSpec α) :
    ∀ (s : LazyRO), s.overflow = true → (OracleComp.simulate hashImpl A s).2.overflow = true := by
  induction A with
  | pure a => intro s h; exact h
  | query x k ih =>
    intro s h
    simp only [OracleComp.simulate]
    apply ih
    unfold hashImpl LazyRO.query
    cases hl : s.table.lookup x with
    | some y => simpa [hl] using h
    | none =>
      cases ht : s.tape with
      | nil => simp
      | cons t ts => simpa [hl, ht] using h

theorem simulate_bind {spec : OracleSpec} {τ α β : Type} (impl : (q : spec.Query) → τ → spec.Resp q × τ)
    (oa : OracleComp spec α) (f : α → OracleComp spec β) (s : τ) :
    OracleComp.simulate impl (OracleComp.bind oa f) s =
      OracleComp.simulate impl (f (OracleComp.simulate impl oa s).1) (OracleComp.simulate impl oa s).2 := by
  induction oa generalizing s with
  | pure a => rfl
  | query q k ih => simp only [OracleComp.bind, OracleComp.simulate]; exact ih _ _

/-- Re-derivation of the preimage-guessing bound from `bad_query_bound`
(one extra query for the final evaluation; overflow excluded by the tape
length).  Same bound as `ArenaCore.Security.rom_guess_bound`. -/
theorem rom_guess_bound' (A : OracleComp hashSpec Bytes) (q : Nat)
    (hA : OracleComp.QueryBound unitWeight A q) (target : Bytes) :
    PrLE (q + 1) roRange (guessWins A target) (q + 1) roRange := by
  classical
  let A' : OracleComp hashSpec Bytes := OracleComp.bind A fun out => OracleComp.ask out
  have hA' : OracleComp.QueryBound unitWeight A' (q + 1) := by
    have key : ∀ {B : OracleComp hashSpec Bytes} {m : Nat}, OracleComp.QueryBound unitWeight B m →
        OracleComp.QueryBound unitWeight (OracleComp.bind B fun out => OracleComp.ask out) (m + 1) := by
      intro B m hB
      induction hB with
      | pure a m =>
        show OracleComp.QueryBound unitWeight (OracleComp.query (spec := hashSpec) a OracleComp.pure) (m + 1)
        exact OracleComp.QueryBound.query (spec := hashSpec) a _ (m + 1)
          (by show 1 ≤ m + 1; omega) fun _ => .pure _ _
      | query x k m hw _ ih =>
        show OracleComp.QueryBound unitWeight
          (OracleComp.query x fun r => OracleComp.bind (k r) fun out => OracleComp.ask out) (m + 1)
        refine OracleComp.QueryBound.query (spec := hashSpec) x _ (m + 1)
          (by show 1 ≤ m + 1; omega) fun r => ?_
        have := ih r
        simp only [unitWeight] at hw this ⊢
        have e : m + 1 - 1 = m - 1 + 1 := by omega
        rw [e]; exact this
    exact key hA
  have hb := bad_query_bound (fun _ _ y => y = target) unitWeight 1
    (fun tbl x => by simpa [unitWeight] using answer_count_le_one target) A' (q + 1) hA' (q + 1)
  rw [Nat.one_mul] at hb
  refine ⟨hb.1, Nat.le_trans (Nat.mul_le_mul_right _ (count_mono_mem _ fun t ht hw => ?_)) hb.2⟩
  -- guessWins ⇒ the target was recorded in the final log of `A'`
  have hlen := mem_allTapes_length ht
  obtain ⟨k, hk, hinv⟩ := LazyInv.simulate hA (LazyInv.init t) (by omega)
  have e : finalTable A' (LazyRO.init t) =
      (LazyRO.query (OracleComp.simulate hashImpl A (LazyRO.init t)).2
        (OracleComp.simulate hashImpl A (LazyRO.init t)).1).2.table := by
    simp only [finalTable, A', simulate_bind, OracleComp.ask, OracleComp.simulate, hashImpl]
  show BadHist _ (finalTable A' (LazyRO.init t))
  rw [e]
  unfold guessWins at hw
  generalize OracleComp.simulate hashImpl A (LazyRO.init t) = r at hw hinv
  obtain ⟨out, s1⟩ := r
  simp only at hw hinv ⊢
  apply badHist_of_mem _ target (fun _ _ _ h => h) _ out
  unfold LazyRO.query at hw ⊢
  cases hl : s1.table.lookup out with
  | some y =>
    simp only [hl] at hw ⊢
    exact hw ▸ lookup_mem_pair hl
  | none =>
    have hkl : k < t.length := by omega
    have hd : s1.tape = t[k]'hkl :: t.drop (k + 1) := by
      rw [hinv.1]; exact List.drop_eq_getElem_cons hkl
    simp only [hl, hd] at hw ⊢
    rw [← hw]; exact List.mem_cons_self

end ZkFormal
