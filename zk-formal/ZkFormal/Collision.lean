import ZkFormal.Product
import ZkFormal.BadQuery

/-!
# ZkFormal.Collision — binding of wide (multi-call) digests

With `2^64` adversary queries plus the honest prover's Merkle hashing
(`2^40` proofs × up to `2^29` oracle calls each), the oracle log can reach
`2^70` entries, and a 256-bit collision then has probability about `2^-117`:
plain 32-byte digests cannot meet the 128-bit target (DESIGN.md §5.2).
Commitments and the transcript state therefore use *wide* digests
`WH(m) = H(enc m 0) ‖ … ‖ H(enc m (k-1))` (`k = 2`: 512 bits).

A collision of wide digests is a *pair* event spread over `2k` oracle
answers asked in any order.  `pairPot` is its potential: for each ordered
pair `(m, m')` of distinct touched keys, the product over `j < k` of
`2^256·[answers equal]` once both `enc m j` and `enc m' j` are answered,
and `1` before.  `collision_bound` gives

  `Pr[∃ m ≠ m', WH(m) = WH(m')] ≤ 2·N·q / (2^256)^k`

for a computation with `q` queries and a log of at most `N` entries
(`q ≤ N`; with `k = 2` and `N = 2^70` this is below `2^-371`).
-/

namespace ZkFormal

open ArenaCore ArenaCore.Security

section
variable (k : Nat) (enc : Bytes → Nat → Bytes) (dec : Bytes → Option (Bytes × Nat))

/-- Pair factor for chunk `j`. -/
noncomputable def pairFactor (tbl : Table) (m m' : Bytes) (j : Nat) : Nat :=
  open Classical in
  match tbl.lookup (enc m j), tbl.lookup (enc m' j) with
  | some a, some b => if a = b then roRange else 0
  | _, _ => 1

noncomputable def pairTerm (tbl : Table) (m m' : Bytes) : Nat :=
  ((List.range k).map (pairFactor enc tbl m m')).prod

/-- Sum over ordered pairs of distinct keys in a list. -/
noncomputable def pairSum (L : List Bytes) (f : Bytes → Bytes → Nat) : Nat :=
  open Classical in
  (L.map fun m => (L.map fun m' => if m = m' then 0 else f m m').sum).sum

/-- The oldest `N` entries of a log (the log is most-recent-first). -/
def oldest (N : Nat) (tbl : Table) : Table := tbl.drop (tbl.length - N)

/-- Collision potential, frozen once the log exceeds `N` entries. -/
noncomputable def pairPot (N : Nat) (tbl : Table) : Nat :=
  pairSum (touched dec (oldest N tbl)) (pairTerm k enc (oldest N tbl))

/-- Two distinct keys with all `k` chunks answered identically. -/
def WideCollision (tbl : Table) : Prop :=
  ∃ m m', m ≠ m' ∧ ∀ j, j < k → ∃ a, tbl.lookup (enc m j) = some a ∧ tbl.lookup (enc m' j) = some a

end

/-! ## Lemmas -/

theorem oldest_cons_of_lt {N : Nat} {tbl : Table} (h : tbl.length < N) (e : Bytes × Bytes) :
    oldest N (e :: tbl) = e :: tbl := by
  unfold oldest
  rw [List.length_cons, Nat.sub_eq_zero_of_le (by omega), List.drop_zero]

theorem oldest_cons_of_ge {N : Nat} {tbl : Table} (h : N ≤ tbl.length) (e : Bytes × Bytes) :
    oldest N (e :: tbl) = oldest N tbl := by
  unfold oldest
  rw [List.length_cons, show tbl.length + 1 - N = (tbl.length - N) + 1 by omega, List.drop_succ_cons]

theorem oldest_of_le {N : Nat} {tbl : Table} (h : tbl.length ≤ N) : oldest N tbl = tbl := by
  unfold oldest; rw [Nat.sub_eq_zero_of_le h, List.drop_zero]

theorem touched_length_le (dec : Bytes → Option (Bytes × Nat)) :
    ∀ tbl : Table, (touched dec tbl).length ≤ tbl.length
  | [] => Nat.le_refl _
  | (x, _) :: tbl => by
    have ih := touched_length_le dec tbl
    simp only [touched, List.length_cons]
    split
    · split
      · omega
      · simp only [List.length_cons]; omega
    · omega

theorem touched_nodup (dec : Bytes → Option (Bytes × Nat)) : ∀ tbl : Table, (touched dec tbl).Nodup
  | [] => List.nodup_nil
  | (x, _) :: tbl => by
    simp only [touched]
    split
    · split
      · exact touched_nodup dec tbl
      · rename_i h
        exact List.nodup_cons.mpr ⟨h, touched_nodup dec tbl⟩
    · exact touched_nodup dec tbl

theorem pairSum_le (L : List Bytes) (f g : Bytes → Bytes → Nat)
    (h : ∀ m m', m ≠ m' → f m m' ≤ g m m') : pairSum L f ≤ pairSum L g := by
  classical
  unfold pairSum
  apply sum_map_le; intro m _
  apply sum_map_le; intro m' _
  by_cases hm : m = m'
  · simp [hm]
  · simp only [hm, ite_false]; exact h m m' hm

/-- `sum_map_ite` for any decidability instance. -/
theorem sum_map_ite' {α : Type} (l : List α) (P : α → Prop) [DecidablePred P] (c : Nat) :
    (l.map fun a => if P a then c else 0).sum = count l P * c := by
  classical
  induction l with
  | nil => simp [count]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, count_cons]
    by_cases hP : P a <;> simp [hP, Nat.add_mul, Nat.add_comm]

/-- Expectation commutes with the pair sum. -/
theorem sum_pairSum (L : List Bytes) (F : Nat → Bytes → Bytes → Nat) (R : Nat) :
    ((List.range R).map fun v => pairSum L (F v)).sum =
      pairSum L (fun m m' => ((List.range R).map fun v => F v m m').sum) := by
  classical
  unfold pairSum
  rw [← sum_map_sum_comm]
  congr 1; apply List.map_congr_left; intro m _
  rw [← sum_map_sum_comm]
  congr 1; apply List.map_congr_left; intro m' _
  by_cases hm : m = m'
  · simp [hm, Security.sum_map_const]
  · simp [hm]

theorem pairSum_mul (L : List Bytes) (f : Bytes → Bytes → Nat) (c : Nat) :
    pairSum L (fun m m' => c * f m m') = c * pairSum L f := by
  classical
  unfold pairSum
  rw [← sum_map_mul_left]
  congr 1; apply List.map_congr_left; intro m _
  rw [← sum_map_mul_left]
  congr 1; apply List.map_congr_left; intro m' _
  by_cases hm : m = m' <;> simp [hm]

/-- Adding a fresh key `m0` (not in `L`) whose pair terms are all `1`. -/
theorem pairSum_cons (L : List Bytes) (m0 : Bytes) (h0 : m0 ∉ L) (f : Bytes → Bytes → Nat)
    (h1 : ∀ m, f m0 m = 1) (h2 : ∀ m, f m m0 = 1) :
    pairSum (m0 :: L) f = pairSum L f + 2 * L.length := by
  classical
  unfold pairSum
  have hne : ∀ m ∈ L, m ≠ m0 := fun m hm h => h0 (h ▸ hm)
  simp only [List.map_cons, List.sum_cons, ite_true, Nat.zero_add]
  have e1 : (L.map fun m' => if m0 = m' then 0 else f m0 m').sum = L.length := by
    rw [List.map_congr_left (g := fun _ => 1) (fun m hm => by
      rw [ite_eq_right (fun h => hne m hm h.symm), h1])]
    simp [Security.sum_map_const]
  have e2 : (L.map fun m => (if m = m0 then 0 else f m m0) +
      (L.map fun m' => if m = m' then 0 else f m m').sum).sum =
      L.length + (L.map fun m => (L.map fun m' => if m = m' then 0 else f m m').sum).sum := by
    rw [sum_map_add]
    congr 1
    rw [List.map_congr_left (g := fun _ => 1) (fun m hm => by rw [ite_eq_right (hne m hm), h2])]
    simp [Security.sum_map_const]
  rw [e1, e2]; omega

theorem pairFactor_off {enc : Bytes → Nat → Bytes} {x y : Bytes} {tbl : Table}
    {m m' : Bytes} {j : Nat} (h : enc m j ≠ x) (h' : enc m' j ≠ x) :
    pairFactor enc ((x, y) :: tbl) m m' j = pairFactor enc tbl m m' j := by
  unfold pairFactor
  rw [lookup_cons, lookup_cons, ite_eq_right h, ite_eq_right h']

theorem pairFactor_fresh {enc : Bytes → Nat → Bytes} {tbl : Table} {m m' : Bytes} {j : Nat}
    (h : tbl.lookup (enc m j) = none) : pairFactor enc tbl m m' j = 1 := by
  unfold pairFactor; rw [h]

theorem pairFactor_fresh' {enc : Bytes → Nat → Bytes} {tbl : Table} {m m' : Bytes} {j : Nat}
    (h : tbl.lookup (enc m' j) = none) : pairFactor enc tbl m m' j = 1 := by
  unfold pairFactor; rw [h]; split <;> simp_all

/-- A fresh answer for one of the two queries `enc m j`, `enc m' j`
(distinct): the pair factor contracts in expectation. -/
theorem pairFactor_step (enc : Bytes → Nat → Bytes) (tbl : Table) (m m' : Bytes) (j : Nat)
    (hne : enc m j ≠ enc m' j) (x : Bytes) (hx : tbl.lookup x = none)
    (hj : enc m j = x ∨ enc m' j = x) :
    ((List.range roRange).map fun v => pairFactor enc ((x, LazyRO.answer v) :: tbl) m m' j).sum ≤
      roRange * pairFactor enc tbl m m' j := by
  classical
  rcases hj with hj | hj
  · subst hj
    rw [pairFactor_fresh hx, Nat.mul_one]
    cases hb : tbl.lookup (enc m' j) with
    | none =>
      have : ∀ v, pairFactor enc ((enc m j, LazyRO.answer v) :: tbl) m m' j = 1 := by
        intro v; unfold pairFactor
        rw [lookup_cons, lookup_cons, ite_eq_left rfl, ite_eq_right (Ne.symm hne), hb]
      simp [this, Security.sum_map_const]
    | some b =>
      have : ∀ v, pairFactor enc ((enc m j, LazyRO.answer v) :: tbl) m m' j =
          if LazyRO.answer v = b then roRange else 0 := by
        intro v; unfold pairFactor
        rw [lookup_cons, lookup_cons, ite_eq_left rfl, ite_eq_right (Ne.symm hne), hb]
      simp only [this]
      rw [sum_map_ite' _ (fun v => LazyRO.answer v = b), Nat.mul_comm]
      exact Nat.le_trans (Nat.mul_le_mul_left _ (answer_count_le_one b)) (by simp)
  · subst hj
    rw [pairFactor_fresh' hx, Nat.mul_one]
    cases ha : tbl.lookup (enc m j) with
    | none =>
      have : ∀ v, pairFactor enc ((enc m' j, LazyRO.answer v) :: tbl) m m' j = 1 := by
        intro v; unfold pairFactor
        rw [lookup_cons, lookup_cons, ite_eq_left rfl, ite_eq_right hne, ha]
      simp [this, Security.sum_map_const]
    | some a =>
      have : ∀ v, pairFactor enc ((enc m' j, LazyRO.answer v) :: tbl) m m' j =
          if LazyRO.answer v = a then roRange else 0 := by
        intro v; unfold pairFactor
        rw [lookup_cons, lookup_cons, ite_eq_left rfl, ite_eq_right hne, ha]
        by_cases h : LazyRO.answer v = a
        · simp [h]
        · simp only [h, ite_false]; rw [ite_eq_right (fun h' => h h'.symm)]
      simp only [this]
      rw [sum_map_ite' _ (fun v => LazyRO.answer v = a), Nat.mul_comm]
      exact Nat.le_trans (Nat.mul_le_mul_left _ (answer_count_le_one a)) (by simp)

/-- Injectivity of the chunk encoding, from the decoder. -/
theorem enc_inj {k : Nat} {enc : Bytes → Nat → Bytes} {dec : Bytes → Option (Bytes × Nat)}
    (hdec : ∀ m j, j < k → dec (enc m j) = some (m, j)) {m m' : Bytes} {j j' : Nat}
    (hj : j < k) (hj' : j' < k) (h : enc m j = enc m' j') : m = m' ∧ j = j' := by
  have h1 := hdec m j hj
  rw [h, hdec m' j' hj'] at h1
  injection h1 with h1; injection h1 with h1 h2
  exact ⟨h1.symm, h2.symm⟩

/-- Each ordered pair term contracts in expectation. -/
theorem pairTerm_step (k : Nat) (enc : Bytes → Nat → Bytes) (dec : Bytes → Option (Bytes × Nat))
    (hdec : ∀ m j, j < k → dec (enc m j) = some (m, j)) (tbl : Table) (m m' : Bytes) (hmm : m ≠ m')
    (x : Bytes) (hx : tbl.lookup x = none) :
    ((List.range roRange).map fun v => pairTerm k enc ((x, LazyRO.answer v) :: tbl) m m').sum ≤
      roRange * pairTerm k enc tbl m m' := by
  classical
  unfold pairTerm
  by_cases hhit : ∃ j0, j0 < k ∧ (enc m j0 = x ∨ enc m' j0 = x)
  · obtain ⟨j0, hj0, hj⟩ := hhit
    apply prod_step roRange (fun j => j < k) (pairFactor enc tbl m m')
      (fun v => pairFactor enc ((x, LazyRO.answer v) :: tbl) m m') j0
    · intro v j hjk hjj
      apply pairFactor_off
      · intro he
        rcases hj with hj | hj
        · exact hjj (enc_inj hdec hjk hj0 (he.trans hj.symm)).2
        · exact hjj (enc_inj hdec hjk hj0 (he.trans hj.symm)).2
      · intro he
        rcases hj with hj | hj
        · exact hjj (enc_inj hdec hjk hj0 (he.trans hj.symm)).2
        · exact hjj (enc_inj hdec hjk hj0 (he.trans hj.symm)).2
    · exact pairFactor_step enc tbl m m' j0
        (fun h => hmm (enc_inj hdec hj0 hj0 h).1) x hx hj
    · exact List.nodup_range
    · intro j hj; exact List.mem_range.mp hj
  · have e : ∀ v, (List.range k).map (pairFactor enc ((x, LazyRO.answer v) :: tbl) m m') =
        (List.range k).map (pairFactor enc tbl m m') := by
      intro v
      apply List.map_congr_left
      intro j hj
      have hj := List.mem_range.mp hj
      exact pairFactor_off (fun h => hhit ⟨j, hj, Or.inl h⟩) (fun h => hhit ⟨j, hj, Or.inr h⟩)
    simp only [e, Security.sum_map_const, List.length_range]
    exact Nat.le_refl _

/-- An untouched key has all pair terms equal to `1`. -/
theorem pairTerm_untouched (k : Nat) (enc : Bytes → Nat → Bytes) (dec : Bytes → Option (Bytes × Nat))
    (hdec : ∀ m j, j < k → dec (enc m j) = some (m, j)) (tbl : Table) (m0 : Bytes)
    (h0 : m0 ∉ touched dec tbl) (m : Bytes) :
    pairTerm k enc tbl m0 m = 1 ∧ pairTerm k enc tbl m m0 = 1 := by
  have hnone : ∀ j, j < k → tbl.lookup (enc m0 j) = none := by
    intro j hj
    cases hl : tbl.lookup (enc m0 j) with
    | none => rfl
    | some y =>
      exfalso
      obtain ⟨y', hy'⟩ := lookup_some_mem hl
      exact h0 (mem_touched hy' (hdec m0 j hj))
  have h1 : ∀ j ∈ List.range k, pairFactor enc tbl m0 m j = 1 :=
    fun j hj => pairFactor_fresh (hnone j (List.mem_range.mp hj))
  have h2 : ∀ j ∈ List.range k, pairFactor enc tbl m m0 j = 1 :=
    fun j hj => pairFactor_fresh' (hnone j (List.mem_range.mp hj))
  unfold pairTerm
  rw [List.map_congr_left h1, List.map_congr_left h2, List.map_const', prod_replicate', Nat.one_pow]
  exact ⟨rfl, rfl⟩

/-- **One-step bound for the collision potential**: each fresh query adds at
most `2N` (scaled) — one new unit for every pair the query can create. -/
theorem pairPot_step (k : Nat) (enc : Bytes → Nat → Bytes) (dec : Bytes → Option (Bytes × Nat))
    (hdec : ∀ m j, j < k → dec (enc m j) = some (m, j)) (N : Nat) :
    StepBound (pairPot k enc dec N) unitWeight (2 * N) := by
  classical
  intro tbl x hx
  simp only [unitWeight, Nat.mul_one]
  by_cases hN : N ≤ tbl.length
  · -- frozen
    have e : ∀ v, pairPot k enc dec N ((x, LazyRO.answer v) :: tbl) = pairPot k enc dec N tbl := by
      intro v; unfold pairPot; rw [oldest_cons_of_ge hN]
    simp only [e, Security.sum_map_const, List.length_range]
    exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  · have hlt : tbl.length < N := by omega
    have e : ∀ v, pairPot k enc dec N ((x, LazyRO.answer v) :: tbl) =
        pairSum (touched dec ((x, []) :: tbl)) (pairTerm k enc ((x, LazyRO.answer v) :: tbl)) := by
      intro v; unfold pairPot; rw [oldest_cons_of_lt hlt]; simp only [touched]
    have e0 : pairPot k enc dec N tbl = pairSum (touched dec tbl) (pairTerm k enc tbl) := by
      unfold pairPot; rw [oldest_of_le (by omega)]
    simp only [e, e0]
    rw [sum_pairSum]
    -- termwise contraction
    refine Nat.le_trans (pairSum_le _ _ (fun m m' => roRange * pairTerm k enc tbl m m') ?_) ?_
    · intro m m' hmm
      exact pairTerm_step k enc dec hdec tbl m m' hmm x hx
    · rw [pairSum_mul]
      apply Nat.mul_le_mul_left
      have hL := touched_length_le dec tbl
      simp only [touched]
      split
      · rename_i m0 j0 hd
        split
        · exact Nat.le_add_right _ _
        · rename_i hnot
          rw [pairSum_cons _ m0 hnot _ (fun m => (pairTerm_untouched k enc dec hdec tbl m0 hnot m).1)
            (fun m => (pairTerm_untouched k enc dec hdec tbl m0 hnot m).2)]
          omega
      · exact Nat.le_add_right _ _

/-- A `q`-query computation adds at most `q` entries to the log. -/
theorem table_length_le {α : Type} {A : OracleComp hashSpec α} {q : Nat}
    (hA : OracleComp.QueryBound unitWeight A q) :
    ∀ s : LazyRO, (OracleComp.simulate hashImpl A s).2.table.length ≤ s.table.length + q := by
  induction hA with
  | pure a q => intro s; exact Nat.le_add_right _ _
  | query x k q hw _ ih =>
    intro s
    simp only [unitWeight] at hw
    simp only [OracleComp.simulate]
    refine Nat.le_trans (ih _ _) ?_
    simp only [unitWeight]
    unfold hashImpl LazyRO.query
    cases hl : s.table.lookup x with
    | some y => simp only; omega
    | none =>
      cases ht : s.tape with
      | nil => simp only; omega
      | cons t ts => simp only [List.length_cons]; omega

/-- A wide collision drives the collision potential to `(2^256)^k`
(for logs of at most `N` entries). -/
theorem wideCollision_pot (k : Nat) (hk : 0 < k) (enc : Bytes → Nat → Bytes)
    (dec : Bytes → Option (Bytes × Nat)) (hdec : ∀ m j, j < k → dec (enc m j) = some (m, j))
    (N : Nat) (tbl : Table) (hlen : tbl.length ≤ N) (hc : WideCollision k enc tbl) :
    roRange ^ k ≤ pairPot k enc dec N tbl := by
  classical
  obtain ⟨m, m', hmm, hj⟩ := hc
  unfold pairPot
  rw [oldest_of_le hlen]
  have hterm : pairTerm k enc tbl m m' = roRange ^ k := by
    unfold pairTerm
    have : ∀ j ∈ List.range k, pairFactor enc tbl m m' j = roRange := by
      intro j hj'
      obtain ⟨a, ha, ha'⟩ := hj j (List.mem_range.mp hj')
      unfold pairFactor; rw [ha, ha']; simp
    rw [List.map_congr_left this, List.map_const', List.length_range, prod_replicate']
  have hm : m ∈ touched dec tbl := by
    obtain ⟨a, ha, _⟩ := hj 0 hk
    obtain ⟨y', hy'⟩ := lookup_some_mem ha
    exact mem_touched hy' (hdec m 0 hk)
  have hm' : m' ∈ touched dec tbl := by
    obtain ⟨a, _, ha⟩ := hj 0 hk
    obtain ⟨y', hy'⟩ := lookup_some_mem ha
    exact mem_touched hy' (hdec m' 0 hk)
  unfold pairSum
  rw [← hterm]
  refine Nat.le_trans ?_ (le_sum_of_mem' (List.mem_map.mpr ⟨m, hm, rfl⟩))
  refine Nat.le_trans ?_ (le_sum_of_mem' (List.mem_map.mpr ⟨m', hm', rfl⟩))
  simp [hmm]

/-- **Wide-digest binding.**  A computation with at most `q ≤ N` oracle
queries finds two distinct keys whose `k` chunk answers all coincide with
probability at most `2·N·q / (2^256)^k`. -/
theorem collision_bound (k : Nat) (hk : 0 < k) (enc : Bytes → Nat → Bytes)
    (dec : Bytes → Option (Bytes × Nat)) (hdec : ∀ m j, j < k → dec (enc m j) = some (m, j))
    {α : Type} (A : OracleComp hashSpec α) (q N : Nat) (hA : OracleComp.QueryBound unitWeight A q)
    (hqN : q ≤ N) (n : Nat) :
    PrLE n roRange (fun t => WideCollision k enc (finalTable A (LazyRO.init t)))
      (2 * N * q) (roRange ^ k) := by
  have h := prLE_of_potential (pairPot_step k enc dec hdec N) hA n [] false
    (fun t => WideCollision k enc (finalTable A (LazyRO.init t))) (roRange ^ k)
    (Nat.pow_pos (by rw [ArenaCore.Security.roRange_eq]; exact Nat.pow_pos (by decide)))
    (fun t _ hc => wideCollision_pot k hk enc dec hdec N _
      (by have := table_length_le hA ⟨t, [], false⟩; simp at this; unfold finalTable; omega) hc)
  have e : pairPot k enc dec N [] = 0 := by
    unfold pairPot oldest pairSum; simp [touched]
  rw [e, Nat.zero_add] at h
  exact h

end ZkFormal
