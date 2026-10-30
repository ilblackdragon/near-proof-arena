import NearSpecV3.Resharding
import NearSpec.TrieUpsertProofs

/-!
# `NearSpecV3.ReshardingProofs` — the shard split is correct, partitions the key space, and reads
only authenticated data (W11)

`Resharding.lean` models the validator's resharding implicit transition
(`Trie::retain_split_shard`, `core/store/src/trie/ops/resharding.rs:143-260` with
`squash.rs:29-178`) as `retainSplit`, and its module docstring recorded the key-level correctness
theorem as a residual obligation ("needs a custom induction principle"). This module discharges it
and adds the two properties a consumer of the split needs:

* **Correctness** (`retainSplit_get`, `splitChild_get`): whenever the split succeeds, the child
  trie answers a key exactly as the parent does when the key lies in one of the retained ranges,
  and answers nothing otherwise. Squashing (`squashBranch`, `extendChild`) and the recomputed
  `memory_usage` are covered: they change node shapes and hashes but never a lookup.
* **Partition** (`splitKey_partition`, `copyToBoth_both`, `copyToOne_right_empty`): for an
  account-prefixed column the two children's ranges are adjacent half-open intervals whose union is
  the column's range, so every key of the column is retained by exactly one child; a copy-to-both
  column is retained by both; a copy-to-one-child column by the left child only
  (`resharding.rs:99-134`). `allColumns_id_lt` discharges the side condition for every column of
  the pinned table.
* **Authentication** (`retainSplit_refinedBy`, `splitRootE_refinedBy`): the split reads only nodes
  the parent's state root commits to. If the split succeeds on a partial parent trie `t₁`, it
  succeeds on every `t₂` that reveals more of the same trie (`t₁.refinedBy t₂`: same hashes,
  more nodes revealed), and the two child roots are equal. Together with `Logged.hashOf_revealAll`
  (the revealed parent hashes to the root it was revealed from) this says the child state root the
  validator compares with the witness is a function of the authenticated parent root and of the
  nodes the split reads, not of anything else the witness happens to reveal.

What this does **not** establish: that `retainSplit` agrees with nearcore's `retain_split_shard`
node for node. That remains a differential obligation, discharged by the validator-generated split
fixtures (`docs/evidence/lean-chunk-completion/resharding-fixtures*/`).

Axioms: `propext`, `Classical.choice`, `Quot.sound` (audit in
`docs/logs/lean-proof-debt-2026-10-29.md`).
-/

namespace NearSpecV3

open NearSpec NearSpecV3.D2

/-! ## Lexicographic order on nibble keys -/

/-- A key in some retained range. -/
def anyIn (ranges : List (List Nat × List Nat)) (k : List Nat) : Bool :=
  ranges.any fun r => inRange k r

theorem isPrefixOf_nil_right (b : List Nat) : isPrefixOf b [] = true := by
  simp [isPrefixOf]

theorem isPrefixOf_cons (b : Nat) (bs : List Nat) (x : Nat) (xs : List Nat) :
    isPrefixOf (b :: bs) (x :: xs) = (b == x && isPrefixOf bs xs) := by
  simp [isPrefixOf, List.take_succ_cons]

/-- Extending a key that is not a prefix of `b` does not move it across `b`. -/
theorem append_lt_iff_of_not_prefix : ∀ (key b k : List Nat), isPrefixOf b key = false →
    (key ++ k < b ↔ key < b)
  | [], b, _, h => by rw [isPrefixOf_nil_right] at h; cases h
  | _ :: _, [], _, _ => by simp
  | x :: xs, y :: ys, k, h => by
    rw [isPrefixOf_cons] at h
    simp only [List.cons_append, List.cons_lt_cons_iff]
    by_cases hxy : y = x
    · subst hxy
      simp only [beq_self_eq_true, Bool.true_and] at h
      rw [append_lt_iff_of_not_prefix xs ys k h]
    · have hne : x ≠ y := fun e => hxy e.symm
      simp only [hne, false_and, or_false]

theorem le_append_iff_of_not_prefix (key b k : List Nat) (h : isPrefixOf b key = false) :
    (b ≤ key ++ k ↔ b ≤ key) := by
  show ¬ (key ++ k < b) ↔ ¬ (key < b)
  rw [append_lt_iff_of_not_prefix key b k h]

/-- Away from both boundaries, extending a key does not change its range membership. -/
theorem inRange_append_of_not_prefix (key k : List Nat) (r : List Nat × List Nat)
    (h1 : isPrefixOf r.1 key = false) (h2 : isPrefixOf r.2 key = false) :
    inRange (key ++ k) r = inRange key r := by
  unfold inRange
  have e1 : decide (r.1 ≤ key ++ k) = decide (r.1 ≤ key) :=
    decide_eq_decide.mpr (le_append_iff_of_not_prefix key r.1 k h1)
  have e2 : decide (key ++ k < r.2) = decide (key < r.2) :=
    decide_eq_decide.mpr (append_lt_iff_of_not_prefix key r.2 k h2)
  rw [e1, e2]

/-- When the split does not descend, every key below `key` has `key`'s range membership. -/
theorem anyIn_append_of_not_descend (key k : List Nat) (ranges : List (List Nat × List Nat))
    (h : (ranges.any fun r => isPrefixOf r.1 key || isPrefixOf r.2 key) = false) :
    anyIn ranges (key ++ k) = anyIn ranges key := by
  unfold anyIn
  induction ranges with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at h ⊢
    obtain ⟨hr, hrs⟩ := h
    rw [inRange_append_of_not_prefix key k r hr.1 hr.2, ih hrs]

theorem retainDecision_retainAll {key : List Nat} {ranges : List (List Nat × List Nat)}
    (h : retainDecision key ranges = .retainAll) (k : List Nat) : anyIn ranges (key ++ k) = true := by
  unfold retainDecision at h
  cases hp : ranges.any (fun r => isPrefixOf r.1 key || isPrefixOf r.2 key)
  · rw [anyIn_append_of_not_descend key k ranges hp]
    cases hi : ranges.any (fun r => inRange key r)
    · simp [hp, hi] at h
    · exact hi
  · simp [hp] at h

theorem retainDecision_discardAll {key : List Nat} {ranges : List (List Nat × List Nat)}
    (h : retainDecision key ranges = .discardAll) (k : List Nat) : anyIn ranges (key ++ k) = false := by
  have ⟨hp, hi⟩ := (discardAll_iff_outside key ranges).mp h
  rw [anyIn_append_of_not_descend key k ranges hp]
  exact hi

/-! ## Lookups through the squash helpers -/

theorem isPrefix_append_iff : ∀ (k k2 p : List Nat),
    isPrefix (k ++ k2) p = (isPrefix k p && isPrefix k2 (p.drop k.length))
  | [], k2, p => by simp [isPrefix]
  | _ :: _, _, [] => by simp [isPrefix]
  | a :: as, k2, b :: bs => by
    simp only [List.cons_append, isPrefix, List.length_cons, List.drop_succ_cons]
    rw [isPrefix_append_iff as k2 bs, Bool.and_assoc]

theorem beq_append_iff : ∀ (k k2 p : List Nat),
    (k ++ k2 == p) = (isPrefix k p && (k2 == p.drop k.length))
  | [], k2, p => by simp [isPrefix]
  | _ :: _, _, [] => by simp [isPrefix]
  | a :: as, k2, b :: bs => by
    simp only [List.cons_append, isPrefix, List.length_cons, List.drop_succ_cons, List.cons_beq_cons]
    rw [beq_append_iff as k2 bs, Bool.and_assoc]

theorem isPrefix_take_drop : ∀ (k p : List Nat), isPrefix k p = true → k ++ p.drop k.length = p
  | [], p, _ => by simp
  | _ :: _, [], h => by simp [isPrefix] at h
  | a :: as, b :: bs, h => by
    simp only [isPrefix, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h2⟩ := h
    simp only [List.cons_append, List.length_cons, List.drop_succ_cons]
    rw [isPrefix_take_drop as bs h2]

/-- `extendChild` (`squash.rs:113-178`) prepends `k` to the child's keys and changes no lookup. -/
theorem extendChild_get {k : List Nat} {c : PTrie} {r : Option PTrie} (h : extendChild k c = some r)
    (p : List Nat) :
    (r.bind fun x => x.get p) = if isPrefix k p then c.get (p.drop k.length) else none := by
  cases c with
  | hash _ => simp [extendChild] at h
  | leaf k2 s m =>
    simp only [extendChild, Option.some.injEq] at h; subst h
    simp only [Option.bind_some, PTrie.get]
    rw [beq_append_iff]
    cases isPrefix k p <;> simp
  | ext k2 c2 m =>
    simp only [extendChild, Option.some.injEq] at h; subst h
    simp only [Option.bind_some, PTrie.get]
    rw [isPrefix_append_iff, List.length_append, ← List.drop_drop]
    cases isPrefix k p <;> simp
  | branch v cs m =>
    simp only [extendChild, Option.some.injEq] at h; subst h
    rfl

theorem Kids.get_present_nil : ∀ (cs : Kids) (j n : Nat) (p : List Nat),
    Kids.present cs j = [] → Kids.get cs n p = none
  | .nil, _, n, _, _ => by cases n <;> rfl
  | .none r, j, 0, p, _ => rfl
  | .none r, j, n + 1, p, h => by
    simp only [Kids.present] at h
    exact Kids.get_present_nil r (j + 1) n p h
  | .some c r, j, n, p, h => by simp [Kids.present] at h

theorem Kids.get_present_single : ∀ (cs : Kids) (j n i : Nat) (c : PTrie) (p : List Nat),
    Kids.present cs j = [(i, c)] → Kids.get cs n p = if j + n = i then c.get p else none
  | .nil, _, _, _, _, _, h => by simp [Kids.present] at h
  | .none r, j, 0, i, c, p, h => by
    simp only [Kids.present] at h
    have := Kids.get_present_single r (j + 1) 0 i c p h
    -- `r` holds the single child at an index ≥ j + 1, so index j is empty
    simp only [Kids.get]
    have hi : i ≠ j + 0 := by
      intro e
      have := Kids.present_index_ge r (j + 1) i c (by rw [h]; exact List.mem_singleton.mpr rfl)
      omega
    have hne : ¬ (j + 0 = i) := fun e => hi e.symm
    simp only [hne, ite_false]
  | .none r, j, n + 1, i, c, p, h => by
    simp only [Kids.present] at h
    simp only [Kids.get]
    rw [Kids.get_present_single r (j + 1) n i c p h]
    have : j + 1 + n = j + (n + 1) := by omega
    rw [this]
  | .some c0 r, j, n, i, c, p, h => by
    simp only [Kids.present, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, hr⟩ := h
    cases n with
    | zero => simp [Kids.get]
    | succ n =>
      simp only [Kids.get]
      rw [Kids.get_present_nil r (j + 1) n p hr]
      simp
where
  Kids.present_index_ge : ∀ (cs : Kids) (j i : Nat) (c : PTrie), (i, c) ∈ Kids.present cs j → j ≤ i
    | .nil, _, _, _, h => by simp [Kids.present] at h
    | .none r, j, i, c, h => by
      simp only [Kids.present] at h
      have := Kids.present_index_ge r (j + 1) i c h; omega
    | .some c0 r, j, i, c, h => by
      simp only [Kids.present, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩ | h
      · exact Nat.le_refl _
      · have := Kids.present_index_ge r (j + 1) i c h; omega

/-- `squash_node` of a branch (`squash.rs:45-98`) changes no lookup. -/
theorem squashBranch_get {v : Option Slot} {cs : Kids} {m : Nat} {r : Option PTrie}
    (h : squashBranch v cs m = some r) (p : List Nat) :
    (r.bind fun x => x.get p) = (PTrie.branch v cs m).get p := by
  unfold squashBranch at h
  cases hp : Kids.present cs 0 with
  | nil =>
    rw [hp] at h
    cases v with
    | none =>
      simp only [Option.some.injEq] at h; subst h
      cases p with
      | nil => rfl
      | cons n rest => simp only [Option.bind_none, PTrie.get]; rw [Kids.get_present_nil cs 0 n rest hp]
    | some s =>
      simp only [Option.some.injEq] at h; subst h
      cases p with
      | nil => simp [PTrie.get]
      | cons n rest =>
        simp only [Option.bind_some, PTrie.get]
        rw [Kids.get_present_nil cs 0 n rest hp]; simp
  | cons e es =>
    rw [hp] at h
    obtain ⟨i, c⟩ := e
    cases es with
    | nil =>
      cases v with
      | none =>
        simp only at h
        rw [extendChild_get h p]
        cases p with
        | nil => simp [isPrefix, PTrie.get]
        | cons n rest =>
          simp only [PTrie.get, isPrefix, Bool.and_true, List.length_singleton, List.drop_succ_cons,
            List.drop_zero]
          rw [Kids.get_present_single cs 0 n i c rest hp]
          by_cases hn : i = n
          · subst hn; simp
          · have : ¬ (0 + n = i) := by omega
            simp only [this, ite_false]
            have : (i == n) = false := by simpa using hn
            simp [this]
      | some s =>
        simp only [Option.some.injEq] at h; subst h; rfl
    | cons e2 es2 =>
      simp only [Option.some.injEq] at h; subst h; rfl

/-! ## The split's equations, per decision -/

section
variable (ranges : List (List Nat × List Nat))

theorem retainSplit_retainAll (t : PTrie) (key : List Nat) (hd : retainDecision key ranges = .retainAll) :
    retainSplit t key ranges = some (some t) := by
  unfold retainSplit; rw [hd]

theorem retainSplit_discardAll (t : PTrie) (key : List Nat)
    (hd : retainDecision key ranges = .discardAll) : retainSplit t key ranges = some none := by
  unfold retainSplit; rw [hd]

theorem retainSplit_hash (h0 : Bytes) (key : List Nat) (hd : retainDecision key ranges = .descend) :
    retainSplit (.hash h0) key ranges = none := by
  unfold retainSplit; rw [hd]

theorem retainSplit_leaf (k : List Nat) (v : Slot) (m : Nat) (key : List Nat)
    (hd : retainDecision key ranges = .descend) :
    retainSplit (.leaf k v m) key ranges =
      some (if ranges.any (fun r => inRange (key ++ k) r) then some (.leaf k v m) else none) := by
  unfold retainSplit; rw [hd]

theorem retainSplit_ext (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat)
    (hd : retainDecision key ranges = .descend) (hc : ∀ h0, c ≠ .hash h0) :
    retainSplit (.ext k c m) key ranges =
      (retainSplit c (key ++ k) ranges).bind fun c'' => match c'' with
        | none => some none
        | some c' => NearSpec.extendChild k c' := by
  rw [retainSplit]
  rw [hd]
  cases c with
  | hash h0 => exact absurd rfl (hc h0)
  | leaf _ _ _ => rfl
  | ext _ _ _ => rfl
  | branch _ _ _ => rfl
  all_goals exact fun h0 e => hc h0 e

theorem retainSplit_branch (v : Option Slot) (cs : Kids) (m : Nat) (key : List Nat)
    (hd : retainDecision key ranges = .descend) :
    retainSplit (.branch v cs m) key ranges =
      (retainSplitKids key ranges 0 cs).bind fun (cs', m') =>
        let v' := if ranges.any (fun r => inRange key r) then v else none
        NearSpec.squashBranch v' cs' (m' + (50 + match v' with | some s => NearSpec.valueMem s.len | none => 0)) := by
  unfold retainSplit; rw [hd]; rfl

end

/-! ## Correctness of the split -/

/-- The two non-descending decisions, for any subtree. -/
theorem retainSplit_get_nodescend (ranges : List (List Nat × List Nat)) (t : PTrie) (key : List Nat)
    (r : Option PTrie) (hd : retainDecision key ranges ≠ .descend) (h : retainSplit t key ranges = some r)
    (p : List Nat) : (r.bind fun x => x.get p) = if anyIn ranges (key ++ p) then t.get p else none := by
  rcases retainDecision_cases key ranges with hd' | hd' | hd'
  · rw [retainSplit_retainAll ranges t key hd'] at h
    simp only [Option.some.injEq] at h; subst h
    simp [retainDecision_retainAll hd' p]
  · rw [retainSplit_discardAll ranges t key hd'] at h
    simp only [Option.some.injEq] at h; subst h
    simp [retainDecision_discardAll hd' p]
  · exact absurd hd' hd

mutual

/-- **The split is correct.** Whenever `retainSplit` succeeds on the subtree at nibble key `key`,
the retained subtree answers a lookup `p` exactly as the parent subtree does if `key ++ p` lies in a
retained range, and answers nothing otherwise. -/
theorem retainSplit_get (ranges : List (List Nat × List Nat)) :
    ∀ (t : PTrie) (key : List Nat) (r : Option PTrie), retainSplit t key ranges = some r →
      ∀ p, (r.bind fun x => x.get p) = if anyIn ranges (key ++ p) then t.get p else none
  | .hash h0, key, r, h, p => by
    by_cases hd : retainDecision key ranges = .descend
    case neg => exact retainSplit_get_nodescend ranges _ key r hd h p
    rw [retainSplit_hash ranges h0 key hd] at h; cases h
  | .leaf k v m, key, r, h, p => by
    by_cases hd : retainDecision key ranges = .descend
    case neg => exact retainSplit_get_nodescend ranges _ key r hd h p
    rw [retainSplit_leaf ranges k v m key hd] at h
    simp only [Option.some.injEq] at h; subst h
    simp only [PTrie.get]
    by_cases hk : k = p
    · subst hk
      cases ha : ranges.any (fun r => inRange (key ++ k) r) <;> simp [anyIn, ha, PTrie.get]
    · have : (k == p) = false := by simpa using hk
      cases ha : ranges.any (fun r => inRange (key ++ k) r) <;> simp [this, PTrie.get]
  | .ext k c m, key, r, h, p => by
    by_cases hd : retainDecision key ranges = .descend
    case neg => exact retainSplit_get_nodescend ranges _ key r hd h p
    by_cases hc : ∃ h0, c = .hash h0
    · obtain ⟨h0, rfl⟩ := hc
      unfold retainSplit at h; rw [hd] at h; cases h
    · have hc' : ∀ h0, c ≠ .hash h0 := fun h0 e => hc ⟨h0, e⟩
      rw [retainSplit_ext ranges k c m key hd hc'] at h
      cases hcr : retainSplit c (key ++ k) ranges with
      | none => rw [hcr] at h; cases h
      | some c'' =>
        rw [hcr] at h
        have ih := retainSplit_get ranges c (key ++ k) c'' hcr
        simp only [PTrie.get]
        cases c'' with
        | none =>
          simp only [Option.bind_some, Option.some.injEq] at h; subst h
          simp only [Option.bind_none]
          by_cases hp : isPrefix k p = true
          · have e := ih (p.drop k.length)
            simp only [Option.bind_none] at e
            rw [List.append_assoc, isPrefix_take_drop k p hp] at e
            simp only [hp, ite_true]; exact e
          · simp [hp]
        | some c' =>
          simp only [Option.bind_some] at h
          rw [extendChild_get h p]
          by_cases hp : isPrefix k p = true
          · have e := ih (p.drop k.length)
            simp only [Option.bind_some] at e
            rw [List.append_assoc, isPrefix_take_drop k p hp] at e
            simp only [hp, ite_true]; exact e
          · simp [hp]
  | .branch v cs m, key, r, h, p => by
    by_cases hd : retainDecision key ranges = .descend
    case neg => exact retainSplit_get_nodescend ranges _ key r hd h p
    rw [retainSplit_branch ranges v cs m key hd] at h
    cases hk : retainSplitKids key ranges 0 cs with
    | none => rw [hk] at h; cases h
    | some q =>
      obtain ⟨cs', m'⟩ := q
      rw [hk] at h
      simp only [Option.bind_some] at h
      rw [squashBranch_get h p]
      cases p with
      | nil =>
        simp only [PTrie.get, List.append_nil]
        by_cases ha : anyIn ranges key = true
        · have : ranges.any (fun r => inRange key r) = true := ha
          simp [this, ha]
        · have : ranges.any (fun r => inRange key r) = false := by simpa [anyIn] using ha
          simp [this, anyIn]
      | cons n rest =>
        simp only [PTrie.get]
        have := retainSplitKids_get ranges cs key 0 cs' m' hk n rest
        simpa using this

/-- The children of a descended branch: child `i + n` is looked up under key `key ++ [i + n]`. -/
theorem retainSplitKids_get (ranges : List (List Nat × List Nat)) :
    ∀ (cs : Kids) (key : List Nat) (i : Nat) (cs' : Kids) (m : Nat),
      retainSplitKids key ranges i cs = some (cs', m) →
      ∀ n p, Kids.get cs' n p = if anyIn ranges (key ++ (i + n) :: p) then Kids.get cs n p else none
  | .nil, key, i, cs', m, h, n, p => by
    simp only [retainSplitKids, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases n <;> simp [Kids.get]
  | .none rest, key, i, cs', m, h, n, p => by
    simp only [retainSplitKids] at h
    cases hr : retainSplitKids key ranges (i + 1) rest with
    | none => rw [hr] at h; cases h
    | some q =>
      obtain ⟨k', m2⟩ := q
      rw [hr] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases n with
      | zero => simp [Kids.get]
      | succ n =>
        simp only [Kids.get]
        rw [retainSplitKids_get ranges rest key (i + 1) k' m2 hr n p]
        rw [show i + 1 + n = i + (n + 1) by omega]
  | .some c rest, key, i, cs', m, h, n, p => by
    by_cases hc : ∃ h0, c = .hash h0
    · obtain ⟨h0, rfl⟩ := hc
      simp [retainSplitKids] at h
    · have hc' : ∀ h0, c ≠ .hash h0 := fun h0 e => hc ⟨h0, e⟩
      have hunf : retainSplitKids key ranges i (.some c rest) =
          (retainSplit c (key ++ [i]) ranges).bind fun c' =>
            (retainSplitKids key ranges (i + 1) rest).bind fun (k, m) =>
              match c' with
              | some c' => some (.some c' k, c'.memD + m)
              | none => some (.none k, m) := by
        cases c with
        | hash h0 => exact absurd rfl (hc' h0)
        | leaf _ _ _ => simp only [retainSplitKids]; rfl
        | ext _ _ _ => simp only [retainSplitKids]; rfl
        | branch _ _ _ => simp only [retainSplitKids]; rfl
      rw [hunf] at h
      cases hcr : retainSplit c (key ++ [i]) ranges with
      | none => rw [hcr] at h; cases h
      | some c'' =>
        rw [hcr] at h
        cases hr : retainSplitKids key ranges (i + 1) rest with
        | none => rw [hr] at h; cases c'' <;> cases h
        | some q =>
          obtain ⟨k', m2⟩ := q
          rw [hr] at h
          have ih := retainSplit_get ranges c (key ++ [i]) c'' hcr
          cases n with
          | zero =>
            cases c'' with
            | none =>
              simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have e := ih p
              simp only [Option.bind_none, List.append_assoc, List.singleton_append] at e
              simp only [Kids.get, Nat.add_zero]; exact e
            | some c' =>
              simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have e := ih p
              simp only [Option.bind_some, List.append_assoc, List.singleton_append] at e
              simp only [Kids.get, Nat.add_zero]; exact e
          | succ n =>
            have ihk := retainSplitKids_get ranges rest key (i + 1) k' m2 hr n p
            rw [show i + 1 + n = i + (n + 1) by omega] at ihk
            cases c'' with
            | none =>
              simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [Kids.get]; exact ihk
            | some c' =>
              simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [Kids.get]; exact ihk

end

/-- **The child state of a split** (`splitRootE`'s trie): a key is retained with its parent value
exactly when it lies in the child's ranges (`boundaryAccountToIntervals`, in nibbles). -/
theorem splitChild_get (parent : PTrie) (boundary : Bytes) (mode : RetainMode) (r : Option PTrie)
    (h : retainSplit parent [] (intervalsToNibbles (boundaryAccountToIntervals boundary mode)) = some r)
    (p : List Nat) :
    (r.bind fun x => x.get p) =
      if anyIn (intervalsToNibbles (boundaryAccountToIntervals boundary mode)) p then parent.get p
      else none := by
  have := retainSplit_get _ parent [] r h p
  simpa using this

/-! ## The two children partition each account-prefixed column -/

/-- Two adjacent half-open ranges `[lo, mid)` and `[mid, hi)` with `lo ≤ mid ≤ hi`: every key lies
in their union exactly when it lies in `[lo, hi)`, and in no case in both. -/
theorem inRange_adjacent (lo mid hi k : List Nat) (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    (inRange k (lo, mid) || inRange k (mid, hi)) = inRange k (lo, hi) ∧
      (inRange k (lo, mid) && inRange k (mid, hi)) = false := by
  unfold inRange
  simp only
  refine ⟨?_, ?_⟩
  · by_cases hm : mid ≤ k
    · have hlo : lo ≤ k := List.le_trans h1 hm
      by_cases hh : k < hi <;> simp [hm, hlo, hh]
    · have hkm : k < mid := Classical.not_not.mp hm
      have hkh : k < hi := Classical.byContradiction fun hn => h2 (List.lt_of_le_of_lt hn hkm)
      by_cases hl : lo ≤ k <;> simp [hm, hkm, hkh, hl]
  · by_cases hm : mid ≤ k
    · have : ¬ k < mid := hm
      simp [this]
    · simp [hm]

theorem toNibbles_cons (c : UInt8) (b : Bytes) : toNibbles (c :: b) = toNibbles [c] ++ toNibbles b := by
  simp [toNibbles]

/-- The boundary key `col ‖ account` sorts below the next column, `col + 1`. -/
theorem toNibbles_boundary_lt (c : UInt8) (b : Bytes) (hc : c.toNat < 255) :
    toNibbles (c :: b) < toNibbles [c + 1] := by
  have hs : (c + 1).toNat = c.toNat + 1 := by
    rw [UInt8.toNat_add]; simp; omega
  simp only [toNibbles, List.flatMap_cons, List.flatMap_nil, List.append_nil, byteNibbles,
    List.cons_append, List.nil_append, hs]
  rw [List.cons_lt_cons_iff]
  by_cases h16 : c.toNat / 16 < (c.toNat + 1) / 16
  · exact Or.inl h16
  · refine Or.inr ⟨by omega, ?_⟩
    rw [List.cons_lt_cons_iff]
    exact Or.inl (by omega)

/-- **The split columns are partitioned.** For an account-prefixed column `c` and boundary
account `b`, the left child's range `[c, c‖b)` and the right child's `[c‖b, c+1)` cover exactly
the column's range `[c, c+1)` and never overlap (`resharding.rs:99-115`): each key of the column
belongs to exactly one child. -/
theorem splitKey_partition (c : UInt8) (b : Bytes) (hc : c.toNat < 255) (k : List Nat) :
    (anyIn (intervalsToNibbles (splitKeyInterval c b .left)) k ||
        anyIn (intervalsToNibbles (splitKeyInterval c b .right)) k) =
      anyIn (intervalsToNibbles (copyToBothInterval c)) k ∧
    (anyIn (intervalsToNibbles (splitKeyInterval c b .left)) k &&
        anyIn (intervalsToNibbles (splitKeyInterval c b .right)) k) = false := by
  have h1 : toNibbles [c] ≤ toNibbles (appendKey c b) := by
    rw [appendKey, toNibbles_cons]; exact List.le_append_left
  have h2 : toNibbles (appendKey c b) ≤ toNibbles [c + 1] :=
    List.le_of_lt (toNibbles_boundary_lt c b hc)
  have := inRange_adjacent (toNibbles [c]) (toNibbles (appendKey c b)) (toNibbles [c + 1]) k h1 h2
  simpa [anyIn, intervalsToNibbles, splitKeyInterval, copyToBothInterval] using this

/-- A copy-to-both column is retained whole by each child (`resharding.rs:117-125`). -/
theorem copyToBoth_both (boundary : Bytes) (c : TrieCol) (mode : RetainMode)
    (hc : copyToBothColumns.contains c = true) (ha : accountColumns.contains c = false) :
    (if accountColumns.contains c then splitKeyInterval c.id boundary mode
      else if copyToBothColumns.contains c then copyToBothInterval c.id
      else copyToOneChildInterval c.id mode) = copyToBothInterval c.id := by
  simp only [ha, hc, Bool.false_eq_true, ite_false, ite_true]

/-- A copy-to-one-child column goes to the left child only (`resharding.rs:127-134`). -/
theorem copyToOne_right_empty (c : UInt8) : copyToOneChildInterval c .right = [] := rfl
theorem copyToOne_left_whole (c : UInt8) : copyToOneChildInterval c .left = copyToBothInterval c := rfl

/-- Every handled column id leaves room for its successor byte, so `splitKey_partition` applies to
every account-prefixed column of the pinned table. -/
theorem allColumns_id_lt : ∀ c ∈ allColumns, c.id.toNat < 255 := by decide

/-! ## Authentication: the split depends only on what the parent root commits to

`PTrie.refinedBy` (`NearSpec/TrieUpsertProofs.lean`): `t₁.refinedBy t₂` when `t₁` is `t₂` with some
subtrees replaced by their hash and some values by their `ValueRef`. Refinement preserves the root
hash (`PTrie.hashOf_refinedBy`). Below, the split is shown to commute with it: a split that succeeds
on a partial parent trie succeeds on any more-revealed version of it, with a refined child, hence the
same child root. `RefM` additionally tracks `memory_usage`, which the squash recomputes from the
retained children. -/

/-- Refinement that also keeps the stored `memory_usage`. -/
def RefM (a b : PTrie) : Prop := a.refinedBy b ∧ a.memD = b.memD

def OptRefM : Option PTrie → Option PTrie → Prop
  | none, none => True
  | some a, some b => RefM a b
  | _, _ => False

/-- A revealed (non-hash) node refines only a node of the same kind, with the same stored
`memory_usage`. -/
theorem memD_refinedBy {t₁ t₂ : PTrie} (h : t₁.refinedBy t₂) (hn : ∀ h0, t₁ ≠ .hash h0) :
    t₁.memD = t₂.memD := by
  cases t₁ with
  | hash h0 => exact absurd rfl (hn h0)
  | leaf k s m => cases t₂ <;> simp only [PTrie.refinedBy] at h; obtain ⟨_, rfl, _⟩ := h; rfl
  | ext k c m => cases t₂ <;> simp only [PTrie.refinedBy] at h; obtain ⟨_, rfl, _⟩ := h; rfl
  | branch v cs m => cases t₂ <;> simp only [PTrie.refinedBy] at h; obtain ⟨rfl, _, _⟩ := h; rfl

theorem extendChild_refinedBy {k : List Nat} {c₁ c₂ : PTrie} {r₁ : Option PTrie}
    (hr : c₁.refinedBy c₂) (h : extendChild k c₁ = some r₁) :
    ∃ r₂, extendChild k c₂ = some r₂ ∧ OptRefM r₁ r₂ := by
  cases c₁ with
  | hash _ => simp [extendChild] at h
  | leaf k2 s m =>
    cases c₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hs⟩ := hr
    simp only [extendChild, Option.some.injEq] at h; subst h
    refine ⟨_, rfl, ?_⟩
    simp only [OptRefM, RefM, PTrie.refinedBy, PTrie.memD, PTrie.mem?, hs.len, true_and]
    exact ⟨hs, trivial⟩
  | ext k2 c m =>
    cases c₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hc⟩ := hr
    simp only [extendChild, Option.some.injEq] at h; subst h
    exact ⟨_, rfl, ⟨by simp only [PTrie.refinedBy, true_and]; exact hc, rfl⟩⟩
  | branch v cs m =>
    cases c₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, hv, hcs⟩ := hr
    simp only [extendChild, Option.some.injEq] at h; subst h
    exact ⟨_, rfl, ⟨by simp only [PTrie.refinedBy, true_and]; exact ⟨hv, hcs⟩, rfl⟩⟩

/-- Refinement keeps the positions of the present children. -/
theorem Kids.present_refinedBy : ∀ (cs₁ cs₂ : Kids) (j : Nat), Kids.refinedBy cs₁ cs₂ →
    (Kids.present cs₁ j).map Prod.fst = (Kids.present cs₂ j).map Prod.fst
  | .nil, cs₂, j, h => by cases cs₂ <;> simp [Kids.refinedBy] at h; rfl
  | .none r, cs₂, j, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at h
    exact Kids.present_refinedBy r _ (j + 1) h
  | .some c r, cs₂, j, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at h
    simp only [Kids.present, List.map_cons, Kids.present_refinedBy r _ (j + 1) h.2]

theorem Kids.present_single_refinedBy : ∀ (cs₁ cs₂ : Kids) (j i : Nat) (c : PTrie),
    Kids.refinedBy cs₁ cs₂ → Kids.present cs₁ j = [(i, c)] →
    ∃ c₂, Kids.present cs₂ j = [(i, c₂)] ∧ c.refinedBy c₂
  | .nil, _, _, _, _, _, h => by simp [Kids.present] at h
  | .none r, cs₂, j, i, c, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    exact Kids.present_single_refinedBy r _ (j + 1) i c hr h
  | .some c0 r, cs₂, j, i, c, hr, h => by
    cases cs₂ with
    | some c0' r' =>
      simp only [Kids.refinedBy] at hr
      simp only [Kids.present, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, hnil⟩ := h
      have := Kids.present_refinedBy r r' (j + 1) hr.2
      rw [hnil] at this
      have h2 : Kids.present r' (j + 1) = [] := by
        cases hq : Kids.present r' (j + 1) with
        | nil => rfl
        | cons _ _ => rw [hq] at this; simp at this
      exact ⟨c0', by simp [Kids.present, h2], hr.1⟩
    | _ => simp [Kids.refinedBy] at hr

theorem squashBranch_refinedBy {v₁ v₂ : Option Slot} {cs₁ cs₂ : Kids} {m : Nat} {r₁ : Option PTrie}
    (hv : OptSlotRefines v₁ v₂) (hcs : Kids.refinedBy cs₁ cs₂) (h : squashBranch v₁ cs₁ m = some r₁) :
    ∃ r₂, squashBranch v₂ cs₂ m = some r₂ ∧ OptRefM r₁ r₂ := by
  have hpos := Kids.present_refinedBy cs₁ cs₂ 0 hcs
  have hbr : OptRefM (some (.branch v₁ cs₁ m)) (some (.branch v₂ cs₂ m)) :=
    ⟨by simp only [PTrie.refinedBy, true_and]; exact ⟨hv, hcs⟩, rfl⟩
  unfold squashBranch at h ⊢
  cases hp1 : Kids.present cs₁ 0 with
  | nil =>
    rw [hp1] at h hpos
    have hp2 : Kids.present cs₂ 0 = [] := by
      cases hq : Kids.present cs₂ 0 with
      | nil => rfl
      | cons _ _ => rw [hq] at hpos; simp at hpos
    rw [hp2]
    cases v₁ <;> cases v₂ <;> simp only [OptSlotRefines] at hv
    · simp only [Option.some.injEq] at h; subst h; exact ⟨none, rfl, trivial⟩
    · simp only [Option.some.injEq] at h; subst h
      refine ⟨_, rfl, ?_⟩
      simp only [OptRefM, RefM, PTrie.refinedBy, PTrie.memD, PTrie.mem?, hv.len, true_and]
      exact ⟨hv, trivial⟩
  | cons e es =>
    obtain ⟨i, c⟩ := e
    cases es with
    | nil =>
      obtain ⟨c₂, hp2, hc⟩ := Kids.present_single_refinedBy cs₁ cs₂ 0 i c hcs hp1
      rw [hp1] at h; rw [hp2]
      cases v₁ <;> cases v₂ <;> simp only [OptSlotRefines] at hv
      · exact extendChild_refinedBy hc h
      · simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, hbr⟩
    | cons e2 es2 =>
      rw [hp1] at h hpos
      cases hq : Kids.present cs₂ 0 with
      | nil => rw [hq] at hpos; simp at hpos
      | cons f fs =>
        cases fs with
        | nil => rw [hq] at hpos; simp at hpos
        | cons f2 fs2 =>
          simp only [Option.some.injEq] at h; subst h
          exact ⟨_, rfl, hbr⟩

def OptRef : Option PTrie → Option PTrie → Prop
  | none, none => True
  | some a, some b => a.refinedBy b
  | _, _ => False

theorem OptRefM.toRef : ∀ {a b : Option PTrie}, OptRefM a b → OptRef a b
  | none, none, _ => trivial
  | some _, some _, h => h.1
  | none, some _, h => h.elim
  | some _, none, h => h.elim

theorem retainSplitKids_some (ranges : List (List Nat × List Nat)) (key : List Nat) (i : Nat)
    (c : PTrie) (rest : Kids) (hc : ∀ h0, c ≠ .hash h0) :
    retainSplitKids key ranges i (.some c rest) =
      (retainSplit c (key ++ [i]) ranges).bind fun c' =>
        (retainSplitKids key ranges (i + 1) rest).bind fun (k, m) =>
          match c' with
          | some c' => some (.some c' k, c'.memD + m)
          | none => some (.none k, m) := by
  cases c with
  | hash h0 => exact absurd rfl (hc h0)
  | leaf _ _ _ => simp only [retainSplitKids]; rfl
  | ext _ _ _ => simp only [retainSplitKids]; rfl
  | branch _ _ _ => simp only [retainSplitKids]; rfl

/-- Same constructor under refinement. -/
theorem notHash_refinedBy {t₁ t₂ : PTrie} (h : t₁.refinedBy t₂) (hn : ∀ h0, t₁ ≠ .hash h0) :
    ∀ h0, t₂ ≠ .hash h0 := by
  intro h0 e; subst e
  cases t₁ with
  | hash h1 => exact hn h1 rfl
  | _ => simp [PTrie.refinedBy] at h

theorem refine_nodescend (ranges : List (List Nat × List Nat)) (t₁ t₂ : PTrie) (key : List Nat)
    (r₁ : Option PTrie) (hr : t₁.refinedBy t₂) (hd : retainDecision key ranges ≠ .descend)
    (h : retainSplit t₁ key ranges = some r₁) :
    ∃ r₂, retainSplit t₂ key ranges = some r₂ ∧ OptRef r₁ r₂ ∧
      ((∀ h0, t₁ ≠ .hash h0) → OptRefM r₁ r₂) := by
  rcases retainDecision_cases key ranges with hd' | hd' | hd'
  · rw [retainSplit_retainAll ranges t₁ key hd'] at h
    simp only [Option.some.injEq] at h; subst h
    exact ⟨_, retainSplit_retainAll ranges t₂ key hd', hr, fun hn => ⟨hr, memD_refinedBy hr hn⟩⟩
  · rw [retainSplit_discardAll ranges t₁ key hd'] at h
    simp only [Option.some.injEq] at h; subst h
    exact ⟨_, retainSplit_discardAll ranges t₂ key hd', trivial, fun _ => trivial⟩
  · exact absurd hd' hd

mutual

/-- **The split reads only authenticated data.** If the split succeeds on a partial parent trie,
it succeeds on any more-revealed version of the same trie, and the child it returns is refined by
the other's (so, by `PTrie.hashOf_refinedBy`, has the same root). For a revealed subtree the stored
`memory_usage` agrees too, which is what the squash's recomputation consumes. -/
theorem retainSplit_refinedBy (ranges : List (List Nat × List Nat)) :
    ∀ (t₁ t₂ : PTrie) (key : List Nat) (r₁ : Option PTrie), t₁.refinedBy t₂ →
      retainSplit t₁ key ranges = some r₁ →
      ∃ r₂, retainSplit t₂ key ranges = some r₂ ∧ OptRef r₁ r₂ ∧
        ((∀ h0, t₁ ≠ .hash h0) → OptRefM r₁ r₂)
  | .hash h0, t₂, key, r₁, hr, h => by
    by_cases hd : retainDecision key ranges = .descend
    case neg => exact refine_nodescend ranges _ t₂ key r₁ hr hd h
    rw [retainSplit_hash ranges h0 key hd] at h; cases h
  | .leaf k s m, t₂, key, r₁, hr, h => by
    by_cases hd : retainDecision key ranges = .descend
    case neg => exact refine_nodescend ranges _ t₂ key r₁ hr hd h
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hs⟩ := hr
    rename_i s₂
    rw [retainSplit_leaf ranges _ s _ key hd] at h
    simp only [Option.some.injEq] at h; subst h
    refine ⟨_, retainSplit_leaf ranges _ _ _ key hd, ?_⟩
    have hl : OptRefM (some (PTrie.leaf k s m)) (some (PTrie.leaf k s₂ m)) :=
      ⟨by simp only [PTrie.refinedBy, true_and]; exact hs, rfl⟩
    split
    · exact ⟨hl.toRef, fun _ => hl⟩
    · exact ⟨trivial, fun _ => trivial⟩
  | .ext k c m, t₂, key, r₁, hr, h => by
    by_cases hd : retainDecision key ranges = .descend
    case neg => exact refine_nodescend ranges _ t₂ key r₁ hr hd h
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hc⟩ := hr
    rename_i c₂
    by_cases hch : ∃ h0, c = .hash h0
    · obtain ⟨h0, rfl⟩ := hch
      unfold retainSplit at h; rw [hd] at h; cases h
    have hcn : ∀ h0, c ≠ .hash h0 := fun h0 e => hch ⟨h0, e⟩
    have hcn2 := notHash_refinedBy hc hcn
    rw [retainSplit_ext ranges k c _ key hd hcn] at h
    rw [retainSplit_ext ranges k c₂ _ key hd hcn2]
    cases hcr : retainSplit c (key ++ k) ranges with
    | none => rw [hcr] at h; cases h
    | some c'' =>
      rw [hcr] at h
      obtain ⟨c''₂, hcr2, _, hm⟩ := retainSplit_refinedBy ranges c c₂ (key ++ k) c'' hc hcr
      have hm := hm hcn
      rw [hcr2]
      cases c'' with
      | none =>
        cases c''₂ with
        | some _ => exact hm.elim
        | none =>
          simp only [Option.bind_some, Option.some.injEq] at h; subst h
          exact ⟨none, rfl, trivial, fun _ => trivial⟩
      | some c' =>
        cases c''₂ with
        | none => exact hm.elim
        | some c'₂ =>
          simp only [Option.bind_some] at h ⊢
          obtain ⟨r₂, he, hrm⟩ := extendChild_refinedBy hm.1 h
          exact ⟨r₂, he, hrm.toRef, fun _ => hrm⟩
  | .branch v cs m, t₂, key, r₁, hr, h => by
    by_cases hd : retainDecision key ranges = .descend
    case neg => exact refine_nodescend ranges _ t₂ key r₁ hr hd h
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, hv, hcs⟩ := hr
    rename_i v₂ cs₂
    rw [retainSplit_branch ranges v cs _ key hd] at h
    rw [retainSplit_branch ranges v₂ cs₂ _ key hd]
    cases hk : retainSplitKids key ranges 0 cs with
    | none => rw [hk] at h; cases h
    | some q =>
      obtain ⟨k₁, m'⟩ := q
      rw [hk] at h
      obtain ⟨k₂, hk2, hkr⟩ := retainSplitKids_refinedBy ranges cs cs₂ key 0 k₁ m' hcs hk
      rw [hk2]
      simp only [Option.bind_some] at h ⊢
      have hv' : OptSlotRefines (if ranges.any (fun r => inRange key r) then v else none)
          (if ranges.any (fun r => inRange key r) then v₂ else none) := by
        split
        · exact hv
        · trivial
      have hown : (match (if ranges.any (fun r => inRange key r) then v else none) with
            | some s => NearSpec.valueMem s.len | none => 0) =
          (match (if ranges.any (fun r => inRange key r) then v₂ else none) with
            | some s => NearSpec.valueMem s.len | none => 0) := by
        revert hv'
        generalize (if ranges.any (fun r => inRange key r) then v else none) = a
        generalize (if ranges.any (fun r => inRange key r) then v₂ else none) = b
        intro hv'
        cases a <;> cases b <;> simp only [OptSlotRefines] at hv' <;> first | rfl | simp [hv'.len]
      rw [hown] at h
      obtain ⟨r₂, he, hrm⟩ := squashBranch_refinedBy hv' hkr h
      exact ⟨r₂, he, hrm.toRef, fun _ => hrm⟩

theorem retainSplitKids_refinedBy (ranges : List (List Nat × List Nat)) :
    ∀ (cs₁ cs₂ : Kids) (key : List Nat) (i : Nat) (k₁ : Kids) (m : Nat), Kids.refinedBy cs₁ cs₂ →
      retainSplitKids key ranges i cs₁ = some (k₁, m) →
      ∃ k₂, retainSplitKids key ranges i cs₂ = some (k₂, m) ∧ Kids.refinedBy k₁ k₂
  | .nil, cs₂, key, i, k₁, m, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    simp only [retainSplitKids, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.nil, rfl, trivial⟩
  | .none rest, cs₂, key, i, k₁, m, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    rename_i rest₂
    simp only [retainSplitKids] at h ⊢
    cases hq : retainSplitKids key ranges (i + 1) rest with
    | none => rw [hq] at h; cases h
    | some q =>
      obtain ⟨k', m2⟩ := q
      rw [hq] at h
      obtain ⟨k₂, hq2, hkr⟩ := retainSplitKids_refinedBy ranges rest rest₂ key (i + 1) k' m2 hr hq
      rw [hq2]
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, ⟨rfl, rfl⟩, hkr⟩
  | .some c rest, cs₂, key, i, k₁, m, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    rename_i c₂ rest₂
    obtain ⟨hc, hrest⟩ := hr
    by_cases hch : ∃ h0, c = .hash h0
    · obtain ⟨h0, rfl⟩ := hch
      simp [retainSplitKids] at h
    have hcn : ∀ h0, c ≠ .hash h0 := fun h0 e => hch ⟨h0, e⟩
    have hcn2 := notHash_refinedBy hc hcn
    rw [retainSplitKids_some ranges key i c rest hcn] at h
    rw [retainSplitKids_some ranges key i c₂ rest₂ hcn2]
    cases hcr : retainSplit c (key ++ [i]) ranges with
    | none => rw [hcr] at h; cases h
    | some c'' =>
      rw [hcr] at h
      obtain ⟨c''₂, hcr2, _, hm⟩ := retainSplit_refinedBy ranges c c₂ (key ++ [i]) c'' hc hcr
      have hm := hm hcn
      rw [hcr2]
      cases hq : retainSplitKids key ranges (i + 1) rest with
      | none => rw [hq] at h; cases c'' <;> cases h
      | some q =>
        obtain ⟨k', m2⟩ := q
        rw [hq] at h
        obtain ⟨k₂, hq2, hkr⟩ := retainSplitKids_refinedBy ranges rest rest₂ key (i + 1) k' m2 hrest hq
        rw [hq2]
        cases c'' with
        | none =>
          cases c''₂ with
          | some _ => exact hm.elim
          | none =>
            simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h ⊢
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨_, ⟨rfl, rfl⟩, hkr⟩
        | some c' =>
          cases c''₂ with
          | none => exact hm.elim
          | some c'₂ =>
            simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h ⊢
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨_, ⟨rfl, by rw [hm.2]⟩, ⟨hm.1, hkr⟩⟩

end

/-- **The child state root is authenticated by the parent root.** If the validator's split succeeds
on a partial parent trie `t₁`, it succeeds with the same child root on every `t₂` revealing more of
the same trie. With `Logged.hashOf_revealAll` (`(revealAll s f h).hashOf = h` on a hash-consistent
store), the root `checkReshardCore` compares with the witness's child post-state root is fixed by the
authenticated parent root and the nodes the split reads. -/
theorem splitRootE_refinedBy (t₁ t₂ : PTrie) (boundary : Bytes) (mode : RetainMode) (root : Bytes)
    (hr : t₁.refinedBy t₂) (h : splitRootE t₁ boundary mode = .ok root) :
    splitRootE t₂ boundary mode = .ok root := by
  unfold splitRootE at h ⊢
  cases h1 : retainSplit t₁ [] (intervalsToNibbles (boundaryAccountToIntervals boundary mode)) with
  | none => rw [h1] at h; cases h
  | some r₁ =>
    rw [h1] at h
    simp only [Except.ok.injEq] at h; subst h
    obtain ⟨r₂, h2, href, _⟩ := retainSplit_refinedBy _ t₁ t₂ [] r₁ hr h1
    rw [h2]
    cases r₁ <;> cases r₂ <;> simp only [OptRef] at href
    · rfl
    · simp only [rootHash]; rw [PTrie.hashOf_refinedBy _ _ href]

end NearSpecV3
