import StateM5a.SerInj

/-!
# StateM5a.Refine — delete refinement, and the rows' trie refines the witness trie

* **`PTrie.del` commutes with refinement** (`del_refinedBy`, the analogue of the spec's
  `PTrie.upsert_refinedBy`): if `t₁.refinedBy t₂` and `t₁.del key = some (b, o₁)`, then
  `t₂.del key = some (b, o₂)` with `o₁` refining `o₂` (so the same root hash, `rootHash`).
  Through `squashBranch` (the remaining children list refines elementwise) and `extendChild`.
  `dchain_witness`: the delete walk's result on any trie the rows' trie refines.
* **The rows' trie refines the witness trie** (`linked_refinedBy`): the rows of a walk reveal a
  trie `t₁` in which every revealed node is a row's node (`Shallow` up to the on-path child),
  linked by hashes to the witness trie `t₂` at the same position (`Linked`: the row node, with its
  on-path child replaced by that child's hash stub, hashes to the witness node).  By induction
  along the path, with `SerInj.nodeSerInj` at every node and `Sha256CR` the only premise,
  `t₁.refinedBy t₂`.  `fchain_witness`, `uchain_witness`, `dchain_witness` then give the spec's
  answer / new root on `t₂`.
-/

namespace StateM5a.Refine

open NearSpec NearSpecV3.D2 StateM5a.Walk StateM5a.SerInj

/-! ## Refinement of optional results -/

def OptRefines : Option PTrie → Option PTrie → Prop
  | none, none => True
  | some a, some b => a.refinedBy b
  | _, _ => False

/-- Delete results: same `deleted` flag, the remaining subtree refines. -/
def DelRefines (r₁ r₂ : Bool × Option PTrie) : Prop := r₁.1 = r₂.1 ∧ OptRefines r₁.2 r₂.2

theorem OptRefines.rootHash {o₁ o₂ : Option PTrie} (h : OptRefines o₁ o₂) : rootHash o₁ = rootHash o₂ := by
  cases o₁ <;> cases o₂ <;> simp only [OptRefines] at h
  · rfl
  · exact PTrie.hashOf_refinedBy _ _ h

/-! ## `extendChild`, `squashBranch` -/

theorem extendChild_refinedBy (k : List Nat) {c₁ c₂ : PTrie} (hr : c₁.refinedBy c₂) {o₁ : Option PTrie}
    (h : extendChild k c₁ = some o₁) : ∃ o₂, extendChild k c₂ = some o₂ ∧ OptRefines o₁ o₂ := by
  cases c₁ with
  | hash => simp [extendChild] at h
  | leaf k2 s m =>
    cases c₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hs⟩ := hr
    simp only [extendChild, Option.some.injEq] at h; subst h
    exact ⟨_, rfl, by simp [OptRefines, PTrie.refinedBy, hs, hs.len]⟩
  | ext k2 c m =>
    cases c₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hc⟩ := hr
    simp only [extendChild, Option.some.injEq] at h; subst h
    exact ⟨_, rfl, by simp [OptRefines, PTrie.refinedBy, hc]⟩
  | branch v cs m =>
    cases c₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, hv, hcs⟩ := hr
    simp only [extendChild, Option.some.injEq] at h; subst h
    exact ⟨_, rfl, by simp [OptRefines, PTrie.refinedBy, hv, hcs]⟩

/-- Children lists that refine elementwise (same indices). -/
def PresRel : List (Nat × PTrie) → List (Nat × PTrie) → Prop
  | [], [] => True
  | (i, c) :: r, (j, d) :: s => i = j ∧ c.refinedBy d ∧ PresRel r s
  | _, _ => False

theorem present_refinedBy : ∀ (cs₁ cs₂ : Kids) (i : Nat), Kids.refinedBy cs₁ cs₂ →
    PresRel (Kids.present cs₁ i) (Kids.present cs₂ i)
  | .nil, cs₂, i, hr => by
    cases cs₂ <;> simp [Kids.refinedBy] at hr; simp [Kids.present, PresRel]
  | .none r, cs₂, i, hr => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    all_goals first | contradiction | exact present_refinedBy r _ (i + 1) hr
  | .some c r, cs₂, i, hr => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    all_goals first | contradiction |
      exact ⟨rfl, hr.1, present_refinedBy r _ (i + 1) hr.2⟩

theorem squashBranch_refinedBy {v₁ v₂ : Option Slot} {cs₁ cs₂ : Kids} (m : Nat)
    (hv : OptSlotRefines v₁ v₂) (hcs : Kids.refinedBy cs₁ cs₂) {o₁ : Option PTrie}
    (h : squashBranch v₁ cs₁ m = some o₁) :
    ∃ o₂, squashBranch v₂ cs₂ m = some o₂ ∧ OptRefines o₁ o₂ := by
  have hp := present_refinedBy cs₁ cs₂ 0 hcs
  have hbr : OptRefines (some (.branch v₁ cs₁ m)) (some (.branch v₂ cs₂ m)) := by
    simp [OptRefines, PTrie.refinedBy, hv, hcs]
  unfold squashBranch at h ⊢
  generalize Kids.present cs₁ 0 = l₁ at h hp
  generalize Kids.present cs₂ 0 = l₂ at hp
  cases v₁ <;> cases v₂ <;> simp only [OptSlotRefines] at hv
  · -- no value
    match l₁, l₂, hp with
    | [], [], _ =>
      simp only [Option.some.injEq] at h; subst h; exact ⟨none, rfl, trivial⟩
    | [(i, c)], [(j, d)], hp =>
      obtain ⟨rfl, hcd, -⟩ := hp
      exact extendChild_refinedBy [i] hcd h
    | (i, c) :: (i', c') :: r, (j, d) :: (j', d') :: s, _ =>
      simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, hbr⟩
    | [], _ :: _, hp => simp [PresRel] at hp
    | _ :: _, [], hp => simp [PresRel] at hp
    | [_], _ :: _ :: _, hp => simp [PresRel] at hp
    | _ :: _ :: _, [_], hp => simp [PresRel] at hp
  · -- a value
    rename_i s₁ s₂
    match l₁, l₂, hp with
    | [], [], _ =>
      simp only [Option.some.injEq] at h; subst h
      exact ⟨_, rfl, by simp [OptRefines, PTrie.refinedBy, hv, hv.len]⟩
    | [(i, c)], [(j, d)], _ =>
      simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, hbr⟩
    | (i, c) :: (i', c') :: r, (j, d) :: (j', d') :: s, _ =>
      simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, hbr⟩
    | [], _ :: _, hp => simp [PresRel] at hp
    | _ :: _, [], hp => simp [PresRel] at hp
    | [_], _ :: _ :: _, hp => simp [PresRel] at hp
    | _ :: _ :: _, [_], hp => simp [PresRel] at hp

/-! ## Delete results are revealed nodes -/

theorem extendChild_some {k : List Nat} {c : PTrie} {o : PTrie} (h : extendChild k c = some (some o)) :
    o.mem?.isSome = true := by
  cases c <;> simp [extendChild] at h <;> subst h <;> rfl

theorem squashBranch_some {v : Option Slot} {cs : Kids} {m : Nat} {o : PTrie}
    (h : squashBranch v cs m = some (some o)) : o.mem?.isSome = true := by
  unfold squashBranch at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · exact extendChild_some h
  · simp only [Option.some.injEq] at h; subst h; rfl

theorem del_some : ∀ {t : PTrie} {key : List Nat} {b : Bool} {o : PTrie},
    t.del key = some (b, some o) → o.mem?.isSome = true
  | .hash _, _, _, _, h => by simp [PTrie.del] at h
  | .leaf k s m, key, b, o, h => by
    simp only [PTrie.del] at h
    split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq,
      and_false] at h
    obtain ⟨-, rfl⟩ := h; rfl
  | .ext k c m, key, b, o, h => by
    simp only [PTrie.del] at h
    split at h
    · split at h
      · split at h
        · simp at h
        · rename_i c' _
          cases he : extendChild k c' with
          | none => simp [he] at h
          | some r =>
            simp only [he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact extendChild_some he
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl
      · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl
  | .branch v cs m, [], b, o, h => by
    simp only [PTrie.del] at h
    cases v with
    | none => simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl
    | some s =>
      simp only at h
      cases he : squashBranch none cs (m - valueMem s.len) with
      | none => simp [he] at h
      | some r =>
        simp only [he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact squashBranch_some he
  | .branch v cs m, n :: rest, b, o, h => by
    simp only [PTrie.del] at h
    split at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl
    · rename_i cs' old new _
      cases he : squashBranch v cs' (m - old + new) with
      | none => simp [he] at h
      | some r =>
        simp only [he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact squashBranch_some he

/-! ## `del` commutes with refinement -/

/-- Results of `Kids.delAt`. -/
def KDelRefines : Option (Kids × Nat × Nat) → Option (Kids × Nat × Nat) → Prop
  | none, none => True
  | some (k₁, a₁, b₁), some (k₂, a₂, b₂) => Kids.refinedBy k₁ k₂ ∧ a₁ = a₂ ∧ b₁ = b₂
  | _, _ => False

mutual
theorem del_refinedBy : ∀ (t₁ t₂ : PTrie) (key : List Nat) (r₁ : Bool × Option PTrie),
    t₁.refinedBy t₂ → t₁.del key = some r₁ → ∃ r₂, t₂.del key = some r₂ ∧ DelRefines r₁ r₂
  | .hash _, _, _, _, _, h => by simp [PTrie.del] at h
  | .leaf k s m, t₂, key, r₁, hr, h => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hs⟩ := hr
    simp only [PTrie.del] at h ⊢
    by_cases e : k = key
    · simp only [e, ↓reduceIte, Option.some.injEq] at h ⊢; subst h
      exact ⟨_, rfl, rfl, trivial⟩
    · simp only [e, ↓reduceIte, Option.some.injEq] at h ⊢; subst h
      exact ⟨_, rfl, rfl, by simp [OptRefines, PTrie.refinedBy, hs]⟩
  | .ext k c m, t₂, key, r₁, hr, h => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    rename_i k₂ c₂ m₂
    obtain ⟨rfl, rfl, hc⟩ := hr
    have hext : OptRefines (some (.ext k c m)) (some (.ext k c₂ m)) := by
      simp [OptRefines, PTrie.refinedBy, hc]
    simp only [PTrie.del] at h ⊢
    by_cases hp : isPrefix k key = true
    · simp only [hp, ↓reduceIte] at h ⊢
      cases hm : c.mem? with
      | none => simp [hm] at h
      | some cm =>
        have hm₂ := refinedBy_mem hc hm
        cases hd : c.del (key.drop k.length) with
        | none => simp [hm, hd] at h
        | some rc =>
          obtain ⟨rc₂, hd₂, hb, ho⟩ := del_refinedBy c c₂ _ rc hc hd
          obtain ⟨b, o⟩ := rc
          obtain ⟨b₂, o₂⟩ := rc₂
          simp only at hb ho; subst hb
          rw [hm₂, hd₂]
          simp only [hm, hd] at h
          cases b with
          | false =>
            simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, rfl, hext⟩
          | true =>
            cases o <;> cases o₂ <;> simp only [OptRefines] at ho
            · simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, rfl, trivial⟩
            · rename_i c' c₂'
              cases he : extendChild k c' with
              | none => simp [he] at h
              | some x =>
                simp only [he, Option.map_some, Option.some.injEq] at h; subst h
                obtain ⟨x₂, he₂, hx⟩ := extendChild_refinedBy k ho he
                exact ⟨(true, x₂), by simp [he₂], rfl, hx⟩
    · have hp' : isPrefix k key = false := by simpa using hp
      simp only [hp', Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h ⊢; subst h
      exact ⟨_, rfl, rfl, hext⟩
  | .branch v cs m, t₂, [], r₁, hr, h => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    rename_i v₂ cs₂ m₂
    obtain ⟨rfl, hv, hcs⟩ := hr
    simp only [PTrie.del] at h ⊢
    cases v <;> cases v₂ <;> simp only [OptSlotRefines] at hv
    · simp only [Option.some.injEq] at h; subst h
      exact ⟨_, rfl, rfl, by simp [OptRefines, PTrie.refinedBy, hcs, OptSlotRefines]⟩
    · rename_i s₁ s₂
      simp only at h ⊢
      rw [← hv.len]
      cases he : squashBranch none cs (m - valueMem s₁.len) with
      | none => simp [he] at h
      | some x =>
        simp only [he, Option.map_some, Option.some.injEq] at h; subst h
        obtain ⟨x₂, he₂, hx⟩ := squashBranch_refinedBy (v₂ := none) _ (by simp [OptSlotRefines]) hcs he
        exact ⟨(true, x₂), by simp [he₂], rfl, hx⟩
  | .branch v cs m, t₂, n :: rest, r₁, hr, h => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    rename_i v₂ cs₂ m₂
    obtain ⟨rfl, hv, hcs⟩ := hr
    simp only [PTrie.del] at h ⊢
    cases hd : Kids.delAt cs n rest with
    | none => simp [hd] at h
    | some o =>
      obtain ⟨o₂, hd₂, ho⟩ := kids_delAt_refinedBy cs cs₂ n rest o hcs hd
      rw [hd₂]
      cases o <;> cases o₂ <;> simp only [KDelRefines] at ho
      · simp only [hd, Option.some.injEq] at h; subst h
        exact ⟨_, rfl, rfl, by simp [OptRefines, PTrie.refinedBy, hcs, hv]⟩
      · rename_i x₁ x₂
        obtain ⟨cs', a, b⟩ := x₁
        obtain ⟨cs₂', a₂, b₂⟩ := x₂
        obtain ⟨hk, rfl, rfl⟩ := ho
        simp only [hd] at h ⊢
        cases he : squashBranch v cs' (m - a + b) with
        | none => simp [he] at h
        | some x =>
          simp only [he, Option.map_some, Option.some.injEq] at h; subst h
          obtain ⟨y, he₂, hy⟩ := squashBranch_refinedBy _ hv hk he
          exact ⟨(true, y), by simp [he₂], rfl, hy⟩

theorem kids_delAt_refinedBy : ∀ (cs₁ cs₂ : Kids) (n : Nat) (key : List Nat)
    (o₁ : Option (Kids × Nat × Nat)), Kids.refinedBy cs₁ cs₂ → Kids.delAt cs₁ n key = some o₁ →
    ∃ o₂, Kids.delAt cs₂ n key = some o₂ ∧ KDelRefines o₁ o₂
  | .nil, cs₂, n, key, o₁, hr, h => by
    cases cs₂ <;> simp [Kids.refinedBy] at hr
    simp only [Kids.delAt, Option.some.injEq] at h ⊢; subst h; exact ⟨_, rfl, trivial⟩
  | .none r, cs₂, 0, key, o₁, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    all_goals first | contradiction | skip
    simp only [Kids.delAt, Option.some.injEq] at h ⊢; subst h; exact ⟨_, rfl, trivial⟩
  | .some c r, cs₂, 0, key, o₁, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    all_goals first | contradiction | skip
    rename_i c₂ r₂
    simp only [Kids.delAt] at h ⊢
    cases hm : c.mem? with
    | none => simp [hm] at h
    | some cm =>
      rw [refinedBy_mem hr.1 hm]
      cases hd : c.del key with
      | none => simp [hm, hd] at h
      | some rc =>
        obtain ⟨rc₂, hd₂, hb, ho⟩ := del_refinedBy c c₂ _ rc hr.1 hd
        obtain ⟨b, oc⟩ := rc
        obtain ⟨b₂, oc₂⟩ := rc₂
        simp only at hb ho; subst hb
        rw [hd₂]
        simp only [hm, hd] at h
        cases b with
        | false => simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, trivial⟩
        | true =>
          simp only [Option.some.injEq] at h; subst h
          refine ⟨_, rfl, ?_⟩
          cases oc <;> cases oc₂ <;> simp only [OptRefines] at ho
          · simp [KDelRefines, Kids.refinedBy, hr.2]
          · rename_i c' c₂'
            have hmd := refinedBy_memD ho (del_some hd)
            simp [KDelRefines, Kids.refinedBy, hr.2, ho, hmd]
  | .none r, cs₂, i + 1, key, o₁, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    all_goals first | contradiction | skip
    rename_i r₂
    simp only [Kids.delAt] at h ⊢
    cases hd : Kids.delAt r i key with
    | none => simp [hd] at h
    | some x =>
      obtain ⟨x₂, hd₂, hx⟩ := kids_delAt_refinedBy r r₂ i key x hr hd
      simp only [hd, Option.map_some, Option.some.injEq] at h; subst h
      refine ⟨_, by rw [hd₂]; rfl, ?_⟩
      cases x <;> cases x₂ <;> simp only [KDelRefines] at hx
      · simp [KDelRefines]
      · rename_i y₁ y₂
        obtain ⟨k₁, a₁, b₁⟩ := y₁; obtain ⟨k₂, a₂, b₂⟩ := y₂
        simp only at hx; simp [KDelRefines, Kids.refinedBy, hx]
  | .some c r, cs₂, i + 1, key, o₁, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    all_goals first | contradiction | skip
    rename_i c₂ r₂
    simp only [Kids.delAt] at h ⊢
    cases hd : Kids.delAt r i key with
    | none => simp [hd] at h
    | some x =>
      obtain ⟨x₂, hd₂, hx⟩ := kids_delAt_refinedBy r r₂ i key x hr.2 hd
      simp only [hd, Option.map_some, Option.some.injEq] at h; subst h
      refine ⟨_, by rw [hd₂]; rfl, ?_⟩
      cases x <;> cases x₂ <;> simp only [KDelRefines] at hx
      · simp [KDelRefines]
      · rename_i y₁ y₂
        obtain ⟨k₁, a₁, b₁⟩ := y₁; obtain ⟨k₂, a₂, b₂⟩ := y₂
        simp only at hx; simp [KDelRefines, Kids.refinedBy, hx, hr.1]
end

/-- **Delete walk on the witness trie.**  On any trie the rows' trie refines, the spec's `del`
gives the same `deleted` flag and a result with the same root hash as the rows compute. -/
theorem dchain_witness {t₁ : PTrie} {key : List Nat} {r₁ : Bool × Option PTrie} (h : DChain t₁ key r₁)
    (t₂ : PTrie) (hr : t₁.refinedBy t₂) :
    ∃ r₂, t₂.del key = some r₂ ∧ r₂.1 = r₁.1 ∧ rootHash r₂.2 = rootHash r₁.2 := by
  obtain ⟨r₂, hd, hb, ho⟩ := del_refinedBy t₁ t₂ key r₁ hr (dchain_sound h)
  exact ⟨r₂, hd, hb.symm, (OptRefines.rootHash ho).symm⟩

/-- One committed delete on the witness trie (`applyChange`): the same post-root. -/
theorem change_del_witness {t₁ t₁' : PTrie} {k : Bytes} {b : Bool} (h : DChain t₁ (nibbles k) (b, some t₁'))
    (t₂ : PTrie) (hr : t₁.refinedBy t₂) :
    ∃ o₂, applyChange (some t₂) k none = some o₂ ∧ rootHash o₂ = t₁'.hashOf := by
  obtain ⟨r₂, hd, -, hh⟩ := dchain_witness h t₂ hr
  exact ⟨r₂.2, by simp [applyChange, hd], hh⟩


/-! ## `findRef` commutes with refinement -/

mutual
theorem findRef_refinedBy : ∀ (t₁ t₂ : PTrie) (key : List Nat) (a : Option Slot),
    t₁.refinedBy t₂ → t₁.findRef key = some a → ∃ a₂, t₂.findRef key = some a₂ ∧ OptSlotRefines a a₂
  | .hash _, _, _, _, _, h => by simp [PTrie.findRef] at h
  | .leaf k s m, t₂, key, a, hr, h => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hs⟩ := hr
    simp only [PTrie.findRef] at h ⊢
    by_cases e : k = key
    · simp only [e, ↓reduceIte, Option.some.injEq] at h ⊢; subst h; exact ⟨_, rfl, hs⟩
    · simp only [e, ↓reduceIte, Option.some.injEq] at h ⊢; subst h; exact ⟨_, rfl, trivial⟩
  | .ext k c m, t₂, key, a, hr, h => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hc⟩ := hr
    simp only [PTrie.findRef] at h ⊢
    by_cases hp : isPrefix k key = true
    · simp only [hp, ↓reduceIte] at h ⊢; exact findRef_refinedBy c _ _ a hc h
    · have hp' : isPrefix k key = false := by simpa using hp
      simp only [hp', Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h ⊢; subst h
      exact ⟨_, rfl, trivial⟩
  | .branch v cs m, t₂, [], a, hr, h => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, hv, -⟩ := hr
    simp only [PTrie.findRef, Option.some.injEq] at h ⊢; subst h; exact ⟨_, rfl, hv⟩
  | .branch v cs m, t₂, n :: rest, a, hr, h => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, -, hcs⟩ := hr
    simp only [PTrie.findRef] at h ⊢
    exact kids_findRef_refinedBy cs _ n rest a hcs h
theorem kids_findRef_refinedBy : ∀ (cs₁ cs₂ : Kids) (n : Nat) (key : List Nat) (a : Option Slot),
    Kids.refinedBy cs₁ cs₂ → Kids.findRef cs₁ n key = some a →
    ∃ a₂, Kids.findRef cs₂ n key = some a₂ ∧ OptSlotRefines a a₂
  | .nil, cs₂, n, _, a, hr, h => by
    cases cs₂ <;> simp [Kids.refinedBy] at hr
    cases n <;> simp only [Kids.findRef, Option.some.injEq] at h ⊢ <;> subst h <;> exact ⟨_, rfl, trivial⟩
  | .none r, cs₂, 0, _, a, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    all_goals first | contradiction | skip
    simp only [Kids.findRef, Option.some.injEq] at h ⊢; subst h; exact ⟨_, rfl, trivial⟩
  | .some c r, cs₂, 0, key, a, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    all_goals first | contradiction | skip
    simp only [Kids.findRef] at h ⊢; exact findRef_refinedBy c _ key a hr.1 h
  | .none r, cs₂, i + 1, key, a, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    all_goals first | contradiction | skip
    simp only [Kids.findRef] at h ⊢; exact kids_findRef_refinedBy r _ i key a hr h
  | .some c r, cs₂, i + 1, key, a, hr, h => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    all_goals first | contradiction | skip
    simp only [Kids.findRef] at h ⊢; exact kids_findRef_refinedBy r _ i key a hr.2 h
end

/-! ## The rows' trie refines the full trie

The rows' trie `t₁` holds `ValueRef`s only (`RefSlots`); its revealed nodes are linked by hashes
(a revealed child's hash is what its parent serializes, so `t₁.hashOf` is the root the rows
compute).  `T` is a fully revealed (`Revealed`) well-formed trie: the true state trie, which the
spec's partial trie also refines. -/

mutual
def RefSlots : PTrie → Prop
  | .hash _ => True
  | .leaf _ s _ => ∃ len h, s = .ref len h
  | .ext _ c _ => RefSlots c
  | .branch v cs _ => (∀ s, v = some s → ∃ len h, s = .ref len h) ∧ KRefSlots cs
def KRefSlots : Kids → Prop
  | .nil => True
  | .none r => KRefSlots r
  | .some c r => RefSlots c ∧ KRefSlots r
end

mutual
def Revealed : PTrie → Prop
  | .hash _ => False
  | .leaf .. => True
  | .ext _ c _ => Revealed c
  | .branch _ cs _ => KRevealed cs
def KRevealed : Kids → Prop
  | .nil => True
  | .none r => KRevealed r
  | .some c r => Revealed c ∧ KRevealed r
end

/-- Children replaced by their hash stubs. -/
def stubs : Kids → Kids
  | .nil => .nil
  | .none r => .none (stubs r)
  | .some c r => .some (.hash c.hashOf) (stubs r)

/-- A node with its children replaced by hash stubs: what one row holds. -/
def shallow : PTrie → PTrie
  | .hash h => .hash h
  | .leaf k s m => .leaf k s m
  | .ext k c m => .ext k (.hash c.hashOf) m
  | .branch v cs m => .branch v (stubs cs) m

theorem stubs_hash : ∀ (cs : Kids) (i : Nat),
    kidsBitmap (stubs cs) i = kidsBitmap cs i ∧ Kids.hashes (stubs cs) = Kids.hashes cs
  | .nil, i => by simp [stubs]
  | .none r, i => by simp [stubs, kidsBitmap, Kids.hashes, stubs_hash r (i + 1)]
  | .some c r, i => by simp [stubs, kidsBitmap, Kids.hashes, PTrie.hashOf, stubs_hash r (i + 1)]

theorem shallow_hashOf (t : PTrie) : (shallow t).hashOf = t.hashOf := by
  cases t with
  | hash => rfl
  | leaf => rfl
  | ext k c m => simp [shallow, PTrie.hashOf]
  | branch v cs m => cases v <;> simp [shallow, PTrie.hashOf, stubs_hash cs 0]

theorem stubs_wf : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true → Kids.wf (stubs cs) n = true
  | .nil, n, h => by simpa [stubs] using h
  | .none r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h
    simp only [stubs, Kids.wf, Bool.and_eq_true]; exact ⟨h.1, stubs_wf r _ h.2⟩
  | .some c r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h
    simp only [stubs, Kids.wf, Bool.and_eq_true, PTrie.wf, hashOf_length c h.1.2, beq_self_eq_true,
      and_true]
    exact ⟨h.1.1, stubs_wf r _ h.2⟩

theorem stubs_at : ∀ (cs : Kids) (j : Nat) (c : PTrie), Kids.at (stubs cs) j = some c → ∃ h, c = .hash h
  | .nil, j, c, h => by simp [stubs, Kids.at] at h
  | .none r, 0, c, h => by simp [stubs, Kids.at] at h
  | .some x r, 0, c, h => by simp only [stubs, Kids.at, Option.some.injEq] at h; exact ⟨_, h.symm⟩
  | .none r, j + 1, c, h => by simp only [stubs, Kids.at] at h; exact stubs_at r j c h
  | .some x r, j + 1, c, h => by simp only [stubs, Kids.at] at h; exact stubs_at r j c h

mutual
/-- **The rows' trie refines the full trie.**  Every revealed node is identified with the full
trie's node at the same position by `nodeSerInj` and `Sha256CR`, from the root hash down. -/
theorem rows_refinedBy (hCR : Sha256CR) : ∀ (t₁ T : PTrie), t₁.wf = true → T.wf = true →
    RefSlots t₁ → Revealed T → t₁.hashOf = T.hashOf → t₁.refinedBy T
  | .hash h, T, _, _, _, _, hh => by simpa [PTrie.refinedBy, PTrie.hashOf] using hh
  | .leaf k s m, T, hw, hW, hs, hR, hh => by
    have hT : ∀ h, T ≠ .hash h := by intro h e; subst e; simp [Revealed] at hR
    exact refinedBy_of_hash' hCR hw hW (by simp) hT hs hh
  | .ext k c m, T, hw, hW, hs, hR, hh => by
    have hT : ∀ h, T ≠ .hash h := by intro h e; subst e; simp [Revealed] at hR
    have hw' : (shallow (.ext k c m)).wf = true := by
      simp only [PTrie.wf, Bool.and_eq_true, shallow] at hw ⊢
      exact ⟨⟨⟨hw.1.1.1, by simp [hashOf_length c hw.1.1.2]⟩, hw.1.2⟩, hw.2⟩
    have hr := refinedBy_of_hash' hCR hw' hW (by simp [shallow]) hT ⟨_, rfl⟩
      (by rw [shallow_hashOf]; exact hh)
    cases T with
    | ext k₂ c₂ m₂ =>
      simp only [shallow, PTrie.refinedBy] at hr
      obtain ⟨rfl, rfl, hc⟩ := hr
      simp only [PTrie.wf, Bool.and_eq_true] at hw hW
      simp only [PTrie.refinedBy, true_and]
      exact (rows_refinedBy hCR c c₂ hw.1.1.2 hW.1.1.2 hs hR hc)
    | _ => simp [shallow, PTrie.refinedBy] at hr
  | .branch v cs m, T, hw, hW, hs, hR, hh => by
    have hT : ∀ h, T ≠ .hash h := by intro h e; subst e; simp [Revealed] at hR
    have hw' : (shallow (.branch v cs m)).wf = true := by
      simp only [PTrie.wf, Bool.and_eq_true, shallow] at hw ⊢
      exact ⟨⟨hw.1.1, stubs_wf cs 16 hw.1.2⟩, hw.2⟩
    have hr := refinedBy_of_hash' hCR hw' hW (by simp [shallow]) hT ⟨hs.1, stubs_at cs⟩
      (by rw [shallow_hashOf]; exact hh)
    cases T with
    | branch v₂ cs₂ m₂ =>
      simp only [shallow, PTrie.refinedBy] at hr
      obtain ⟨rfl, hv, hk⟩ := hr
      simp only [PTrie.wf, Bool.and_eq_true] at hw hW
      simp only [PTrie.refinedBy, true_and]
      exact ⟨hv, kids_rows_refinedBy hCR cs cs₂ 16 16 hw.1.2 hW.1.2 hs.2 hR hk⟩
    | _ => simp [shallow, PTrie.refinedBy] at hr
theorem kids_rows_refinedBy (hCR : Sha256CR) : ∀ (cs₁ cs₂ : Kids) (n n₂ : Nat),
    Kids.wf cs₁ n = true → Kids.wf cs₂ n₂ = true → KRefSlots cs₁ → KRevealed cs₂ →
    Kids.refinedBy (stubs cs₁) cs₂ → Kids.refinedBy cs₁ cs₂
  | .nil, cs₂, _, _, _, _, _, _, hk => by simpa [stubs] using hk
  | .none r, cs₂, n, n₂, w₁, w₂, hs, hR, hk => by
    cases cs₂ <;> simp only [stubs, Kids.refinedBy] at hk
    all_goals first | contradiction | skip
    simp only [Kids.wf, Bool.and_eq_true] at w₁ w₂
    simp only [Kids.refinedBy]
    exact kids_rows_refinedBy hCR r _ _ _ w₁.2 w₂.2 hs hR hk
  | .some c r, cs₂, n, n₂, w₁, w₂, hs, hR, hk => by
    cases cs₂ <;> simp only [stubs, Kids.refinedBy] at hk
    all_goals first | contradiction | skip
    rename_i c₂ r₂
    simp only [Kids.wf, Bool.and_eq_true] at w₁ w₂
    simp only [PTrie.refinedBy] at hk
    simp only [Kids.refinedBy]
    exact ⟨rows_refinedBy hCR c c₂ w₁.1.2 w₂.1.2 hs.1 hR.1 hk.1,
      kids_rows_refinedBy hCR r _ _ _ w₁.2 w₂.2 hs.2 hR.2 hk.2⟩
end

/-! ## Walks against the spec's partial trie

The spec runs on its partial trie `t₂` (`revealTrie` of the witness), which the full trie `T`
refines.  If the rows' trie hashes to the same root, the rows' answer / new root equals the
spec's whenever the spec's operation is defined (as it is on an accepted chunk). -/

theorem find_spec (hCR : Sha256CR) {t₁ t₂ T : PTrie} {key : List Nat} {a : Option Slot}
    (h : FChain t₁ key a) (hw : t₁.wf = true) (hs : RefSlots t₁) (hW : T.wf = true) (hR : Revealed T)
    (hh : t₁.hashOf = T.hashOf) (h₂ : t₂.refinedBy T) {a₂ : Option Slot} (hf : t₂.findRef key = some a₂) :
    a.map Slot.valueRef = a₂.map Slot.valueRef := by
  have hr := rows_refinedBy hCR t₁ T hw hW hs hR hh
  obtain ⟨b₁, hb₁, h₁⟩ := findRef_refinedBy t₁ T key a hr (fchain_sound h)
  obtain ⟨b₂, hb₂, h₂'⟩ := findRef_refinedBy t₂ T key a₂ h₂ hf
  rw [hb₁] at hb₂; simp only [Option.some.injEq] at hb₂; subst hb₂
  cases a <;> cases a₂ <;> cases b₁ <;> simp only [OptSlotRefines] at h₁ h₂'
  all_goals first | rfl | (simp only [Option.map_some, Option.some.injEq]; rw [h₁.valueRef, h₂'.valueRef])

theorem upsert_spec (hCR : Sha256CR) {t₁ t₁' t₂ T : PTrie} {key : List Nat} {v : Bytes}
    (h : UChain t₁ key v t₁') (hw : t₁.wf = true) (hs : RefSlots t₁) (hW : T.wf = true)
    (hR : Revealed T) (hh : t₁.hashOf = T.hashOf) (h₂ : t₂.refinedBy T) {t₂' : PTrie}
    (hu : t₂.upsert key v = some t₂') : t₂'.hashOf = t₁'.hashOf := by
  have hr := rows_refinedBy hCR t₁ T hw hW hs hR hh
  obtain ⟨T', hT', hh'⟩ := uchain_witness h T hr
  obtain ⟨T'', hT'', hr''⟩ := PTrie.upsert_refinedBy t₂ T key v t₂' h₂ hu
  rw [hT'] at hT''; simp only [Option.some.injEq] at hT''; subst hT''
  rw [PTrie.hashOf_refinedBy _ _ hr'', hh']

theorem del_spec (hCR : Sha256CR) {t₁ t₂ T : PTrie} {key : List Nat} {r₁ : Bool × Option PTrie}
    (h : DChain t₁ key r₁) (hw : t₁.wf = true) (hs : RefSlots t₁) (hW : T.wf = true)
    (hR : Revealed T) (hh : t₁.hashOf = T.hashOf) (h₂ : t₂.refinedBy T) {r₂ : Bool × Option PTrie}
    (hd : t₂.del key = some r₂) : r₂.1 = r₁.1 ∧ rootHash r₂.2 = rootHash r₁.2 := by
  have hr := rows_refinedBy hCR t₁ T hw hW hs hR hh
  obtain ⟨R, hR', hb, hrh⟩ := dchain_witness h T hr
  obtain ⟨R₂, hR₂, hb₂, ho₂⟩ := del_refinedBy t₂ T key r₂ h₂ hd
  rw [hR'] at hR₂; simp only [Option.some.injEq] at hR₂; subst hR₂
  exact ⟨by rw [hb₂, hb], by rw [ho₂.rootHash, hrh]⟩

end StateM5a.Refine
