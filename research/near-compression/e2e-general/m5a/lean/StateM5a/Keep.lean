import StateM5a.Refine

/-!
# StateM5a.Keep — what a committed change keeps: revealed (`Full`) and well-formed (`wf`)

`Store.KeepsFW` ("an applied change keeps the witness revealed and well-formed") is false as a
spec statement: `wf` bounds a written value's length (`< 2^32`), every node's `memory_usage`
(`< 2^64`) and every key's hex-prefix length (`< 2^32`), and an upsert / delete recomputes usages
and merges keys (`extendChild`) without any bound.  What *is* true:

* **revealed is kept unconditionally**: `upsert` / `del` on a trie without hash stubs give a trie
  without hash stubs (the relation `RP` below with `P = False`);
* **well-formed is kept where the rows say so**: every node of the spec's result `T'` is either a
  node the rows rewrote — revealed in the rows' new trie `t₁'` with the same key, slot (up to
  `SlotRefines`) and memory — or a subtree of the witness `T` (which is `wf`).  So `t₁'.wf` (a fact
  about the rows: range-checked memory limbs, nibbles, key lengths, value-length bytes) and
  `T.wf` give `T'.wf` (`upsert_wf_of_rows`, `del_wf_of_rows`).

Both are one argument: `RP P a b` is refinement (`refinedBy`) where a hash stub of `a` covers a
subtree of `b` satisfying `P` (instead of hashing to the stub).  `upsert` and `del` commute with
`RP P` for every `P` (`upsert_rp`, `del_rp`: the proofs of `PTrie.upsert_refinedBy` /
`Refine.del_refinedBy`, which never use the stub case: both functions fail on a stub).
-/

namespace StateM5a.Keep

open NearSpec NearSpecV3.D2 StateM5a.Walk StateM5a.Refine

/-! ## The relation -/

mutual
/-- `a` refines `b`, each hash stub of `a` covering a subtree of `b` with property `P`. -/
def RP (P : PTrie → Prop) : PTrie → PTrie → Prop
  | .hash _, t => P t
  | .leaf k s m, .leaf k' s' m' => k = k' ∧ m = m' ∧ SlotRefines s s'
  | .ext k c m, .ext k' c' m' => k = k' ∧ m = m' ∧ RP P c c'
  | .branch v cs m, .branch v' cs' m' => m = m' ∧ OptSlotRefines v v' ∧ KRP P cs cs'
  | .leaf .., .hash _ | .leaf .., .ext .. | .leaf .., .branch .. => False
  | .ext .., .hash _ | .ext .., .leaf .. | .ext .., .branch .. => False
  | .branch .., .hash _ | .branch .., .leaf .. | .branch .., .ext .. => False
def KRP (P : PTrie → Prop) : Kids → Kids → Prop
  | .nil, .nil => True
  | .none r, .none r' => KRP P r r'
  | .some c r, .some c' r' => RP P c c' ∧ KRP P r r'
  | .nil, .none _ | .nil, .some .. => False
  | .none _, .nil | .none _, .some .. => False
  | .some .., .nil | .some .., .none _ => False
end

variable {P : PTrie → Prop}

theorem rp_mem {t₁ t₂ : PTrie} {m : Nat} (hr : RP P t₁ t₂) (hm : t₁.mem? = some m) :
    t₂.mem? = some m := by
  cases t₁ <;> cases t₂ <;> simp_all [RP, PTrie.mem?]

theorem rp_memD {t₁ t₂ : PTrie} (hr : RP P t₁ t₂) (hm : t₁.mem?.isSome = true) :
    t₁.memD = t₂.memD := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hm
  simp [PTrie.memD, hm, rp_mem hr hm]

theorem rp_leaf (k : List Nat) (s : Slot) (m : Nat) : RP P (.leaf k s m) (.leaf k s m) := by
  simp [RP, SlotRefines]

theorem kidsFrom_rp (n i : Nat) (f g : Nat → Option PTrie)
    (h : ∀ j, (f j = none ∧ g j = none) ∨ ∃ a b, f j = some a ∧ g j = some b ∧ RP P a b) :
    KRP P (kidsFrom n i f) (kidsFrom n i g) := by
  induction n generalizing i with
  | zero => simp [kidsFrom, KRP]
  | succ n ih =>
    rcases h i with ⟨hf, hg⟩ | ⟨a, b, hf, hg, hab⟩
    · simp only [kidsFrom, hf, hg, KRP]; exact ih (i + 1)
    · simp only [kidsFrom, hf, hg, KRP]; exact ⟨hab, ih (i + 1)⟩

theorem kids1_rp (x : Nat) {c₁ c₂ : PTrie} (h : RP P c₁ c₂) : KRP P (kids1 x c₁) (kids1 x c₂) := by
  apply kidsFrom_rp; intro j
  by_cases hj : j = x
  · right; exact ⟨c₁, c₂, by simp [hj], by simp [hj], h⟩
  · left; simp [hj]

theorem kids2_rp (x y : Nat) {c₁ c₂ d₁ d₂ : PTrie} (hc : RP P c₁ c₂) (hd : RP P d₁ d₂) :
    KRP P (kids2 x c₁ y d₁) (kids2 x c₂ y d₂) := by
  apply kidsFrom_rp; intro j
  by_cases hjx : j = x
  · right; exact ⟨c₁, c₂, by simp [hjx], by simp [hjx], hc⟩
  · by_cases hjy : j = y
    · subst hjy; right; exact ⟨d₁, d₂, by simp [hjx], by simp [hjx], hd⟩
    · left; simp [hjx, hjy]

theorem wrapExt_rp (p : List Nat) {b₁ b₂ : PTrie} (h : RP P b₁ b₂) (hm : b₁.memD = b₂.memD) :
    RP P (wrapExt p b₁) (wrapExt p b₂) := by
  cases p with
  | nil => exact h
  | cons a as => simp [wrapExt, RP, hm, h]

theorem branch_rp {v₁ v₂ : Option Slot} {cs₁ cs₂ : Kids} (m : Nat)
    (hv : OptSlotRefines v₁ v₂) (hcs : KRP P cs₁ cs₂) :
    RP P (.branch v₁ cs₁ m) (.branch v₂ cs₂ m) := by
  simp [RP, hv, hcs]

theorem splitLeaf_rp (k key : List Nat) {s₁ s₂ : Slot} (v : Bytes) (hs : SlotRefines s₁ s₂) :
    RP P (splitLeaf k s₁ key v) (splitLeaf k s₂ key v) := by
  unfold splitLeaf; dsimp only
  have hl : s₁.len = s₂.len := hs.len
  generalize k.drop (commonPrefix k key).length = kr
  generalize key.drop (commonPrefix k key).length = yr
  cases kr <;> cases yr <;> simp only [hl]
  · exact rp_leaf _ _ _
  · exact wrapExt_rp _ (branch_rp _ (by simpa [OptSlotRefines] using hs)
      (kids1_rp _ (rp_leaf _ _ _))) rfl
  · exact wrapExt_rp _ (branch_rp _ (by simp [OptSlotRefines, SlotRefines])
      (kids1_rp _ (by simp [RP, hs]))) rfl
  · exact wrapExt_rp _ (branch_rp _ trivial
      (kids2_rp _ _ (by simp [RP, hs]) (rp_leaf _ _ _))) rfl

theorem splitExt_rp (k : List Nat) {c₁ c₂ : PTrie} (m : Nat) (key : List Nat) (v : Bytes)
    (hc : RP P c₁ c₂) : RP P (splitExt k c₁ m key v) (splitExt k c₂ m key v) := by
  unfold splitExt; dsimp only
  generalize k.drop (commonPrefix k key).length = kr
  generalize key.drop (commonPrefix k key).length = yr
  cases kr with
  | nil => simp [RP, hc]
  | cons x xs =>
    have hsub : RP P (match xs with
          | [] => c₁
          | _ :: _ => PTrie.ext xs c₁ (extOwnMem xs + (m - extOwnMem k)))
        (match xs with
          | [] => c₂
          | _ :: _ => PTrie.ext xs c₂ (extOwnMem xs + (m - extOwnMem k))) := by
      cases xs <;> simp [RP, hc]
    cases yr with
    | nil =>
      exact wrapExt_rp _ (branch_rp _ (by simp [OptSlotRefines, SlotRefines])
        (kids1_rp _ hsub)) rfl
    | cons y ys =>
      exact wrapExt_rp _ (branch_rp _ trivial (kids2_rp _ _ hsub (rp_leaf _ _ _))) rfl

/-! ## `upsert` commutes with `RP P` -/

mutual
theorem upsert_rp : ∀ (t₁ t₂ : PTrie) (key : List Nat) (v : Bytes) (t₁' : PTrie),
    RP P t₁ t₂ → t₁.upsert key v = some t₁' →
    ∃ t₂', t₂.upsert key v = some t₂' ∧ RP P t₁' t₂'
  | .hash _, _, _, _, _, _, h => by simp [PTrie.upsert] at h
  | .leaf k s m, t₂, key, v, t₁', hr, h => by
    cases t₂ <;> simp only [RP] at hr
    obtain ⟨rfl, rfl, hs⟩ := hr
    simp only [PTrie.upsert] at h ⊢
    by_cases e : k = key
    · simp only [e, ↓reduceIte, Option.some.injEq] at h ⊢; subst h
      exact ⟨_, rfl, rp_leaf _ _ _⟩
    · simp only [e, ↓reduceIte, Option.some.injEq] at h ⊢; subst h
      exact ⟨_, rfl, splitLeaf_rp k key v hs⟩
  | .ext k c m, t₂, key, v, t₁', hr, h => by
    cases t₂ <;> simp only [RP] at hr
    rename_i k₂ c₂ m₂
    obtain ⟨rfl, rfl, hc⟩ := hr
    simp only [PTrie.upsert] at h ⊢
    by_cases hp : isPrefix k key = true
    · simp only [hp, ↓reduceIte] at h ⊢
      cases hm : c.mem? <;> cases hu : c.upsert (key.drop k.length) v <;> simp [hm, hu] at h
      rename_i cm c'
      obtain ⟨c₂', hu₂, hc'⟩ := upsert_rp c c₂ _ v c' hc hu
      have hm₂ := rp_mem hc hm
      have hd := rp_memD hc' (PTrie.upsert_mem c _ v c' hu)
      subst h
      refine ⟨.ext k c₂' (m + c₂'.memD - cm), by simp [hm₂, hu₂], ?_⟩
      simp [RP, hc', hd]
    · have hp' : isPrefix k key = false := by simpa using hp
      simp only [hp', Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h ⊢; subst h
      exact ⟨_, rfl, splitExt_rp k m key v hc⟩
  | .branch bv cs m, t₂, [], v, t₁', hr, h => by
    cases t₂ <;> simp only [RP] at hr
    rename_i bv₂ cs₂ m₂
    obtain ⟨rfl, hv, hcs⟩ := hr
    simp only [PTrie.upsert, Option.some.injEq] at h ⊢; subst h
    refine ⟨_, rfl, ?_⟩
    cases bv <;> cases bv₂ <;> simp only [OptSlotRefines] at hv
    · exact branch_rp _ (by simp [OptSlotRefines, SlotRefines]) hcs
    · simp only [hv.len]
      exact branch_rp _ (by simp [OptSlotRefines, SlotRefines]) hcs
  | .branch bv cs m, t₂, n :: rest, v, t₁', hr, h => by
    cases t₂ <;> simp only [RP] at hr
    rename_i bv₂ cs₂ m₂
    obtain ⟨rfl, hv, hcs⟩ := hr
    simp only [PTrie.upsert] at h ⊢
    cases hu : Kids.upsert cs n rest v with
    | none => simp [hu] at h
    | some r =>
      obtain ⟨cs', a, b⟩ := r
      simp only [hu, Option.map_some, Option.some.injEq] at h; subst h
      obtain ⟨cs₂', hu₂, hr'⟩ := kids_upsert_rp cs cs₂ n rest v cs' a b hcs hu
      exact ⟨_, by simp [hu₂], branch_rp _ hv hr'⟩

theorem kids_upsert_rp : ∀ (cs₁ cs₂ : Kids) (n : Nat) (key : List Nat) (v : Bytes)
    (cs₁' : Kids) (a b : Nat), KRP P cs₁ cs₂ → Kids.upsert cs₁ n key v = some (cs₁', a, b) →
    ∃ cs₂', Kids.upsert cs₂ n key v = some (cs₂', a, b) ∧ KRP P cs₁' cs₂'
  | .nil, _, _, _, _, _, _, _, _, h => by simp [Kids.upsert] at h
  | .none r, cs₂, 0, key, v, cs₁', a, b, hr, h => by
    cases cs₂ <;> simp only [KRP] at hr
    simp only [Kids.upsert, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨_, ⟨rfl, rfl, rfl⟩, by simp only [KRP]; exact ⟨rp_leaf _ _ _, hr⟩⟩
  | .some c r, cs₂, 0, key, v, cs₁', a, b, hr, h => by
    cases cs₂ <;> simp only [KRP] at hr
    rename_i c₂ r₂
    simp only [Kids.upsert] at h ⊢
    cases hm : c.mem? <;> cases hu : c.upsert key v <;> simp [hm, hu] at h
    rename_i cm c'
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨c₂', hu₂, hc'⟩ := upsert_rp c c₂ key v c' hr.1 hu
    have hm₂ := rp_mem hr.1 hm
    have hd := rp_memD hc' (PTrie.upsert_mem c key v c' hu)
    exact ⟨.some c₂' r₂, by simp [hm₂, hu₂, hd], by simp only [KRP]; exact ⟨hc', hr.2⟩⟩
  | .none r, cs₂, i + 1, key, v, cs₁', a, b, hr, h => by
    cases cs₂ <;> simp only [KRP] at hr
    rename_i r₂
    simp only [Kids.upsert] at h ⊢
    cases hu : Kids.upsert r i key v with
    | none => simp [hu] at h
    | some x =>
      obtain ⟨x1, x2, x3⟩ := x
      simp only [hu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨r₂', hu₂, hr'⟩ := kids_upsert_rp r r₂ i key v x1 x2 x3 hr hu
      exact ⟨.none r₂', by simp [hu₂], by simp only [KRP]; exact hr'⟩
  | .some c r, cs₂, i + 1, key, v, cs₁', a, b, hr, h => by
    cases cs₂ <;> simp only [KRP] at hr
    rename_i c₂ r₂
    simp only [Kids.upsert] at h ⊢
    cases hu : Kids.upsert r i key v with
    | none => simp [hu] at h
    | some x =>
      obtain ⟨x1, x2, x3⟩ := x
      simp only [hu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨r₂', hu₂, hr'⟩ := kids_upsert_rp r r₂ i key v x1 x2 x3 hr.2 hu
      exact ⟨.some c₂ r₂', by simp [hu₂], by simp only [KRP]; exact ⟨hr.1, hr'⟩⟩
end

/-! ## `del` commutes with `RP P` -/

def OptRP (P : PTrie → Prop) : Option PTrie → Option PTrie → Prop
  | none, none => True
  | some a, some b => RP P a b
  | _, _ => False

theorem extendChild_rp (k : List Nat) {c₁ c₂ : PTrie} (hr : RP P c₁ c₂) {o₁ : Option PTrie}
    (h : extendChild k c₁ = some o₁) : ∃ o₂, extendChild k c₂ = some o₂ ∧ OptRP P o₁ o₂ := by
  cases c₁ with
  | hash => simp [extendChild] at h
  | leaf k2 s m =>
    cases c₂ <;> simp only [RP] at hr
    obtain ⟨rfl, rfl, hs⟩ := hr
    simp only [extendChild, Option.some.injEq] at h; subst h
    exact ⟨_, rfl, by simp [OptRP, RP, hs, hs.len]⟩
  | ext k2 c m =>
    cases c₂ <;> simp only [RP] at hr
    obtain ⟨rfl, rfl, hc⟩ := hr
    simp only [extendChild, Option.some.injEq] at h; subst h
    exact ⟨_, rfl, by simp [OptRP, RP, hc]⟩
  | branch v cs m =>
    cases c₂ <;> simp only [RP] at hr
    obtain ⟨rfl, hv, hcs⟩ := hr
    simp only [extendChild, Option.some.injEq] at h; subst h
    exact ⟨_, rfl, by simp [OptRP, RP, hv, hcs]⟩

def PresRP (P : PTrie → Prop) : List (Nat × PTrie) → List (Nat × PTrie) → Prop
  | [], [] => True
  | (i, c) :: r, (j, d) :: s => i = j ∧ RP P c d ∧ PresRP P r s
  | _, _ => False

theorem present_rp : ∀ (cs₁ cs₂ : Kids) (i : Nat), KRP P cs₁ cs₂ →
    PresRP P (Kids.present cs₁ i) (Kids.present cs₂ i)
  | .nil, cs₂, i, hr => by
    cases cs₂ <;> simp [KRP] at hr; simp [Kids.present, PresRP]
  | .none r, cs₂, i, hr => by
    cases cs₂ <;> simp only [KRP] at hr
    all_goals first | contradiction | exact present_rp r _ (i + 1) hr
  | .some c r, cs₂, i, hr => by
    cases cs₂ <;> simp only [KRP] at hr
    all_goals first | contradiction |
      exact ⟨rfl, hr.1, present_rp r _ (i + 1) hr.2⟩

theorem squashBranch_rp {v₁ v₂ : Option Slot} {cs₁ cs₂ : Kids} (m : Nat)
    (hv : OptSlotRefines v₁ v₂) (hcs : KRP P cs₁ cs₂) {o₁ : Option PTrie}
    (h : squashBranch v₁ cs₁ m = some o₁) :
    ∃ o₂, squashBranch v₂ cs₂ m = some o₂ ∧ OptRP P o₁ o₂ := by
  have hp := present_rp cs₁ cs₂ 0 hcs
  have hbr : OptRP P (some (.branch v₁ cs₁ m)) (some (.branch v₂ cs₂ m)) := by
    simp [OptRP, RP, hv, hcs]
  unfold squashBranch at h ⊢
  generalize Kids.present cs₁ 0 = l₁ at h hp
  generalize Kids.present cs₂ 0 = l₂ at hp
  cases v₁ <;> cases v₂ <;> simp only [OptSlotRefines] at hv
  · match l₁, l₂, hp with
    | [], [], _ =>
      simp only [Option.some.injEq] at h; subst h; exact ⟨none, rfl, trivial⟩
    | [(i, c)], [(j, d)], hp =>
      obtain ⟨rfl, hcd, -⟩ := hp
      exact extendChild_rp [i] hcd h
    | (i, c) :: (i', c') :: r, (j, d) :: (j', d') :: s, _ =>
      simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, hbr⟩
    | [], _ :: _, hp => simp [PresRP] at hp
    | _ :: _, [], hp => simp [PresRP] at hp
    | [_], _ :: _ :: _, hp => simp [PresRP] at hp
    | _ :: _ :: _, [_], hp => simp [PresRP] at hp
  · rename_i s₁ s₂
    match l₁, l₂, hp with
    | [], [], _ =>
      simp only [Option.some.injEq] at h; subst h
      exact ⟨_, rfl, by simp [OptRP, RP, hv, hv.len]⟩
    | [(i, c)], [(j, d)], _ =>
      simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, hbr⟩
    | (i, c) :: (i', c') :: r, (j, d) :: (j', d') :: s, _ =>
      simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, hbr⟩
    | [], _ :: _, hp => simp [PresRP] at hp
    | _ :: _, [], hp => simp [PresRP] at hp
    | [_], _ :: _ :: _, hp => simp [PresRP] at hp
    | _ :: _ :: _, [_], hp => simp [PresRP] at hp

/-- Delete results: same `deleted` flag, the remaining subtree related by `RP P`. -/
def DelRP (P : PTrie → Prop) (r₁ r₂ : Bool × Option PTrie) : Prop := r₁.1 = r₂.1 ∧ OptRP P r₁.2 r₂.2

def KDelRP (P : PTrie → Prop) : Option (Kids × Nat × Nat) → Option (Kids × Nat × Nat) → Prop
  | none, none => True
  | some (k₁, a₁, b₁), some (k₂, a₂, b₂) => KRP P k₁ k₂ ∧ a₁ = a₂ ∧ b₁ = b₂
  | _, _ => False

mutual
theorem del_rp : ∀ (t₁ t₂ : PTrie) (key : List Nat) (r₁ : Bool × Option PTrie),
    RP P t₁ t₂ → t₁.del key = some r₁ → ∃ r₂, t₂.del key = some r₂ ∧ DelRP P r₁ r₂
  | .hash _, _, _, _, _, h => by simp [PTrie.del] at h
  | .leaf k s m, t₂, key, r₁, hr, h => by
    cases t₂ <;> simp only [RP] at hr
    obtain ⟨rfl, rfl, hs⟩ := hr
    simp only [PTrie.del] at h ⊢
    by_cases e : k = key
    · simp only [e, ↓reduceIte, Option.some.injEq] at h ⊢; subst h
      exact ⟨_, rfl, rfl, trivial⟩
    · simp only [e, ↓reduceIte, Option.some.injEq] at h ⊢; subst h
      exact ⟨_, rfl, rfl, by simp [OptRP, RP, hs]⟩
  | .ext k c m, t₂, key, r₁, hr, h => by
    cases t₂ <;> simp only [RP] at hr
    rename_i k₂ c₂ m₂
    obtain ⟨rfl, rfl, hc⟩ := hr
    have hext : OptRP P (some (.ext k c m)) (some (.ext k c₂ m)) := by
      simp [OptRP, RP, hc]
    simp only [PTrie.del] at h ⊢
    by_cases hp : isPrefix k key = true
    · simp only [hp, ↓reduceIte] at h ⊢
      cases hm : c.mem? with
      | none => simp [hm] at h
      | some cm =>
        have hm₂ := rp_mem hc hm
        cases hd : c.del (key.drop k.length) with
        | none => simp [hm, hd] at h
        | some rc =>
          obtain ⟨rc₂, hd₂, hb, ho⟩ := del_rp c c₂ _ rc hc hd
          obtain ⟨b, o⟩ := rc
          obtain ⟨b₂, o₂⟩ := rc₂
          simp only at hb ho; subst hb
          rw [hm₂, hd₂]
          simp only [hm, hd] at h
          cases b with
          | false =>
            simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, rfl, hext⟩
          | true =>
            cases o <;> cases o₂ <;> simp only [OptRP] at ho
            · simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, rfl, trivial⟩
            · rename_i c' c₂'
              cases he : extendChild k c' with
              | none => simp [he] at h
              | some x =>
                simp only [he, Option.map_some, Option.some.injEq] at h; subst h
                obtain ⟨x₂, he₂, hx⟩ := extendChild_rp k ho he
                exact ⟨(true, x₂), by simp [he₂], rfl, hx⟩
    · have hp' : isPrefix k key = false := by simpa using hp
      simp only [hp', Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h ⊢; subst h
      exact ⟨_, rfl, rfl, hext⟩
  | .branch v cs m, t₂, [], r₁, hr, h => by
    cases t₂ <;> simp only [RP] at hr
    rename_i v₂ cs₂ m₂
    obtain ⟨rfl, hv, hcs⟩ := hr
    simp only [PTrie.del] at h ⊢
    cases v <;> cases v₂ <;> simp only [OptSlotRefines] at hv
    · simp only [Option.some.injEq] at h; subst h
      exact ⟨_, rfl, rfl, by simp [OptRP, RP, hcs, OptSlotRefines]⟩
    · rename_i s₁ s₂
      simp only at h ⊢
      rw [← hv.len]
      cases he : squashBranch none cs (m - valueMem s₁.len) with
      | none => simp [he] at h
      | some x =>
        simp only [he, Option.map_some, Option.some.injEq] at h; subst h
        obtain ⟨x₂, he₂, hx⟩ := squashBranch_rp (v₂ := none) _ (by simp [OptSlotRefines]) hcs he
        exact ⟨(true, x₂), by simp [he₂], rfl, hx⟩
  | .branch v cs m, t₂, n :: rest, r₁, hr, h => by
    cases t₂ <;> simp only [RP] at hr
    rename_i v₂ cs₂ m₂
    obtain ⟨rfl, hv, hcs⟩ := hr
    simp only [PTrie.del] at h ⊢
    cases hd : Kids.delAt cs n rest with
    | none => simp [hd] at h
    | some o =>
      obtain ⟨o₂, hd₂, ho⟩ := kids_delAt_rp cs cs₂ n rest o hcs hd
      rw [hd₂]
      cases o <;> cases o₂ <;> simp only [KDelRP] at ho
      · simp only [hd, Option.some.injEq] at h; subst h
        exact ⟨_, rfl, rfl, by simp [OptRP, RP, hcs, hv]⟩
      · rename_i x₁ x₂
        obtain ⟨cs', a, b⟩ := x₁
        obtain ⟨cs₂', a₂, b₂⟩ := x₂
        obtain ⟨hk, rfl, rfl⟩ := ho
        simp only [hd] at h ⊢
        cases he : squashBranch v cs' (m - a + b) with
        | none => simp [he] at h
        | some x =>
          simp only [he, Option.map_some, Option.some.injEq] at h; subst h
          obtain ⟨y, he₂, hy⟩ := squashBranch_rp _ hv hk he
          exact ⟨(true, y), by simp [he₂], rfl, hy⟩

theorem kids_delAt_rp : ∀ (cs₁ cs₂ : Kids) (n : Nat) (key : List Nat)
    (o₁ : Option (Kids × Nat × Nat)), KRP P cs₁ cs₂ → Kids.delAt cs₁ n key = some o₁ →
    ∃ o₂, Kids.delAt cs₂ n key = some o₂ ∧ KDelRP P o₁ o₂
  | .nil, cs₂, n, key, o₁, hr, h => by
    cases cs₂ <;> simp [KRP] at hr
    simp only [Kids.delAt, Option.some.injEq] at h ⊢; subst h; exact ⟨_, rfl, trivial⟩
  | .none r, cs₂, 0, key, o₁, hr, h => by
    cases cs₂ <;> simp only [KRP] at hr
    all_goals first | contradiction | skip
    simp only [Kids.delAt, Option.some.injEq] at h ⊢; subst h; exact ⟨_, rfl, trivial⟩
  | .some c r, cs₂, 0, key, o₁, hr, h => by
    cases cs₂ <;> simp only [KRP] at hr
    all_goals first | contradiction | skip
    rename_i c₂ r₂
    simp only [Kids.delAt] at h ⊢
    cases hm : c.mem? with
    | none => simp [hm] at h
    | some cm =>
      rw [rp_mem hr.1 hm]
      cases hd : c.del key with
      | none => simp [hm, hd] at h
      | some rc =>
        obtain ⟨rc₂, hd₂, hb, ho⟩ := del_rp c c₂ _ rc hr.1 hd
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
          cases oc <;> cases oc₂ <;> simp only [OptRP] at ho
          · simp [KDelRP, KRP, hr.2]
          · rename_i c' c₂'
            have hmd := rp_memD ho (del_some hd)
            simp [KDelRP, KRP, hr.2, ho, hmd]
  | .none r, cs₂, i + 1, key, o₁, hr, h => by
    cases cs₂ <;> simp only [KRP] at hr
    all_goals first | contradiction | skip
    rename_i r₂
    simp only [Kids.delAt] at h ⊢
    cases hd : Kids.delAt r i key with
    | none => simp [hd] at h
    | some x =>
      obtain ⟨x₂, hd₂, hx⟩ := kids_delAt_rp r r₂ i key x hr hd
      simp only [hd, Option.map_some, Option.some.injEq] at h; subst h
      refine ⟨_, by rw [hd₂]; rfl, ?_⟩
      cases x <;> cases x₂ <;> simp only [KDelRP] at hx
      · simp [KDelRP]
      · rename_i y₁ y₂
        obtain ⟨k₁, a₁, b₁⟩ := y₁; obtain ⟨k₂, a₂, b₂⟩ := y₂
        simp only at hx; simp [KDelRP, KRP, hx]
  | .some c r, cs₂, i + 1, key, o₁, hr, h => by
    cases cs₂ <;> simp only [KRP] at hr
    all_goals first | contradiction | skip
    rename_i c₂ r₂
    simp only [Kids.delAt] at h ⊢
    cases hd : Kids.delAt r i key with
    | none => simp [hd] at h
    | some x =>
      obtain ⟨x₂, hd₂, hx⟩ := kids_delAt_rp r r₂ i key x hr.2 hd
      simp only [hd, Option.map_some, Option.some.injEq] at h; subst h
      refine ⟨_, by rw [hd₂]; rfl, ?_⟩
      cases x <;> cases x₂ <;> simp only [KDelRP] at hx
      · simp [KDelRP]
      · rename_i y₁ y₂
        obtain ⟨k₁, a₁, b₁⟩ := y₁; obtain ⟨k₂, a₂, b₂⟩ := y₂
        simp only at hx; simp [KDelRP, KRP, hx, hr.1]
end

/-! ## Well-formedness along `RP wf` -/

/-- The covering predicate for well-formedness. -/
abbrev WfP : PTrie → Prop := fun t => t.wf = true

theorem slotOk_of_refines {s₁ s₂ : Slot} (h : SlotRefines s₁ s₂) (hs : slotOk s₁ = true) :
    slotOk s₂ = true := by
  rcases h with rfl | ⟨v, rfl, rfl⟩
  · exact hs
  · simp only [slotOk, Bool.and_eq_true, decide_eq_true_eq] at hs ⊢; exact hs.1

mutual
/-- **`wf` transfers along `RP wf`**: the related nodes have the same keys, memories and (up to
`SlotRefines`) slots, and the stubs cover well-formed subtrees. -/
theorem rp_wf : ∀ (a b : PTrie), RP WfP a b → a.wf = true → b.wf = true
  | .hash _, _, hr, _ => hr
  | .leaf k s m, b, hr, hw => by
    cases b <;> simp only [RP] at hr
    obtain ⟨rfl, rfl, hs⟩ := hr
    simp only [PTrie.wf, Bool.and_eq_true] at hw ⊢
    exact ⟨⟨⟨hw.1.1.1, slotOk_of_refines hs hw.1.1.2⟩, hw.1.2⟩, hw.2⟩
  | .ext k c m, b, hr, hw => by
    cases b <;> simp only [RP] at hr
    rename_i k' c' m'
    obtain ⟨rfl, rfl, hc⟩ := hr
    simp only [PTrie.wf, Bool.and_eq_true] at hw ⊢
    exact ⟨⟨⟨hw.1.1.1, rp_wf c c' hc hw.1.1.2⟩, hw.1.2⟩, hw.2⟩
  | .branch v cs m, b, hr, hw => by
    cases b <;> simp only [RP] at hr
    rename_i v' cs' m'
    obtain ⟨rfl, hv, hcs⟩ := hr
    simp only [PTrie.wf, Bool.and_eq_true] at hw ⊢
    refine ⟨⟨?_, krp_wf cs cs' 16 hcs hw.1.2⟩, hw.2⟩
    have h1 := hw.1.1
    cases v <;> cases v' <;> simp only [OptSlotRefines] at hv
    · rfl
    · exact slotOk_of_refines hv h1
theorem krp_wf : ∀ (a b : Kids) (n : Nat), KRP WfP a b → Kids.wf a n = true → Kids.wf b n = true
  | .nil, b, n, hr, hw => by
    cases b <;> simp only [KRP] at hr
    exact hw
  | .none r, b, n, hr, hw => by
    cases b <;> simp only [KRP] at hr
    rename_i r'
    simp only [Kids.wf, Bool.and_eq_true] at hw ⊢
    exact ⟨hw.1, krp_wf r r' _ hr hw.2⟩
  | .some c r, b, n, hr, hw => by
    cases b <;> simp only [KRP] at hr
    rename_i c' r'
    simp only [Kids.wf, Bool.and_eq_true] at hw ⊢
    exact ⟨⟨hw.1.1, rp_wf c c' hr.1 hw.1.2⟩, krp_wf r r' _ hr.2 hw.2⟩
end

mutual
/-- A refinement of a well-formed trie covers well-formed subtrees. -/
theorem rp_of_refinedBy : ∀ (a b : PTrie), a.refinedBy b → b.wf = true → RP WfP a b
  | .hash _, _, _, hw => hw
  | .leaf k s m, b, hr, _ => by
    cases b <;> simp only [PTrie.refinedBy] at hr
    simpa only [RP] using hr
  | .ext k c m, b, hr, hw => by
    cases b <;> simp only [PTrie.refinedBy] at hr
    rename_i k' c' m'
    obtain ⟨rfl, rfl, hc⟩ := hr
    simp only [PTrie.wf, Bool.and_eq_true] at hw
    simp only [RP, true_and]
    exact rp_of_refinedBy c c' hc hw.1.1.2
  | .branch v cs m, b, hr, hw => by
    cases b <;> simp only [PTrie.refinedBy] at hr
    rename_i v' cs' m'
    obtain ⟨rfl, hv, hcs⟩ := hr
    simp only [PTrie.wf, Bool.and_eq_true] at hw
    simp only [RP, true_and]
    exact ⟨hv, krp_of_refinedBy cs cs' 16 hcs hw.1.2⟩
theorem krp_of_refinedBy : ∀ (a b : Kids) (n : Nat), Kids.refinedBy a b → Kids.wf b n = true →
    KRP WfP a b
  | .nil, b, _, hr, _ => by
    cases b <;> simp only [Kids.refinedBy] at hr
    simp [KRP]
  | .none r, b, n, hr, hw => by
    cases b <;> simp only [Kids.refinedBy] at hr
    rename_i r'
    simp only [Kids.wf, Bool.and_eq_true] at hw
    simp only [KRP]
    exact krp_of_refinedBy r r' _ hr hw.2
  | .some c r, b, n, hr, hw => by
    cases b <;> simp only [Kids.refinedBy] at hr
    rename_i c' r'
    simp only [Kids.wf, Bool.and_eq_true] at hw
    simp only [KRP]
    exact ⟨rp_of_refinedBy c c' hr.1 hw.1.2, krp_of_refinedBy r r' _ hr.2 hw.2⟩
end

/-! ## A change keeps `wf` where the rows' new trie is `wf` -/

/-- **Upsert keeps `wf` (rows' bounds).**  The rows' trie `t₁` refines the well-formed witness
`T`; if the rows' result `t₁'` is well-formed, so is the spec's result `T'`. -/
theorem upsert_wf_of_rows {t₁ t₁' T T' : PTrie} {key : List Nat} {x : Bytes}
    (hr : t₁.refinedBy T) (hw : T.wf = true) (h : t₁.upsert key x = some t₁')
    (hT : T.upsert key x = some T') (hw' : t₁'.wf = true) : T'.wf = true := by
  obtain ⟨T'', hT'', hr'⟩ := upsert_rp t₁ T key x t₁' (rp_of_refinedBy t₁ T hr hw) h
  rw [hT] at hT''; cases hT''
  exact rp_wf _ _ hr' hw'

/-- **Delete keeps `wf` (rows' bounds).** -/
theorem del_wf_of_rows {t₁ t₁' T T' : PTrie} {key : List Nat} {b b₂ : Bool}
    (hr : t₁.refinedBy T) (hw : T.wf = true) (h : t₁.del key = some (b, some t₁'))
    (hT : T.del key = some (b₂, some T')) (hw' : t₁'.wf = true) : T'.wf = true := by
  obtain ⟨r₂, hr₂, -, ho⟩ := del_rp t₁ T key _ (rp_of_refinedBy t₁ T hr hw) h
  rw [hT] at hr₂; cases hr₂
  exact rp_wf _ _ ho hw'

/-- **A committed change keeps `wf` (rows' bounds)**, at `applyChange`: the rows' change on their
trie `t₁` (refining the well-formed witness `T`) leaves a well-formed `t₁'`. -/
theorem applyChange_wf_of_rows {t₁ t₁' T T' : PTrie} {k : Bytes} {v : Option Bytes}
    (hr : t₁.refinedBy T) (hw : T.wf = true) (h : applyChange (some t₁) k v = some (some t₁'))
    (hT : applyChange (some T) k v = some (some T')) (hw' : t₁'.wf = true) : T'.wf = true := by
  cases v with
  | some x =>
    simp only [applyChange, Option.map_eq_some_iff, Option.some.injEq] at h hT
    obtain ⟨a, ha, rfl⟩ := h
    obtain ⟨A, hA, rfl⟩ := hT
    exact upsert_wf_of_rows hr hw ha hA hw'
  | none =>
    simp only [applyChange, Option.map_eq_some_iff] at h hT
    obtain ⟨⟨b, o⟩, ha, ho⟩ := h
    obtain ⟨⟨b₂, O⟩, hA, hO⟩ := hT
    simp only at ho hO; subst ho hO
    exact del_wf_of_rows hr hw ha hA hw'

/-! ## Revealed is kept unconditionally (`RP` with `P = False`) -/

/-- The predicate of no stub at all. -/
abbrev NoP : PTrie → Prop := fun _ => False

end StateM5a.Keep
