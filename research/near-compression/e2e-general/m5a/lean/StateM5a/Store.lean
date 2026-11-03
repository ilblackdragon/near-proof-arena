import StateM5a.Refine

/-!
# StateM5a.Store — batched FINAL: the version store replaces the hash link

Batched FINAL (M5a-2) hashes each touched node once: a node a later change rewrites is not
hashed but published on the `VER` bus under a *version id* (the producing row's new-node id,
unique per row), and the rows of the next change that read it receive its record from `VER` by
that id.  A pre-state node is hashed by one row and published under its digest for every other
reader.  The trie root between changes (`TCH`) and every child slot are *refs*: a digest or a
version id.

**The store.**  Version ids are unique (one producing row each) and every `VER` receive must
match a send, so the receives of one id all see one record: the bus defines a function
`σ : Store` from ids to records (`Rec`: a node whose children are refs).  A ref *expands*
(`Exp σ`) to the partial trie obtained by replacing every version id by its record, recursively,
and leaving digests as hash stubs.  `exp_functional`: a ref has at most one expansion, so the
trie that change `j` leaves (the expansion of `TCH`'s ref `j + 1`, as the rows that produced it
see it) is the trie change `j + 1` starts from.

**One change.**  Its rows reveal the expansion `P` along the walk: stubs on the path are replaced
by nodes that hash to them (`Rv`: the row hashed the record, or received it from `VER` under its
digest from a row that hashed it).  The rows' step relation (`UChain` / `DChain` / `FChain` of
`Walk`, one constructor per row op) holds on the revealed trie `t₁` and gives the rows' new trie
`t₁'`; nodes the rows hash (final nodes) collapse back to their digests, giving the expansion `P'`
of the change's output ref (`Rv P' t₁'`).
* `rv_refinedBy`: revealing preserves refinement of the witness trie (collision resistance and
  `NodeSerInj` through `refinedBy_of_hash`; the witness is revealed where the rows reveal: `Full`);
* `rv_collapse`: collapsing does too (no assumption: `hashOf_refinedBy`);
* `change_step`: so `P.refinedBy T` gives `P'.refinedBy T'` for the spec's step `T ↦ T'`
  (`upsert_step` for an upsert walk, `find_step` for an INTAKE find).

**All changes.**  `batched_upserts`: from `TCH(0) = prev_state_root` (a digest, so `P₀` is the
stub `prev_state_root`, refined by any witness trie with that root hash) through every change to
`TCH(n) = post_state_root` (a digest: the last change hashes the root), the post-state root is
the root hash of the spec's `applyChanges` on the witness trie.  Deletes join through the same
`change_step` once a delete witness lemma (`del_refinedBy`) is available.

Premises (never axioms): `Sha256CR` and `NodeSerInj` (`Walk`); the witness tries are revealed
where the rows reveal (`Full`, a property of the witness: open, witness extraction).  The
bus-level facts (that the rows' `VER` / `DOWN` / `UP` messages produce `Rv`, the chain relation
and `Exp`) are the open bus-level step of `Walk`.
-/

namespace StateM5a.Store

open NearSpec NearSpecV3.D2 StateM5a.Steps StateM5a.Walk

/-! ## Refs, records, the store -/

/-- A node ref on `DOWN` / `UP` / `TCH` / `VER`: a SHA-256 digest (flag 0) or a version id. -/
inductive Ref where
  | dig (h : Bytes)
  | vid (n : Nat)

/-- A record's 16 child slots (as `Kids`), holding refs. -/
inductive RKids where
  | nil
  | none (rest : RKids)
  | some (c : Ref) (rest : RKids)

/-- A version record (the `VER` message parts of a `BR` / `SN` row): a node with ref children. -/
inductive Rec where
  | leaf (k : List Nat) (v : Slot) (m : Nat)
  | ext (k : List Nat) (c : Ref) (m : Nat)
  | branch (v : Option Slot) (cs : RKids) (m : Nat)

/-- The version store: the record each version id is published with. -/
abbrev Store := Nat → Option Rec

/-- Expansion through the store: a ref to a partial trie (digests stay stubs), record children
to `Kids` (one inductive over `Sum`, refs / children). -/
inductive Exp (σ : Store) : Sum Ref RKids → Sum PTrie Kids → Prop
  | dig (h : Bytes) : Exp σ (.inl (.dig h)) (.inl (.hash h))
  | leaf (n : Nat) (k : List Nat) (v : Slot) (m : Nat) (hn : σ n = some (.leaf k v m)) :
      Exp σ (.inl (.vid n)) (.inl (.leaf k v m))
  | ext (n : Nat) (k : List Nat) (c : Ref) (m : Nat) (t : PTrie) (hn : σ n = some (.ext k c m))
      (hc : Exp σ (.inl c) (.inl t)) : Exp σ (.inl (.vid n)) (.inl (.ext k t m))
  | branch (n : Nat) (v : Option Slot) (cs : RKids) (m : Nat) (ks : Kids)
      (hn : σ n = some (.branch v cs m)) (hc : Exp σ (.inr cs) (.inr ks)) :
      Exp σ (.inl (.vid n)) (.inl (.branch v ks m))
  | knil : Exp σ (.inr .nil) (.inr .nil)
  | knone (r : RKids) (ks : Kids) (hr : Exp σ (.inr r) (.inr ks)) :
      Exp σ (.inr (.none r)) (.inr (.none ks))
  | ksome (c : Ref) (r : RKids) (t : PTrie) (ks : Kids) (hc : Exp σ (.inl c) (.inl t))
      (hr : Exp σ (.inr r) (.inr ks)) : Exp σ (.inr (.some c r)) (.inr (.some t ks))

/-- **A ref has at most one expansion** (the store is a function). -/
theorem exp_functional {σ : Store} {x : Sum Ref RKids} {y₁ : Sum PTrie Kids} (h₁ : Exp σ x y₁) :
    ∀ {y₂}, Exp σ x y₂ → y₁ = y₂ := by
  induction h₁ with
  | dig h => intro y₂ h₂; cases h₂; rfl
  | leaf n k v m hn =>
    intro y₂ h₂
    cases h₂ with
    | leaf _ k' v' m' hn' => rw [hn] at hn'; cases hn'; rfl
    | ext _ k' c' m' t' hn' => rw [hn] at hn'; cases hn'
    | branch _ v' cs' m' ks' hn' => rw [hn] at hn'; cases hn'
  | ext n k c m t hn hc ih =>
    intro y₂ h₂
    cases h₂ with
    | leaf _ k' v' m' hn' => rw [hn] at hn'; cases hn'
    | ext _ k' c' m' t' hn' hc' =>
      rw [hn] at hn'; cases hn'
      cases ih hc'; rfl
    | branch _ v' cs' m' ks' hn' => rw [hn] at hn'; cases hn'
  | branch n v cs m ks hn hc ih =>
    intro y₂ h₂
    cases h₂ with
    | leaf _ k' v' m' hn' => rw [hn] at hn'; cases hn'
    | ext _ k' c' m' t' hn' => rw [hn] at hn'; cases hn'
    | branch _ v' cs' m' ks' hn' hc' =>
      rw [hn] at hn'; cases hn'
      cases ih hc'; rfl
  | knil => intro y₂ h₂; cases h₂; rfl
  | knone r ks hr ih => intro y₂ h₂; cases h₂ with | knone _ ks' hr' => cases ih hr'; rfl
  | ksome c r t ks hc hr ihc ihr =>
    intro y₂ h₂
    cases h₂ with
    | ksome _ _ t' ks' hc' hr' => cases ihc hc'; cases ihr hr'; rfl

/-! ## Revealing and collapsing -/

/-- `Rv x y`: `y` is `x` with hash stubs replaced by nodes hashing to them (revealed further). -/
inductive Rv : Sum PTrie Kids → Sum PTrie Kids → Prop
  | refl (x : Sum PTrie Kids) : Rv x x
  | stub (h : Bytes) (n n' : PTrie) (hn : ∀ g, n ≠ .hash g) (hw : n.wf = true) (hs : Shallow n)
      (hh : n.hashOf = h) (hr : Rv (.inl n) (.inl n')) : Rv (.inl (.hash h)) (.inl n')
  | ext (k : List Nat) (c c' : PTrie) (m : Nat) (hr : Rv (.inl c) (.inl c')) :
      Rv (.inl (.ext k c m)) (.inl (.ext k c' m))
  | branch (v : Option Slot) (cs cs' : Kids) (m : Nat) (hr : Rv (.inr cs) (.inr cs')) :
      Rv (.inl (.branch v cs m)) (.inl (.branch v cs' m))
  | knone (r r' : Kids) (hr : Rv (.inr r) (.inr r')) : Rv (.inr (.none r)) (.inr (.none r'))
  | ksome (c c' : PTrie) (r r' : Kids) (hc : Rv (.inl c) (.inl c')) (hr : Rv (.inr r) (.inr r')) :
      Rv (.inr (.some c r)) (.inr (.some c' r'))

/-- Refinement on `Sum PTrie Kids`. -/
def RB : Sum PTrie Kids → Sum PTrie Kids → Prop
  | .inl a, .inl b => a.refinedBy b
  | .inr a, .inr b => Kids.refinedBy a b
  | _, _ => False

mutual
/-- No hash stub: the witness is revealed (wherever the rows reveal). -/
def Full : PTrie → Prop
  | .hash _ => False
  | .leaf .. => True
  | .ext _ c _ => Full c
  | .branch _ cs _ => KFull cs
def KFull : Kids → Prop
  | .nil => True
  | .none r => KFull r
  | .some c r => Full c ∧ KFull r
end

/-- Revealed and well-formed. -/
def FW : Sum PTrie Kids → Prop
  | .inl t => Full t ∧ t.wf = true
  | .inr ks => KFull ks ∧ ∃ n, Kids.wf ks n = true

/-- **Revealing preserves refinement** of a revealed, well-formed witness (each revealed node is
the witness's node: `refinedBy_of_hash`). -/
theorem rv_refinedBy (hCR : Sha256CR) (hInj : NodeSerInj) {x y : Sum PTrie Kids} (h : Rv x y) :
    ∀ T, RB x T → FW T → RB y T := by
  induction h with
  | refl x => intro T hb _; exact hb
  | stub h n n' hn hw hs hh hr ih =>
    intro T hb hf
    cases T with
    | inr _ => exact hb.elim
    | inl T₀ =>
      simp only [RB, PTrie.refinedBy] at hb
      obtain ⟨hfu, hw₀⟩ := hf
      have hT₀ : ∀ g, T₀ ≠ .hash g := by
        intro g e; subst e; exact hfu
      exact ih (.inl T₀) (refinedBy_of_hash hCR hInj hw hw₀ hn hT₀ hs (hh.trans hb)) ⟨hfu, hw₀⟩
  | ext k c c' m hr ih =>
    intro T hb hf
    cases T with
    | inr _ => exact hb.elim
    | inl T₀ =>
      cases T₀ <;> simp only [RB, PTrie.refinedBy] at hb
      rename_i k₀ c₀ m₀
      obtain ⟨rfl, rfl, hc⟩ := hb
      obtain ⟨hfu, hw₀⟩ := hf
      simp only [PTrie.wf, Bool.and_eq_true] at hw₀
      have := ih (.inl c₀) hc ⟨hfu, hw₀.1.1.2⟩
      simp only [RB, PTrie.refinedBy, true_and] at this ⊢
      exact this
  | branch v cs cs' m hr ih =>
    intro T hb hf
    cases T with
    | inr _ => exact hb.elim
    | inl T₀ =>
      cases T₀ <;> simp only [RB, PTrie.refinedBy] at hb
      rename_i v₀ cs₀ m₀
      obtain ⟨rfl, hv, hc⟩ := hb
      obtain ⟨hfu, hw₀⟩ := hf
      simp only [PTrie.wf, Bool.and_eq_true] at hw₀
      have := ih (.inr cs₀) hc ⟨hfu, 16, hw₀.1.2⟩
      simp only [RB, PTrie.refinedBy, true_and] at this ⊢
      exact ⟨hv, this⟩
  | knone r r' hr ih =>
    intro T hb hf
    cases T with
    | inl _ => exact hb.elim
    | inr T₀ =>
      cases T₀ <;> simp only [RB, Kids.refinedBy] at hb
      rename_i r₀
      obtain ⟨hfu, n, hw₀⟩ := hf
      simp only [Kids.wf, Bool.and_eq_true] at hw₀
      have := ih (.inr r₀) hb ⟨hfu, n - 1, hw₀.2⟩
      simpa only [RB, Kids.refinedBy] using this
  | ksome c c' r r' hc hr ihc ihr =>
    intro T hb hf
    cases T with
    | inl _ => exact hb.elim
    | inr T₀ =>
      cases T₀ <;> simp only [RB, Kids.refinedBy] at hb
      rename_i c₀ r₀
      obtain ⟨⟨hfc, hfr⟩, n, hw₀⟩ := hf
      simp only [Kids.wf, Bool.and_eq_true] at hw₀
      have h1 := ihc (.inl c₀) hb.1 ⟨hfc, hw₀.1.2⟩
      have h2 := ihr (.inr r₀) hb.2 ⟨hfr, n - 1, hw₀.2⟩
      simp only [RB, Kids.refinedBy] at h1 h2 ⊢
      exact ⟨h1, h2⟩

/-- **Collapsing preserves refinement**: replacing revealed nodes by their digests (`hashOf`
is preserved by refinement). -/
theorem rv_collapse {x y : Sum PTrie Kids} (h : Rv x y) : ∀ T, RB y T → RB x T := by
  induction h with
  | refl x => intro T hb; exact hb
  | stub h n n' hn hw hs hh hr ih =>
    intro T hb
    cases T with
    | inr _ => exact hb.elim
    | inl T₀ =>
      have h1 := ih (.inl T₀) hb
      simp only [RB, PTrie.refinedBy] at h1 ⊢
      rw [← hh]; exact PTrie.hashOf_refinedBy _ _ h1
  | ext k c c' m hr ih =>
    intro T hb
    cases T with
    | inr _ => exact hb.elim
    | inl T₀ =>
      cases T₀ <;> simp only [RB, PTrie.refinedBy] at hb
      rename_i k₀ c₀ m₀
      obtain ⟨rfl, rfl, hc⟩ := hb
      have := ih (.inl c₀) hc
      simp only [RB, PTrie.refinedBy, true_and] at this ⊢
      exact this
  | branch v cs cs' m hr ih =>
    intro T hb
    cases T with
    | inr _ => exact hb.elim
    | inl T₀ =>
      cases T₀ <;> simp only [RB, PTrie.refinedBy] at hb
      rename_i v₀ cs₀ m₀
      obtain ⟨rfl, hv, hc⟩ := hb
      have := ih (.inr cs₀) hc
      simp only [RB, PTrie.refinedBy, true_and] at this ⊢
      exact ⟨hv, this⟩
  | knone r r' hr ih =>
    intro T hb
    cases T with
    | inl _ => exact hb.elim
    | inr T₀ =>
      cases T₀ <;> simp only [RB, Kids.refinedBy] at hb
      rename_i r₀
      simpa only [RB, Kids.refinedBy] using ih (.inr r₀) hb
  | ksome c c' r r' hc hr ihc ihr =>
    intro T hb
    cases T with
    | inl _ => exact hb.elim
    | inr T₀ =>
      cases T₀ <;> simp only [RB, Kids.refinedBy] at hb
      rename_i c₀ r₀
      have h1 := ihc (.inl c₀) hb.1
      have h2 := ihr (.inr r₀) hb.2
      simp only [RB, Kids.refinedBy] at h1 h2 ⊢
      exact ⟨h1, h2⟩

/-! ## One change -/

/-- **One batched change.**  The expansion `P` of the change's input ref refines the witness
trie `T`; the rows reveal `P` to `t₁`, take one spec step `C t₁ t₁'` (the chain relation), and
collapse their final nodes, leaving `P'` (the expansion of the output ref).  For any step
relation whose results carry refinement over (`hW`), `P'` refines the spec's result `T'`. -/
theorem change_step (hCR : Sha256CR) (hInj : NodeSerInj) (C : PTrie → PTrie → Prop)
    (F : PTrie → Option PTrie)
    (hW : ∀ t₁ t₁' T, C t₁ t₁' → t₁.refinedBy T → ∃ T', F T = some T' ∧ t₁'.refinedBy T')
    {P t₁ t₁' P' T : PTrie} (hPT : P.refinedBy T) (hF : Full T ∧ T.wf = true)
    (hr : Rv (.inl P) (.inl t₁)) (hc : C t₁ t₁') (hr' : Rv (.inl P') (.inl t₁')) :
    ∃ T', F T = some T' ∧ P'.refinedBy T' := by
  have h1 := rv_refinedBy hCR hInj hr (.inl T) hPT hF
  obtain ⟨T', hT', h2⟩ := hW t₁ t₁' T hc h1
  exact ⟨T', hT', rv_collapse hr' (.inl T') h2⟩

/-- The upsert walk's step relation carries refinement (`PTrie.upsert_refinedBy`). -/
theorem upsert_step (key : List Nat) (x : Bytes) :
    ∀ t₁ t₁' T, UChain t₁ key x t₁' → t₁.refinedBy T →
      ∃ T', T.upsert key x = some T' ∧ t₁'.refinedBy T' := by
  intro t₁ t₁' T hc hr
  exact PTrie.upsert_refinedBy t₁ T key x t₁' hr (uchain_sound hc)

/-- **INTAKE find on a revealed pre-state.**  The rows reveal the stub `prev_state_root` (each
pre-state node hashed by one row and read by the others from `VER` under its digest) and their
find chain answers the spec's `findRef` on the witness trie (up to the value slot). -/
theorem find_step (hCR : Sha256CR) (hInj : NodeSerInj) {P t₁ T : PTrie} {key : List Nat}
    {a : Option Slot} (hPT : P.refinedBy T) (hF : Full T ∧ T.wf = true)
    (hr : Rv (.inl P) (.inl t₁)) (hc : FChain t₁ key a) :
    ∃ a₂, T.findRef key = some a₂ ∧ OptSlotRefines a a₂ :=
  fchain_witness hc T (rv_refinedBy hCR hInj hr (.inl T) hPT hF)

/-! ## All changes (upserts) -/

/-- One upsert change's rows, as the bus-level step will produce them: the rows reveal the
input expansion, run an upsert chain, and collapse to the output expansion. -/
def UpsertRows (P P' : PTrie) (key : List Nat) (x : Bytes) : Prop :=
  ∃ t₁ t₁', Rv (.inl P) (.inl t₁) ∧ UChain t₁ key x t₁' ∧ Rv (.inl P') (.inl t₁')

/-- Upserts keep the witness revealed and well-formed (a property of the spec on the witness;
premise of `batched_upserts`). -/
def UpsertKeepsFW : Prop :=
  ∀ (T T' : PTrie) (key : List Nat) (x : Bytes), Full T ∧ T.wf = true → T.upsert key x = some T' →
    Full T' ∧ T'.wf = true

/-- Fold of upserts (`applyChanges` restricted to present final values). -/
def upserts : PTrie → List (List Nat × Bytes) → Option PTrie
  | t, [] => some t
  | t, (k, x) :: rest => (t.upsert k x).bind fun t' => upserts t' rest

/-- **Batched FINAL, all changes.**  `P : Nat → PTrie` are the expansions of the `TCH` refs
(well defined by `exp_functional`).  `P 0` is the stub `prev_state_root` and the last ref is
a digest `post` (the last change hashes the root).  Then on any revealed witness trie with root
`prev_state_root`, the spec's fold of the changes succeeds and its root hash is `post`. -/
theorem batched_upserts (hCR : Sha256CR) (hInj : NodeSerInj) (hKeep : UpsertKeepsFW) :
    ∀ (cs : List (List Nat × Bytes)) (P : Nat → PTrie) (T : PTrie),
      (P 0).refinedBy T → Full T ∧ T.wf = true →
      (∀ j (hj : j < cs.length), UpsertRows (P j) (P (j + 1)) (cs[j]).1 (cs[j]).2) →
      ∀ post, P cs.length = .hash post →
      ∃ T', upserts T cs = some T' ∧ T'.hashOf = post
  | [], P, T, h0, _, _, post, hn => by
    refine ⟨T, rfl, ?_⟩
    simp only [List.length_nil] at hn
    rw [hn] at h0
    simpa [PTrie.refinedBy] using h0.symm
  | (k, x) :: rest, P, T, h0, hF, hrows, post, hn => by
    obtain ⟨t₁, t₁', hr, hc, hr'⟩ := hrows 0 (by simp)
    obtain ⟨T', hT', h1⟩ := change_step hCR hInj (fun a b => UChain a k x b) (fun t => t.upsert k x)
      (upsert_step k x) h0 hF hr hc hr'
    obtain ⟨T'', h2, h3⟩ := batched_upserts hCR hInj hKeep rest (fun j => P (j + 1)) T' h1
      (hKeep T T' k x hF hT')
      (fun j hj => by
        have := hrows (j + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        exact this) post (by simpa using hn)
    exact ⟨T'', by simp [upserts, hT', h2], h3⟩

/-- `P 0` for a digest ref is the stub, refined by any trie with that root hash. -/
theorem start_refinedBy (T : PTrie) : (PTrie.hash T.hashOf).refinedBy T := stub_refinedBy T

/-! ## All changes: upserts and deletes (`NodeSerInj` discharged by `SerInj.nodeSerInj`) -/

/-- The spec's step of one committed change on a non-empty trie that stays non-empty. -/
def stepOf (k : Bytes) (v : Option Bytes) (T : PTrie) : Option PTrie :=
  match applyChange (some T) k v with
  | some (some T') => some T'
  | _ => none

theorem stepOf_some {k : Bytes} {v : Option Bytes} {T T' : PTrie} (h : stepOf k v T = some T') :
    applyChange (some T) k v = some (some T') := by
  unfold stepOf at h
  split at h
  · rename_i T₁ e; cases h; exact e
  · cases h

/-- One committed change's rows: reveal the input expansion, run the change's chain (an upsert
chain for a present value, a delete chain that leaves a non-empty trie for an absent one),
collapse to the output expansion. -/
def ChangeRows (P P' : PTrie) (k : Bytes) : Option Bytes → Prop
  | some x => ∃ t₁ t₁', Rv (.inl P) (.inl t₁) ∧ UChain t₁ (nibbles k) x t₁' ∧ Rv (.inl P') (.inl t₁')
  | none => ∃ t₁ t₁' b, Rv (.inl P) (.inl t₁) ∧ DChain t₁ (nibbles k) (b, some t₁') ∧
      Rv (.inl P') (.inl t₁')

/-- The delete walk's step relation carries refinement (`Refine.del_refinedBy`). -/
theorem del_step (k : Bytes) :
    ∀ t₁ t₁' T, (∃ b, DChain t₁ (nibbles k) (b, some t₁')) → t₁.refinedBy T →
      ∃ T', stepOf k none T = some T' ∧ t₁'.refinedBy T' := by
  intro t₁ t₁' T ⟨b, hc⟩ hr
  obtain ⟨r₂, hd, -, ho⟩ := StateM5a.Refine.del_refinedBy t₁ T _ _ hr (dchain_sound hc)
  obtain ⟨b₂, o₂⟩ := r₂
  cases o₂ with
  | none => simp [StateM5a.Refine.OptRefines] at ho
  | some T' =>
    refine ⟨T', ?_, ho⟩
    simp [stepOf, applyChange, hd]

/-- Applied changes keep the witness revealed and well-formed (a spec property; premise). -/
def KeepsFW : Prop :=
  ∀ (T T' : PTrie) (k : Bytes) (v : Option Bytes), Full T ∧ T.wf = true →
    applyChange (some T) k v = some (some T') → Full T' ∧ T'.wf = true

/-- **Batched FINAL, every change (upserts and deletes).**  `P j` are the expansions of the
`TCH` refs; `P 0` is the stub `prev_state_root`, the last ref the digest `post`.  On any revealed,
well-formed witness trie with root `prev_state_root`, the spec's `applyChanges` succeeds and its
`rootHash` is `post` — the claim's post-state root.  Premises: `Sha256CR` and `KeepsFW` only
(`NodeSerInj` is `SerInj.nodeSerInj`). -/
theorem batched_changes (hCR : Sha256CR) (hKeep : KeepsFW) :
    ∀ (cs : List (Bytes × Option Bytes)) (P : Nat → PTrie) (T : PTrie),
      (P 0).refinedBy T → Full T ∧ T.wf = true →
      (∀ j (hj : j < cs.length), ChangeRows (P j) (P (j + 1)) (cs[j]).1 (cs[j]).2) →
      ∀ post, P cs.length = .hash post →
      ∃ T', applyChanges (some T) cs = some (some T') ∧ rootHash (some T') = post
  | [], P, T, h0, _, _, post, hn => by
    refine ⟨T, rfl, ?_⟩
    simp only [List.length_nil] at hn
    rw [hn] at h0
    simpa [PTrie.refinedBy, rootHash] using h0.symm
  | (k, v) :: rest, P, T, h0, hF, hrows, post, hn => by
    have hr0 := hrows 0 (by simp)
    simp only [List.getElem_cons_zero] at hr0
    obtain ⟨T₁, hT₁, h1⟩ : ∃ T₁, stepOf k v T = some T₁ ∧ (P 1).refinedBy T₁ := by
      cases v with
      | some x =>
        obtain ⟨t₁, t₁', hr, hc, hr'⟩ := hr0
        obtain ⟨T', hT', h1⟩ := change_step hCR StateM5a.SerInj.nodeSerInj (fun a b => UChain a (nibbles k) x b)
          (fun t => t.upsert (nibbles k) x) (upsert_step (nibbles k) x) h0 hF hr hc hr'
        exact ⟨T', by simp [stepOf, applyChange, hT'], h1⟩
      | none =>
        obtain ⟨t₁, t₁', b, hr, hc, hr'⟩ := hr0
        exact change_step hCR StateM5a.SerInj.nodeSerInj (fun a b' => ∃ b, DChain a (nibbles k) (b, some b'))
          (stepOf k none) (del_step k) h0 hF hr ⟨b, hc⟩ hr'
    have hA := stepOf_some hT₁
    obtain ⟨T'', h2, h3⟩ := batched_changes hCR hKeep rest (fun j => P (j + 1)) T₁ h1
      (hKeep T T₁ k v hF hA)
      (fun j hj => by
        have := hrows (j + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        exact this) post (by simpa using hn)
    exact ⟨T'', by simp [applyChanges, hA, h2], h3⟩

end StateM5a.Store
