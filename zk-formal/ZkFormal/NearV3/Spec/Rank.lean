import ZkFormal.NearV3.Spec.StoreSound

/-!
# ZkFormal.NearV3.Spec.Rank — `StoreBuildStmt` for ranked records and weak `uniq`

Lane `v3-trie` (lead decision, V3-D0-DESIGN §11: A6 rejected, weak `uniq`, tree-shaped
records).  Two generalisations of `Spec/StoreSound.lean`:

* **`RootedDagR ns vs τ root rk`** — `RootedDag` with id order replaced by an arbitrary
  rank: a child `c` of a `τ` record `n` has `rk n < rk c`.  The AIR's tree-shaped node
  records give the rank `depth` (v1 `PARENT (cid, depth+1, …)`), not id order.  The
  unfolding `fullTree` (fuel `ns.length`) is fuel-stable under any rank, by the measure
  `μ n = #{m | τ record, rk n < rk m}` (`mu_child`).  `storeBuildR` is `storeBuild` for
  ranked records; `rootedDag_R` recovers the id-order case.
* **Weak uniqueness** — `WeakUniq key bytes l`: a list sorted non-strictly by `key` in which
  consecutive entries with equal keys have equal bytes.  `weakUniq_functional`: any two
  entries with equal keys have equal bytes (the relation `<` or `= ∧ bytes =` is transitive,
  so the chain is pairwise).  `hashFunctional_of_weakUniq`: if the witness store of
  instance `τ` is (as a multiset) the byte column of a weakly unique list keyed by digest,
  it is `HashFunctional` — exactly what `buildFor` needs.  This replaces
  `DigestsDistinct` (strict `uniq`), which an honest witness with two identical subtrees
  in different positions (tree-shaped records) or a value byte-equal to a node cannot
  satisfy.
-/

namespace ZkFormal.NearV3

open NearSpec NearSpecV3

/-! ## Ranked rooted DAGs -/

/-- Rooted records of instance `τ`, acyclic by a rank `rk` (children have larger rank). -/
structure RootedDagR (ns : List NodeRec3) (vs : List ValRec3) (τ root : Nat) (rk : Nat → Nat) :
    Prop where
  root_inst : InInst ns τ root
  child : ∀ (n : Nat) (nr : NodeRec3), ns[n]? = some nr → nr.tau = τ → ∀ c, Kid3.node c ∈ nr.node.kids →
    rk n < rk c ∧ InInst ns τ c
  vals : ∀ (n : Nat) (nr : NodeRec3), ns[n]? = some nr → nr.tau = τ → ∀ i ∈ nr.node.vids,
    ∃ vr : ValRec3, vs[i]? = some vr ∧ vr.tau = τ
  wf : ∀ (n : Nat) (nr : NodeRec3), ns[n]? = some nr → nr.tau = τ → nr.node.wf vs

/-- Id order is a rank. -/
theorem rootedDag_R {ns : List NodeRec3} {vs : List ValRec3} {τ root : Nat}
    (h : RootedDag ns vs τ root) : RootedDagR ns vs τ root id :=
  ⟨h.root_inst, fun n nr h1 h2 c hc => h.child n nr h1 h2 c hc, h.vals, h.wf⟩

variable {ns : List NodeRec3} {vs : List ValRec3} {τ root : Nat} {rk : Nat → Nat}

/-- Boolean form of `InInst`. -/
def inInstB (ns : List NodeRec3) (τ m : Nat) : Bool := (ns[m]?.map (·.tau == τ)).getD false

theorem inInstB_iff {m : Nat} : inInstB ns τ m = true ↔ InInst ns τ m := by
  unfold inInstB InInst
  cases h : ns[m]? with
  | none => simp
  | some nr => simp

/-- Number of `τ` records ranked strictly above `n`. -/
def mu (ns : List NodeRec3) (τ : Nat) (rk : Nat → Nat) (n : Nat) : Nat :=
  (List.range ns.length).countP fun m => inInstB ns τ m && decide (rk n < rk m)

theorem countP_lt_of {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) → (∃ x ∈ l, q x = true ∧ p x = false) →
      l.countP p < l.countP q
  | [], _, ⟨x, hx, _⟩ => by simp at hx
  | a :: l, himp, ⟨x, hx, hqx, hpx⟩ => by
    have hle : l.countP p ≤ l.countP q :=
      List.countP_mono_left (fun y hy hp => himp y (List.mem_cons_of_mem _ hy) hp)
    simp only [List.countP_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · simp only [hqx, hpx]; simp; omega
    · have := countP_lt_of p q l (fun y hy hp => himp y (List.mem_cons_of_mem _ hy) hp) ⟨x, hx, hqx, hpx⟩
      have hab : (if p a = true then 1 else 0) ≤ (if q a = true then 1 else 0) := by
        by_cases hp : p a = true
        · simp [hp, himp a (by simp) hp]
        · simp [hp]
      omega

theorem mu_lt_length {n : Nat} (hn : InInst ns τ n) : mu ns τ rk n < ns.length := by
  unfold mu
  have h1 : (List.range ns.length).countP (fun m => inInstB ns τ m && decide (rk n < rk m)) <
      (List.range ns.length).countP (fun _ => true) :=
    countP_lt_of _ _ _ (fun _ _ _ => rfl) ⟨n, List.mem_range.2 hn.lt, rfl, by simp⟩
  simpa using h1

theorem mu_child {n c : Nat} (hlt : rk n < rk c) (hc : InInst ns τ c) : mu ns τ rk c < mu ns τ rk n := by
  unfold mu
  apply countP_lt_of
  · intro m _ h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨h.1, by omega⟩
  · refine ⟨c, List.mem_range.2 hc.lt, ?_, ?_⟩
    · simp [(inInstB_iff).2 hc, hlt]
    · simp

theorem treeOf3_fuel_eqR (hd : RootedDagR ns vs τ root rk) :
    ∀ f f' n, InInst ns τ n → mu ns τ rk n < f → mu ns τ rk n < f' →
      treeOf3 ns vs f n = treeOf3 ns vs f' n := by
  intro f
  induction f with
  | zero => intro f' n hn h0 _; omega
  | succ f ih =>
    intro f' n hn hf hf'
    obtain ⟨f'', rfl⟩ : ∃ f'', f' = f'' + 1 := ⟨f' - 1, by omega⟩
    obtain ⟨nr, hnr, ht⟩ := hn
    simp only [treeOf3, hnr]
    apply nodeTree3_congr
    intro c hc
    obtain ⟨hlt, hcI⟩ := hd.child n nr hnr ht c hc
    have := mu_child (ns := ns) hlt hcI
    exact ih f'' c hcI (by omega) (by omega)

theorem treeOf3_fuelR (hd : RootedDagR ns vs τ root rk) {f n : Nat} (hn : InInst ns τ n)
    (hf : mu ns τ rk n < f) : treeOf3 ns vs f n = fullTree ns vs n :=
  treeOf3_fuel_eqR hd f ns.length n hn hf (mu_lt_length hn)

theorem fullTree_unfoldR (hd : RootedDagR ns vs τ root rk) {n : Nat} {nr : NodeRec3}
    (hnr : ns[n]? = some nr) (ht : nr.tau = τ) :
    fullTree ns vs n = nodeTree3 vs (fullTree ns vs) nr.node := by
  have hn : InInst ns τ n := ⟨nr, hnr, ht⟩
  have hm := mu_lt_length (rk := rk) hn
  obtain ⟨f, hf⟩ : ∃ f, ns.length = f + 1 := ⟨ns.length - 1, by omega⟩
  have h1 : fullTree ns vs n = treeOf3 ns vs (f + 1) n := by unfold fullTree; rw [hf]
  rw [h1]
  simp only [treeOf3, hnr]
  apply nodeTree3_congr
  intro c hc
  obtain ⟨hlt, hcI⟩ := hd.child n nr hnr ht c hc
  have := mu_child (ns := ns) hlt hcI
  exact treeOf3_fuelR hd hcI (by omega)

/-- Induction over the `τ` records along the ranked DAG (children first). -/
theorem dag_inductionR (hd : RootedDagR ns vs τ root rk) (P : Nat → Prop)
    (step : ∀ n nr, ns[n]? = some nr → nr.tau = τ →
      (∀ c, Kid3.node c ∈ nr.node.kids → P c) → P n) :
    ∀ n, InInst ns τ n → P n := by
  have key : ∀ d n, InInst ns τ n → mu ns τ rk n < d → P n := by
    intro d
    induction d with
    | zero => intro n _ h; omega
    | succ d ih =>
      intro n hn hle
      obtain ⟨nr, hnr, ht⟩ := hn
      apply step n nr hnr ht
      intro c hc
      obtain ⟨hlt, hcI⟩ := hd.child n nr hnr ht c hc
      have := mu_child (ns := ns) hlt hcI
      exact ih c hcI (by omega)
  exact fun n hn => key _ n hn (Nat.lt_succ_self _)

theorem fullTree_wfR (hd : RootedDagR ns vs τ root rk) :
    ∀ n, InInst ns τ n → (fullTree ns vs n).wf = true := by
  apply dag_inductionR hd
  intro n nr hnr ht ih
  rw [fullTree_unfoldR hd hnr ht]
  have hw := hd.wf n nr hnr ht
  cases hr : nr.node with
  | leaf k v m =>
    rw [hr] at hw
    obtain ⟨h1, h2, h3, h4⟩ := hw
    simp [nodeTree3, PTrie.wf, h1, h2, h4, slot3_ok v h3]
  | ext k kid m =>
    rw [hr] at hw ih
    obtain ⟨h1, h2, h3, h4, h5⟩ := hw
    have hc : (kidTree3 (fullTree ns vs) kid).wf = true := by
      cases kid with
      | none => exact absurd rfl h3
      | hash h => simp [Kid3.wf] at h4; simp [kidTree3, PTrie.wf, h4]
      | node c => exact ih c (by simp [Rec3.kids])
    simp [nodeTree3, PTrie.wf, h1, h2, h5, hc]
  | branch v kids m =>
    rw [hr] at hw ih
    obtain ⟨h1, h2, h3, h4⟩ := hw
    have hk := kidsOf3_wf (fullTree ns vs) kids h3 (fun c hc => ih c (by simpa [Rec3.kids]))
    rw [h1] at hk
    have hv : (match v.map (slot3 vs) with | some s => slotOk s | none => true) = true := by
      cases v with
      | none => rfl
      | some s => exact slot3_ok s (h2 s rfl)
    simp only [nodeTree3, PTrie.wf, Bool.and_eq_true, hk, decide_eq_true_eq]
    exact ⟨⟨hv, trivial⟩, h4⟩

theorem fullTree_storedR (hd : RootedDagR ns vs τ root rk) (hf : HashFunctional (storeOf ns vs τ)) :
    ∀ n, InInst ns τ n → Stored (mkStore (storeOf ns vs τ)) (fullTree ns vs n) := by
  apply dag_inductionR hd
  intro n nr hnr ht ih
  have hF : Found (mkStore (storeOf ns vs τ)) (nodeEnc (fullTree ns vs n)) :=
    found_of_mem hf (nodeEnc_mem ⟨nr, hnr, ht⟩)
  have hvals := hd.vals n nr hnr ht
  have hslot : ∀ s : VSlot3, (∀ i, s = .val i → i ∈ nr.node.vids) →
      SlotStored (mkStore (storeOf ns vs τ)) (slot3 vs s) := by
    intro s hs
    cases s with
    | ref => trivial
    | val i =>
      obtain ⟨vr, hv, hvt⟩ := hvals i (hs i rfl)
      exact found_of_mem hf (valOf_mem hv hvt)
  rw [fullTree_unfoldR hd hnr ht] at hF ⊢
  cases hr : nr.node with
  | leaf k v m =>
    rw [hr] at hF
    exact ⟨hF, hslot v (fun i hi => by simp [hr, hi, Rec3.vids])⟩
  | ext k kid m =>
    rw [hr] at hF ih
    refine ⟨hF, ?_⟩
    cases kid with
    | none => trivial
    | hash h => trivial
    | node c => exact ih c (by simp [Rec3.kids])
  | branch v kids m =>
    rw [hr] at hF ih
    refine ⟨hF, ?_, kidsOf3_stored _ _ kids (fun c hc => ih c (by simpa [Rec3.kids]))⟩
    cases v with
    | none => trivial
    | some s => exact hslot s (fun i hi => by simp [hr, hi, Rec3.vids])

/-- **`StoreBuildStmt` for ranked records.** -/
theorem storeBuildR (ns : List NodeRec3) (vs : List ValRec3) (τ root : Nat) (rk : Nat → Nat)
    (keys : List (List Nat))
    (hf : HashFunctional (storeOf ns vs τ)) (hd : RootedDagR ns vs τ root rk)
    (hp : PathsRevealed ns vs root keys) :
    (partialTrie (storeOf ns vs τ) (digest ns vs root) keys).refinedBy (fullTree ns vs root) ∧
    (partialTrie (storeOf ns vs τ) (digest ns vs root) keys).hashOf = digest ns vs root ∧
    ∀ k ∈ keys, (partialTrie (storeOf ns vs τ) (digest ns vs root) keys).find k =
      (fullTree ns vs root).find k := by
  have hw := fullTree_wfR hd root hd.root_inst
  have hs := fullTree_storedR hd hf root hd.root_inst
  have h := buildFor_spec (mkStore (storeOf ns vs τ)) trieFuel (fullTree ns vs root) keys hw hs
    (fun k hk => (hp k hk).1)
  refine ⟨h.1, PTrie.hashOf_refinedBy _ _ h.1, fun k hk => h.2 k hk (hp k hk).2⟩


/-! ## Fuel from bounded ranks -/

theorem kfdepth_kidsOf3 (g : Nat → PTrie) : ∀ (kids : List Kid3) (j : Nat) (key : List Nat),
    kfdepth (kidsOf3 g kids) j key = 0 ∨ ∃ c, Kid3.node c ∈ kids ∧ kfdepth (kidsOf3 g kids) j key = fdepth (g c) key
  | [], j, key => by left; cases j <;> simp [kidsOf3, kfdepth]
  | kid :: r, j, key => by
    have ih := kfdepth_kidsOf3 g r
    cases kid with
    | none =>
      cases j with
      | zero => left; simp [kidsOf3, kfdepth]
      | succ j =>
        rcases ih j key with h | ⟨c, hc, h⟩
        · left; simpa [kidsOf3, kfdepth] using h
        · right; exact ⟨c, List.mem_cons_of_mem _ hc, by simpa [kidsOf3, kfdepth] using h⟩
    | hash h =>
      cases j with
      | zero => left; simp [kidsOf3, kfdepth, fdepth]
      | succ j =>
        rcases ih j key with h | ⟨c, hc, h⟩
        · left; simpa [kidsOf3, kfdepth] using h
        · right; exact ⟨c, List.mem_cons_of_mem _ hc, by simpa [kidsOf3, kfdepth] using h⟩
    | node c =>
      cases j with
      | zero => right; exact ⟨c, by simp, by simp [kidsOf3, kfdepth]⟩
      | succ j =>
        rcases ih j key with h | ⟨c', hc, h⟩
        · left; simpa [kidsOf3, kfdepth] using h
        · right; exact ⟨c', List.mem_cons_of_mem _ hc, by simpa [kidsOf3, kfdepth] using h⟩

/-- Ranks below `B` bound the number of revealed nodes any lookup visits. -/
theorem fdepth_le_rank (hd : RootedDagR ns vs τ root rk) (B : Nat)
    (hB : ∀ n, InInst ns τ n → rk n < B) :
    ∀ n, InInst ns τ n → ∀ key, fdepth (fullTree ns vs n) key ≤ B - rk n := by
  apply dag_inductionR hd
  intro n nr hnr ht ih key
  have hn : rk n < B := hB n ⟨nr, hnr, ht⟩
  rw [fullTree_unfoldR hd hnr ht]
  cases hr : nr.node with
  | leaf k v m => simp [nodeTree3, fdepth]; omega
  | ext k kid m =>
    simp only [nodeTree3, fdepth]
    split
    · cases kid with
      | none => simp [kidTree3, fdepth]; omega
      | hash h => simp [kidTree3, fdepth]; omega
      | node c =>
        have hc : Kid3.node c ∈ nr.node.kids := by simp [hr, Rec3.kids]
        obtain ⟨hlt, hcI⟩ := hd.child n nr hnr ht c hc
        have := ih c hc (key.drop k.length)
        have := hB c hcI
        simp only [kidTree3]; omega
    · omega
  | branch v kids m =>
    cases key with
    | nil => simp [nodeTree3, fdepth]; omega
    | cons j r =>
      simp only [nodeTree3, fdepth]
      rcases kfdepth_kidsOf3 (fullTree ns vs) kids j r with h | ⟨c, hc, h⟩
      · omega
      · have hc' : Kid3.node c ∈ nr.node.kids := by simp [hr, Rec3.kids, hc]
        obtain ⟨hlt, hcI⟩ := hd.child n nr hnr ht c hc'
        have := ih c hc' r
        have := hB c hcI
        omega

/-- `PathsRevealed` from determined lookups and ranks below `trieFuel`. -/
theorem pathsRevealed_of_rank (hd : RootedDagR ns vs τ root rk)
    (hB : ∀ n, InInst ns τ n → rk n < trieFuel) (keys : List (List Nat))
    (hf : ∀ k ∈ keys, (fullTree ns vs root).find k ≠ none) : PathsRevealed ns vs root keys :=
  fun k hk => ⟨hf k hk, Nat.le_trans (fdepth_le_rank hd trieFuel hB root hd.root_inst k) (Nat.sub_le _ _)⟩

/-! ## Weak uniqueness -/

/-- Sorted by `key` (non-strictly); consecutive equal keys carry equal bytes. -/
def WeakStep {α : Type} (key : α → Nat) (bytes : α → Bytes) (a b : α) : Prop :=
  key a < key b ∨ (key a = key b ∧ bytes a = bytes b)

def WeakUniq {α : Type} (key : α → Nat) (bytes : α → Bytes) : List α → Prop
  | a :: b :: r => WeakStep key bytes a b ∧ WeakUniq key bytes (b :: r)
  | _ => True

theorem weakStep_trans {α : Type} {key : α → Nat} {bytes : α → Bytes} {a b c : α}
    (h1 : WeakStep key bytes a b) (h2 : WeakStep key bytes b c) : WeakStep key bytes a c := by
  unfold WeakStep at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩

theorem weakUniq_tail {α : Type} {key : α → Nat} {bytes : α → Bytes} {a : α} {l : List α}
    (h : WeakUniq key bytes (a :: l)) : WeakUniq key bytes l := by
  cases l with
  | nil => trivial
  | cons b r => exact h.2

theorem weakUniq_head {α : Type} {key : α → Nat} {bytes : α → Bytes} :
    ∀ {a : α} {l : List α}, WeakUniq key bytes (a :: l) → ∀ b ∈ l, WeakStep key bytes a b
  | _, [], _, b, hb => by simp at hb
  | a, c :: r, h, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h.1
    · exact weakStep_trans h.1 (weakUniq_head h.2 b hb)

/-- **Weak uniqueness is functional**: equal keys ⇒ equal bytes, for any two entries. -/
theorem weakUniq_functional {α : Type} {key : α → Nat} {bytes : α → Bytes} :
    ∀ {l : List α}, WeakUniq key bytes l → ∀ a ∈ l, ∀ b ∈ l, key a = key b → bytes a = bytes b
  | [], _, a, ha, _, _, _ => by simp at ha
  | x :: xs, h, a, ha, b, hb, he => by
    have hx : ∀ y ∈ xs, key x = key y → bytes x = bytes y := by
      intro y hy hk
      rcases weakUniq_head h y hy with h1 | ⟨-, h1⟩
      · omega
      · exact h1
    have ha' := List.mem_cons.1 ha
    have hb' := List.mem_cons.1 hb
    rcases ha' with ha' | ha'
    · rcases hb' with hb' | hb'
      · rw [ha', hb']
      · rw [ha'] at he ⊢; exact hx b hb' he
    · rcases hb' with hb' | hb'
      · rw [hb'] at he ⊢; exact (hx a ha' he.symm).symm
      · exact weakUniq_functional (weakUniq_tail h) a ha' b hb' he

/-- A store is hash-functional if it is the byte column of a weakly unique list whose
key is (an injective function of) the SHA-256 digest of the bytes. -/
theorem hashFunctional_of_weakUniq {α : Type} {key : α → Nat} {bytes : α → Bytes} {l : List α}
    (h : WeakUniq key bytes l) (dkey : Bytes → Nat)
    (hkey : ∀ a ∈ l, key a = dkey (sha256 (bytes a)))
    (st : List Bytes) (hst : ∀ x ∈ st, ∃ a ∈ l, bytes a = x) : HashFunctional st := by
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := hst x hx
  obtain ⟨b, hb, rfl⟩ := hst y hy
  apply weakUniq_functional h a ha b hb
  rw [hkey a ha, hkey b hb, hxy]

end ZkFormal.NearV3
