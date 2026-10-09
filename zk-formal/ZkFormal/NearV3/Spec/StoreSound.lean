import ZkFormal.NearV3.Spec.Records

/-!
# ZkFormal.NearV3.Spec.StoreSound — `StoreBuildStmt` (soundness direction)

* `treeOf3_fuel`, `fullTree_unfold` — under `RootedDag`, the unfolding of a
  `τ` record does not depend on the fuel beyond `ns.length - n`;
* `fullTree_wf`, `fullTree_stored` — the unfolded trie is `PTrie.wf` and, if
  the store is `HashFunctional`, `Stored` in `mkStore (storeOf ns vs τ)`;
* **`storeBuild`** — `partialTrie (storeOf ns vs τ) (digest ns vs root) keys`
  refines `fullTree ns vs root`, has hash `digest ns vs root`, and agrees with
  it on `find` for every read key.
-/

namespace ZkFormal.NearV3

open NearSpec NearSpecV3

variable {ns : List NodeRec3} {vs : List ValRec3} {τ root : Nat}

/-! ## Congruence and fuel -/

theorem kidsOf3_congr {g g' : Nat → PTrie} :
    ∀ kids : List Kid3, (∀ c, Kid3.node c ∈ kids → g c = g' c) → kidsOf3 g kids = kidsOf3 g' kids
  | [], _ => rfl
  | kid :: r, h => by
    have ih := kidsOf3_congr r (fun c hc => h c (List.mem_cons_of_mem _ hc))
    cases kid with
    | none => simp [kidsOf3, ih]
    | hash _ => simp [kidsOf3, ih]
    | node c => simp [kidsOf3, ih, h c (by simp)]

theorem nodeTree3_congr {g g' : Nat → PTrie} (r : Rec3) (h : ∀ c, Kid3.node c ∈ r.kids → g c = g' c) :
    nodeTree3 vs g r = nodeTree3 vs g' r := by
  cases r with
  | leaf => rfl
  | ext k kid m =>
    cases kid with
    | node c => simp [nodeTree3, kidTree3, h c (by simp [Rec3.kids])]
    | _ => rfl
  | branch v kids m => simp [nodeTree3, kidsOf3_congr kids (fun c hc => h c (by simpa [Rec3.kids]))]

theorem InInst.lt {n : Nat} (h : InInst ns τ n) : n < ns.length := by
  obtain ⟨nr, hn, -⟩ := h
  exact (List.getElem?_eq_some_iff.1 hn).1

theorem treeOf3_fuel_eq (hd : RootedDag ns vs τ root) :
    ∀ f f' n, InInst ns τ n → ns.length - n ≤ f → ns.length - n ≤ f' →
      treeOf3 ns vs f n = treeOf3 ns vs f' n := by
  intro f
  induction f with
  | zero => intro f' n hn h0 _; have := hn.lt; omega
  | succ f ih =>
    intro f' n hn hf hf'
    obtain ⟨f'', rfl⟩ : ∃ f'', f' = f'' + 1 := ⟨f' - 1, by have := hn.lt; omega⟩
    obtain ⟨nr, hnr, ht⟩ := hn
    simp only [treeOf3, hnr]
    apply nodeTree3_congr
    intro c hc
    obtain ⟨hlt, hcI⟩ := hd.child n nr hnr ht c hc
    exact ih f'' c hcI (by omega) (by omega)

theorem treeOf3_fuel (hd : RootedDag ns vs τ root) {f n : Nat} (hn : InInst ns τ n)
    (hf : ns.length - n ≤ f) : treeOf3 ns vs f n = fullTree ns vs n :=
  treeOf3_fuel_eq hd f ns.length n hn hf (by omega)

theorem fullTree_unfold (hd : RootedDag ns vs τ root) {n : Nat} {nr : NodeRec3}
    (hnr : ns[n]? = some nr) (ht : nr.tau = τ) :
    fullTree ns vs n = nodeTree3 vs (fullTree ns vs) nr.node := by
  have hn : InInst ns τ n := ⟨nr, hnr, ht⟩
  obtain ⟨f, hf⟩ : ∃ f, ns.length = f + 1 := ⟨ns.length - 1, by have := hn.lt; omega⟩
  have h1 : fullTree ns vs n = treeOf3 ns vs (f + 1) n := by unfold fullTree; rw [hf]
  rw [h1]
  simp only [treeOf3, hnr]
  apply nodeTree3_congr
  intro c hc
  obtain ⟨hlt, hcI⟩ := hd.child n nr hnr ht c hc
  exact treeOf3_fuel hd hcI (by omega)

/-- Induction over the `τ` records along the DAG (children first). -/
theorem dag_induction (hd : RootedDag ns vs τ root) (P : Nat → Prop)
    (step : ∀ n nr, ns[n]? = some nr → nr.tau = τ →
      (∀ c, Kid3.node c ∈ nr.node.kids → P c) → P n) :
    ∀ n, InInst ns τ n → P n := by
  have key : ∀ d n, InInst ns τ n → ns.length - n ≤ d → P n := by
    intro d
    induction d with
    | zero => intro n hn h; have := hn.lt; omega
    | succ d ih =>
      intro n hn hle
      obtain ⟨nr, hnr, ht⟩ := hn
      apply step n nr hnr ht
      intro c hc
      obtain ⟨hlt, hcI⟩ := hd.child n nr hnr ht c hc
      exact ih c hcI (by have := hcI.lt; omega)
  exact fun n hn => key _ n hn (Nat.le_refl _)

/-! ## Well-formedness -/

theorem kidsOf3_wf (g : Nat → PTrie) : ∀ kids : List Kid3,
    (∀ kid ∈ kids, kid.wf) → (∀ c, Kid3.node c ∈ kids → (g c).wf = true) →
    Kids.wf (kidsOf3 g kids) kids.length = true
  | [], _, _ => by simp [kidsOf3, Kids.wf]
  | kid :: r, hw, hg => by
    have ih := kidsOf3_wf g r (fun k hk => hw k (List.mem_cons_of_mem _ hk))
      (fun c hc => hg c (List.mem_cons_of_mem _ hc))
    have hk := hw kid (by simp)
    cases kid with
    | none => simp [kidsOf3, Kids.wf, ih]
    | hash h => simp [Kid3.wf] at hk; simp [kidsOf3, Kids.wf, PTrie.wf, ih, hk]
    | node c => simp [kidsOf3, Kids.wf, ih, hg c (by simp)]

theorem slot3_ok (s : VSlot3) (h : s.wf vs) : slotOk (slot3 vs s) = true := by
  cases s with
  | ref len hh => simp [VSlot3.wf] at h; simp [slot3, slotOk, h]
  | val i => simp [VSlot3.wf] at h; simp [slot3, slotOk, h]

theorem fullTree_wf (hd : RootedDag ns vs τ root) :
    ∀ n, InInst ns τ n → (fullTree ns vs n).wf = true := by
  apply dag_induction hd
  intro n nr hnr ht ih
  rw [fullTree_unfold hd hnr ht]
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
    simp only [nodeTree3, PTrie.wf, Bool.and_eq_true, hv, hk, decide_eq_true_eq]
    exact ⟨⟨hv, trivial⟩, h4⟩

/-! ## Storage -/

theorem nodeEnc_mem {n : Nat} (hn : InInst ns τ n) :
    nodeEnc (fullTree ns vs n) ∈ storeOf ns vs τ := by
  obtain ⟨nr, hnr, ht⟩ := hn
  apply List.mem_append_left
  simp only [nodeEntries, List.mem_filterMap, List.mem_range]
  exact ⟨n, (List.getElem?_eq_some_iff.1 hnr).1, by simp [hnr, ht]⟩

theorem valOf_mem {i : Nat} {vr : ValRec3} (hv : vs[i]? = some vr) (ht : vr.tau = τ) :
    valOf vs i ∈ storeOf ns vs τ := by
  apply List.mem_append_right
  simp only [valEntries, valOf, hv, Option.map_some, Option.getD_some]
  exact List.mem_map.2 ⟨vr, List.mem_filter.2 ⟨List.mem_of_getElem? hv, by simp [ht]⟩, rfl⟩

theorem kidsOf3_stored (s : Store) (g : Nat → PTrie) : ∀ kids : List Kid3,
    (∀ c, Kid3.node c ∈ kids → Stored s (g c)) → KidsStored s (kidsOf3 g kids)
  | [], _ => by simp [kidsOf3, KidsStored]
  | kid :: r, hg => by
    have ih := kidsOf3_stored s g r (fun c hc => hg c (List.mem_cons_of_mem _ hc))
    cases kid with
    | none => simpa [kidsOf3, KidsStored] using ih
    | hash h => simp [kidsOf3, KidsStored, Stored, ih]
    | node c => exact ⟨hg c (by simp), ih⟩

theorem fullTree_stored (hd : RootedDag ns vs τ root) (hf : HashFunctional (storeOf ns vs τ)) :
    ∀ n, InInst ns τ n → Stored (mkStore (storeOf ns vs τ)) (fullTree ns vs n) := by
  apply dag_induction hd
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
  rw [fullTree_unfold hd hnr ht] at hF ⊢
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

/-! ## `StoreBuildStmt` -/

/-- **`StoreBuildStmt`.** For a hash-functional rooted DAG, NearSpecV3's
partial trie over the record store refines the unfolded record trie, has the
root digest as hash, and answers every read key exactly like it. -/
theorem storeBuild (ns : List NodeRec3) (vs : List ValRec3) (τ root : Nat) (keys : List (List Nat))
    (hf : HashFunctional (storeOf ns vs τ)) (hd : RootedDag ns vs τ root)
    (hp : PathsRevealed ns vs root keys) :
    (partialTrie (storeOf ns vs τ) (digest ns vs root) keys).refinedBy (fullTree ns vs root) ∧
    (partialTrie (storeOf ns vs τ) (digest ns vs root) keys).hashOf = digest ns vs root ∧
    ∀ k ∈ keys, (partialTrie (storeOf ns vs τ) (digest ns vs root) keys).find k =
      (fullTree ns vs root).find k := by
  have hw := fullTree_wf hd root hd.root_inst
  have hs := fullTree_stored hd hf root hd.root_inst
  have h := buildFor_spec (mkStore (storeOf ns vs τ)) trieFuel (fullTree ns vs root) keys hw hs
    (fun k hk => (hp k hk).1)
  refine ⟨h.1, PTrie.hashOf_refinedBy _ _ h.1, fun k hk => h.2 k hk (hp k hk).2⟩

/-- The statement as named in V3-D0-DESIGN §6.2. -/
def StoreBuildStmt : Prop :=
  ∀ (ns : List NodeRec3) (vs : List ValRec3) (τ root : Nat) (keys : List (List Nat)),
    HashFunctional (storeOf ns vs τ) → RootedDag ns vs τ root → PathsRevealed ns vs root keys →
    (partialTrie (storeOf ns vs τ) (digest ns vs root) keys).hashOf = digest ns vs root ∧
    ∀ k ∈ keys, (partialTrie (storeOf ns vs τ) (digest ns vs root) keys).find k =
      (fullTree ns vs root).find k

theorem storeBuildStmt : StoreBuildStmt := fun ns vs τ root keys hf hd hp =>
  let h := storeBuild ns vs τ root keys hf hd hp
  ⟨h.2.1, h.2.2⟩

end ZkFormal.NearV3
