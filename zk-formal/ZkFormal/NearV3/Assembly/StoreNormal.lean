import ZkFormal.NearV3.Spec.Occs

/-! Candidate store normalization. The native store is FIRST-wins. These
lemmas do not assume SHA injectivity, StoreDag/A6, or distinct input digests. -/
namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

private theorem find_filter_ne {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (a : α) (p : α → Bool) (hp : p a = false) :
    (xs.filter fun b => !(b == a)).find? p = xs.find? p := by
  rw [List.find?_filter]
  congr 1
  funext b
  by_cases h : b = a
  · subst b; simp [hp]
  · simp [h]

/-- Stable first-occurrence dedup preserves every first-match predicate,
including predicates induced by noninjective hash functions. -/
theorem find_eraseDups {α : Type} [BEq α] [LawfulBEq α]
    (p : α → Bool) (xs : List α) : xs.eraseDups.find? p = xs.find? p := by
  match xs with
  | [] => rfl
  | a :: xs =>
    rw [List.eraseDups_cons]
    cases hp : p a with
    | true => simp [List.find?_cons, hp]
    | false =>
      simp only [List.find?_cons, hp, Bool.false_eq_true, ↓reduceIte]
      rw [find_eraseDups p, find_filter_ne xs a p hp]
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

/-- Exact native lookup preservation, even if different bytes collide. -/
theorem storeGet_eraseDups (ws : List Bytes) (h : Bytes) :
    storeGet (mkStore ws.eraseDups) h = storeGet (mkStore ws) h := by
  simp only [storeGet, mkStore, List.find?_map, Function.comp_def, find_eraseDups]

private theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) : xs.eraseDups.Nodup := by
  match xs with
  | [] => simp
  | a :: xs =>
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨?_, eraseDups_nodup _⟩
    simp
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

/-- Serialized vector payload, including each entry's u32 length prefix. -/
def entryCost (b : Bytes) : Nat := 4 + b.length

def storeCost (ws : List Bytes) : Nat := 4 + (ws.map entryCost).sum

private theorem cost_erase {x : Bytes} : ∀ {ws : List Bytes}, x ∈ ws →
    (ws.map entryCost).sum = entryCost x + ((ws.erase x).map entryCost).sum
  | [], h => by simp at h
  | y :: ys, h => by
    by_cases e : y = x
    · subst e; simp
    · have hx : x ∈ ys := by simpa [List.mem_cons, Ne.symm e] using h
      simp only [List.map_cons, List.sum_cons, List.erase_cons, beq_iff_eq, e, ↓reduceIte]
      rw [cost_erase hx]; omega

/-- Membership plus uniqueness bounds the full encoded cost, not just payload bytes. -/
theorem storeCost_le_of_nodup_sub : ∀ (xs ws : List Bytes), xs.Nodup →
    (∀ b ∈ xs, b ∈ ws) → storeCost xs ≤ storeCost ws
  | [], ws, _, _ => by simp [storeCost]
  | x :: xs, ws, hn, hs => by
    rw [List.nodup_cons] at hn
    have hx : x ∈ ws := hs x (by simp)
    have ih := storeCost_le_of_nodup_sub xs (ws.erase x) hn.2 (fun y hy => by
      have hyx : y ≠ x := fun e => hn.1 (e ▸ hy)
      exact (List.mem_erase_of_ne hyx).2 (hs y (by simp [hy])))
    unfold storeCost at ih ⊢
    rw [cost_erase hx]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem storeCost_eraseDups (ws : List Bytes) : storeCost ws.eraseDups ≤ storeCost ws :=
  storeCost_le_of_nodup_sub _ _ (eraseDups_nodup _) (fun _ h => List.mem_eraseDups.mp h)

/-- Regenerated occurrence bytes, with sharing and node/value overlap collapsed. -/
def normalStore (t : PTrie) : List Bytes :=
  ((occs t).map nodeEnc ++ valsOf t).eraseDups

theorem normalStore_found {s : Store} {t : PTrie} (ht : Stored s t) :
    ∀ b ∈ normalStore t, Found s b := by
  intro b hb
  simp only [normalStore, List.mem_eraseDups, List.mem_append, List.mem_map] at hb
  rcases hb with ⟨o, ho, rfl⟩ | hv
  · exact stored_found (occs_stored s t ht o ho) (occs_isNode t o ho)
  · obtain ⟨o, ho, hb⟩ := List.mem_flatMap.mp hv
    exact stored_ownVals (occs_stored s t ht o ho) b hb

/-- No graph acyclicity, hash injectivity or node/value separation is required. -/
theorem normalStore_cost {ws : List Bytes} {t : PTrie}
    (ht : Stored (mkStore ws) t) : storeCost (normalStore t) ≤ storeCost ws := by
  apply storeCost_le_of_nodup_sub _ _ (eraseDups_nodup _)
  intro b hb
  exact (storeGet_some (normalStore_found ht b hb)).2

theorem normalStore_hashFunctional {s : Store} {t : PTrie} (ht : Stored s t) :
    HashFunctional (normalStore t) := by
  intro a ha b hb he
  exact found_inj (normalStore_found ht a ha) (normalStore_found ht b hb) he

/-- A normalized occurrence store cannot introduce a different collision winner. -/
theorem normalStore_lookup_sub {ws : List Bytes} {t : PTrie}
    (ht : Stored (mkStore ws) t) {h b : Bytes}
    (hb : storeGet (mkStore (normalStore t)) h = some b) :
    storeGet (mkStore ws) h = some b := by
  obtain ⟨hh, hm⟩ := storeGet_some hb
  rw [← hh]
  exact normalStore_found ht b hm

/-- Actual native partial-trie construction supplies the store-cost premise. -/
theorem partialTrie_normalStore_cost (ws : List Bytes) (root : Bytes)
    (keys : List (List Nat)) (hr : root.length = 32) :
    storeCost (normalStore (partialTrie ws root keys)) ≤ storeCost ws :=
  normalStore_cost (built_spec ws trieFuel root keys hr).2.2.1

theorem buildFor_store_congr {s₁ s₂ : Store}
    (hs : ∀ h, storeGet s₁ h = storeGet s₂ h) (fuel : Nat) :
    buildFor s₁ fuel = buildFor s₂ fuel := by
  induction fuel with
  | zero => rfl
  | succ f ih =>
    funext root keys
    simp only [buildFor, hs, ih, mkSlot]

/-- Stable byte dedup leaves every native partial-trie computation unchanged. -/
theorem partialTrie_eraseDups (ws : List Bytes) (root : Bytes)
    (keys : List (List Nat)) :
    partialTrie ws.eraseDups root keys = partialTrie ws root keys := by
  exact congrFun (congrFun (buildFor_store_congr (storeGet_eraseDups ws) trieFuel) root) keys

end ZkFormal.NearV3.Assembly
