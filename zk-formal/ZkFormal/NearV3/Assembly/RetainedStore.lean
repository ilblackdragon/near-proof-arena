import ZkFormal.NearV3.Assembly.NativePayload

/-! Semantic store extension only. Retained blobs are not allocated as AIR value
rows here: their per-instance ownership and the unchanged value-byte capacity
must be proved separately before integrating any concrete view allocator. -/
namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

def retainedStore (front original : List Bytes) : List Bytes :=
  (front ++ original).eraseDups

private theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) : xs.eraseDups.Nodup := by
  match xs with
  | [] => simp
  | a :: xs =>
    rw [List.eraseDups_cons,List.nodup_cons]
    refine ⟨?_,eraseDups_nodup _⟩
    simp
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

theorem storeGet_append (a b : List Bytes) (h : Bytes) :
    storeGet (mkStore (a++b)) h =
      (storeGet (mkStore a) h).or (storeGet (mkStore b) h) := by
  simp only [storeGet,mkStore,List.map_append,List.find?_append]
  cases (List.find? (fun x : Bytes × Bytes => x.1 == h) (a.map fun v => (sha256 v,v))) <;> rfl

theorem storeGet_found_prefix {front original : List Bytes}
    (hp : ∀ b ∈ front, Found (mkStore original) b) (h : Bytes) :
    storeGet (mkStore (front++original)) h = storeGet (mkStore original) h := by
  rw [storeGet_append]
  cases he : storeGet (mkStore front) h with
  | none => rfl
  | some b =>
    obtain ⟨hh,hm⟩ := storeGet_some he
    have ho : storeGet (mkStore original) h = some b := by
      rw [←hh]
      exact hp b hm
    simp only [ho,Option.or_some,Option.getD_some]

theorem retainedStore_lookup {front original : List Bytes}
    (hp : ∀ b ∈ front, Found (mkStore original) b) (h : Bytes) :
    storeGet (mkStore (retainedStore front original)) h = storeGet (mkStore original) h := by
  rw [retainedStore,storeGet_eraseDups]
  exact storeGet_found_prefix hp h

theorem retainedStore_mem {front original : List Bytes}
    (hp : ∀ b ∈ front, Found (mkStore original) b) {b : Bytes}
    (hb : b ∈ retainedStore front original) : b ∈ original := by
  rw [retainedStore,List.mem_eraseDups,List.mem_append] at hb
  exact hb.elim (fun h => (storeGet_some (hp b h)).2) id

theorem retainedStore_cost {front original : List Bytes}
    (hp : ∀ b ∈ front, Found (mkStore original) b) :
    storeCost (retainedStore front original) ≤ storeCost original :=
  storeCost_le_of_nodup_sub _ _ (eraseDups_nodup _) (fun _ hb => retainedStore_mem hp hb)

theorem retainedStore_payload {front original : List Bytes}
    (hp : ∀ b ∈ front, Found (mkStore original) b) :
    ((retainedStore front original).map List.length).sum ≤ (original.map List.length).sum :=
  weighted_nodup_subset List.length _ _ (eraseDups_nodup _) (fun _ hb => retainedStore_mem hp hb)

theorem retainedStore_partialTrie {front original : List Bytes}
    (hp : ∀ b ∈ front, Found (mkStore original) b) (root : Bytes) (keys : List (List Nat)) :
    partialTrie (retainedStore front original) root keys = partialTrie original root keys := by
  unfold partialTrie
  rw [buildFor_store_congr (retainedStore_lookup hp)]

theorem retainedStore_rebuildPost {front original : List Bytes}
    (hp : ∀ b ∈ front, Found (mkStore original) b) (post : PTrie) (keys : List (List Nat)) :
    rebuildPost (retainedStore front original) post keys = rebuildPost original post keys := by
  unfold rebuildPost partialTrie
  apply congrFun (congrFun (buildFor_store_congr ?_ trieFuel) post.hashOf) keys
  intro h
  simp only [storeGet_append,retainedStore_lookup hp]

/-- Distinct original blobs not already represented by the view store. -/
def retainedExtra (front original : List Bytes) : List Bytes :=
  original.eraseDups.filter (fun b => !front.contains b)

theorem retainedExtra_mem {front original : List Bytes} {b : Bytes} :
    b ∈ retainedExtra front original ↔ b ∈ original ∧ b ∉ front := by
  simp [retainedExtra]

theorem retainedExtra_payload (front original : List Bytes) :
    ((retainedExtra front original).map List.length).sum ≤ (original.map List.length).sum := by
  apply weighted_nodup_subset List.length _ _
    ((eraseDups_nodup original).sublist (List.filter_sublist))
  intro b hb
  exact (retainedExtra_mem.mp hb).1

theorem retainedExtra_singleton (b : Bytes) : retainedExtra [] [b] = [b] := by
  simp [retainedExtra,List.eraseDups_cons]

/-- The native 3MB payload limit alone does not imply the 2MiB AIR value-byte
limit for retained extras. This is a size-domain example, not an accepted
transition counterexample. No large byte list is evaluated by the proof. -/
theorem retainedExtra_capacity_gap :
    let original := [List.replicate 2097153 (0 : UInt8)]
    (original.map List.length).sum ≤ 3000000 ∧
      2097152 < ((retainedExtra [] original).map List.length).sum := by
  dsimp only
  rw [retainedExtra_singleton]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_replicate,Nat.add_zero]
  decide

end ZkFormal.NearV3.Assembly
