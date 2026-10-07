import ZkFormal.NearV3.Assembly.UnfoldStoreEq
import ZkFormal.NearV3.Assembly.ExactReplay

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

/-- Original collision winners for hashes introduced by post-state serialization. -/
def postShadows (original extra : List Bytes) : List Bytes :=
  extra.filterMap (fun b => storeGet (mkStore original) (sha256 b))

theorem postShadows_found (original extra : List Bytes) :
    ∀ b ∈ postShadows original extra, Found (mkStore original) b := by
  intro b hb
  obtain ⟨v,_,hv⟩ := List.mem_filterMap.mp hb
  have he := (storeGet_some hv).1
  unfold Found
  rw [he]
  exact hv

/-- Keep only requested preimages and original winners shadowing new bytes. -/
def postRetained (front original extra : List Bytes) : List Bytes :=
  (front ++ postShadows original extra).eraseDups

theorem postRetained_found {front original extra : List Bytes}
    (hf : ∀ b ∈ front, Found (mkStore original) b) :
    ∀ b ∈ postRetained front original extra, Found (mkStore original) b := by
  intro b hb
  simp only [postRetained,List.mem_eraseDups,List.mem_append] at hb
  exact hb.elim (hf b) (postShadows_found original extra b)

theorem postRetained_hashFunctional {front original extra : List Bytes}
    (hf : ∀ b ∈ front, Found (mkStore original) b) :
    HashFunctional (postRetained front original extra) :=
  hashFunctional_of_found (postRetained_found hf)

theorem postRetained_shadow {front original extra : List Bytes}
    (hf : ∀ b ∈ front, Found (mkStore original) b) {h b v : Bytes}
    (he : storeGet (mkStore extra) h = some b)
    (ho : storeGet (mkStore original) h = some v) :
    storeGet (mkStore (postRetained front original extra)) h = some v := by
  obtain ⟨hh,hb⟩ := storeGet_some he
  have hv : v ∈ postShadows original extra :=
    List.mem_filterMap.mpr ⟨b,hb,by simpa only [hh] using ho⟩
  have hm : v ∈ postRetained front original extra := by
    simp only [postRetained,List.mem_eraseDups,List.mem_append]
    exact Or.inr hv
  have hfound := found_of_mem (postRetained_hashFunctional hf) hm
  unfold Found at hfound
  rw [(storeGet_some ho).1] at hfound
  exact hfound

theorem postRetained_append_subset {front original extra : List Bytes}
    (hf : ∀ b ∈ front, Found (mkStore original) b) :
    StoreSubset (mkStore (postRetained front original extra ++ extra)) (mkStore (original ++ extra)) := by
  intro h b hb
  rw [storeGet_append] at hb ⊢
  cases hs : storeGet (mkStore (postRetained front original extra)) h with
  | some v =>
    simp only [hs,Option.some_or,Option.some.injEq] at hb
    subst b
    have ho := postRetained_found hf v (storeGet_some hs).2
    unfold Found at ho
    rw [(storeGet_some hs).1] at ho
    simp only [ho,Option.some_or]
  | none =>
    simp only [hs,Option.none_or] at hb
    cases ho : storeGet (mkStore original) h with
    | none => simpa only [Option.none_or] using hb
    | some v =>
      have he := postRetained_shadow hf hb ho
      rw [hs] at he
      cases he

theorem storeGet_present_of_mem {ws : List Bytes} {b : Bytes} (hb : b ∈ ws) :
    ∃ v, storeGet (mkStore ws) (sha256 b) = some v := by
  unfold storeGet mkStore
  cases hh : (ws.map (fun v => (sha256 v,v))).find? (fun p => p.1 == sha256 b) with
  | some p => exact ⟨p.2,rfl⟩
  | none =>
    have hp : (sha256 b,b) ∈ ws.map (fun v => (sha256 v,v)) := List.mem_map.mpr ⟨b,hb,rfl⟩
    have hn := List.find?_eq_none.mp hh _ hp
    simp at hn

theorem found_of_subset_mem {small large : List Bytes}
    (hs : StoreSubset (mkStore small) (mkStore large)) {b : Bytes}
    (hb : b ∈ small) (hf : Found (mkStore large) b) : Found (mkStore small) b := by
  obtain ⟨v,hv⟩ := storeGet_present_of_mem hb
  have he := hs _ _ hv
  rw [hf] at he
  cases he
  exact hv

/-- Only post-query blobs whose winner came from the original store. -/
def originalQueries (original : List Bytes) (t : PTrie) : List Bytes :=
  (normalStore t).filter (fun b => storeGet (mkStore original) (sha256 b) == some b)

theorem originalQueries_found (original : List Bytes) (t : PTrie) :
    ∀ b ∈ originalQueries original t, Found (mkStore original) b := by
  intro b hb
  simpa only [beq_iff_eq,Found] using (List.mem_filter.mp hb).2

theorem postRetained_queries_stored {front original extra : List Bytes} {t : PTrie}
    (hf : ∀ b ∈ front, Found (mkStore original) b)
    (hq : ∀ b ∈ originalQueries original t, b ∈ front)
    (ht : Stored (mkStore (original ++ extra)) t) :
    Stored (mkStore (postRetained front original extra ++ extra)) t := by
  have sub := postRetained_append_subset (extra := extra) hf
  have found : ∀ b ∈ normalStore t, Found (mkStore (postRetained front original extra ++ extra)) b := by
    intro b hb
    have old := normalStore_found ht b hb
    apply found_of_subset_mem sub ?_ old
    unfold Found at old
    rw [storeGet_append] at old
    cases ho : storeGet (mkStore original) (sha256 b) with
    | none =>
      simp only [ho,Option.none_or] at old
      exact List.mem_append.mpr (Or.inr (storeGet_some old).2)
    | some v =>
      simp only [ho,Option.some_or,Option.some.injEq] at old
      subst v
      have hq' : b ∈ originalQueries original t := by
        apply List.mem_filter.mpr
        exact ⟨hb,by simpa only [beq_iff_eq,Found] using ho⟩
      apply List.mem_append.mpr
      apply Or.inl
      simp only [postRetained,List.mem_eraseDups,List.mem_append]
      exact Or.inl (hq b hq')
  apply stored_of_occ_found
  intro o ho
  constructor
  · apply found
    simp only [normalStore,List.mem_eraseDups,List.mem_append,List.mem_map]
    exact Or.inl ⟨o,ho,rfl⟩
  · intro b hb
    apply found
    simp only [normalStore,List.mem_eraseDups,List.mem_append]
    exact Or.inr (ownVals_sub ho hb)

/-- Exact post-query replay retains queried original winners plus collision shadows;
it does not require that these blobs appeared in the pre-state trie. -/
theorem postRetained_partialTrie {front original extra : List Bytes}
    (hf : ∀ b ∈ front, Found (mkStore original) b)
    (root : Bytes) (keys : List (List Nat)) (hr : root.length = 32)
    (hq : ∀ b ∈ originalQueries original (partialTrie (original ++ extra) root keys), b ∈ front) :
    partialTrie (postRetained front original extra ++ extra) root keys =
      partialTrie (original ++ extra) root keys := by
  exact buildFor_replay (postRetained_append_subset hf) trieFuel root keys
    (postRetained_queries_stored hf hq (built_spec (original ++ extra) trieFuel root keys hr).2.2.1)

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

theorem postRetained_cost {front original extra : List Bytes}
    (hf : ∀ b ∈ front, Found (mkStore original) b) :
    storeCost (postRetained front original extra) ≤ storeCost original :=
  storeCost_le_of_nodup_sub _ _ (eraseDups_nodup _) (fun b hb =>
    (storeGet_some (postRetained_found hf b hb)).2)

theorem postRetained_payload {front original extra : List Bytes}
    (hf : ∀ b ∈ front, Found (mkStore original) b) :
    ((postRetained front original extra).map List.length).sum ≤ (original.map List.length).sum :=
  weighted_nodup_subset List.length _ _ (eraseDups_nodup _) (fun b hb =>
    (storeGet_some (postRetained_found hf b hb)).2)

/-- Executable targeted original-store selection. No AIR ownership is assigned. -/
def postQueryStore (original extra : List Bytes) (root : Bytes) (keys : List (List Nat)) : List Bytes :=
  postRetained (originalQueries original (partialTrie (original ++ extra) root keys)) original extra

theorem postQueryStore_replay (original extra : List Bytes) (root : Bytes)
    (keys : List (List Nat)) (hr : root.length = 32) :
    partialTrie (postQueryStore original extra root keys ++ extra) root keys =
      partialTrie (original ++ extra) root keys :=
  postRetained_partialTrie (originalQueries_found _ _) root keys hr (fun _ h => h)

theorem postQueryStore_cost (original extra : List Bytes) (root : Bytes) (keys : List (List Nat)) :
    storeCost (postQueryStore original extra root keys) ≤ storeCost original :=
  postRetained_cost (originalQueries_found _ _)

theorem postQueryStore_payload (original extra : List Bytes) (root : Bytes) (keys : List (List Nat)) :
    ((postQueryStore original extra root keys).map List.length).sum ≤ (original.map List.length).sum :=
  postRetained_payload (originalQueries_found _ _)

theorem postRetained_preReplay {front original extra : List Bytes}
    (hf : ∀ b ∈ front, Found (mkStore original) b)
    (root : Bytes) (keys : List (List Nat))
    (hq : ∀ b ∈ normalStore (partialTrie original root keys), b ∈ front) :
    partialTrie (postRetained front original extra) root keys = partialTrie original root keys := by
  have sub : StoreSubset (mkStore (postRetained front original extra)) (mkStore original) := by
    intro h b hb
    have hf' := postRetained_found hf b (storeGet_some hb).2
    unfold Found at hf'
    rw [(storeGet_some hb).1] at hf'
    exact hf'
  apply buildFor_replay sub trieFuel root keys
  have found : ∀ b ∈ normalStore (partialTrie original root keys),
      Found (mkStore (postRetained front original extra)) b := by
    intro b hb
    apply found_of_mem (postRetained_hashFunctional hf)
    simp only [postRetained,List.mem_eraseDups,List.mem_append]
    exact Or.inl (hq b hb)
  apply stored_of_occ_found
  intro o ho
  constructor
  · apply found
    simp only [normalStore,List.mem_eraseDups,List.mem_append,List.mem_map]
    exact Or.inl ⟨o,ho,rfl⟩
  · intro b hb
    apply found
    simp only [normalStore,List.mem_eraseDups,List.mem_append]
    exact Or.inr (ownVals_sub ho hb)

/-- A single restricted original store serves both pre and post queries. -/
def transitionQueryStore (original extra : List Bytes) (preRoot postRoot : Bytes)
    (preKeys postKeys : List (List Nat)) : List Bytes :=
  postRetained (normalStore (partialTrie original preRoot preKeys) ++
    originalQueries original (partialTrie (original ++ extra) postRoot postKeys)) original extra

private theorem transitionQueryStore_front (original extra : List Bytes) (preRoot postRoot : Bytes)
    (preKeys postKeys : List (List Nat)) (hr : preRoot.length = 32) :
    ∀ b ∈ normalStore (partialTrie original preRoot preKeys) ++
      originalQueries original (partialTrie (original ++ extra) postRoot postKeys),
      Found (mkStore original) b := by
  intro b hb
  rcases List.mem_append.mp hb with h | h
  · exact normalStore_found (built_spec original trieFuel preRoot preKeys hr).2.2.1 b h
  · exact originalQueries_found _ _ b h

theorem transitionQueryStore_pre (original extra : List Bytes) (preRoot postRoot : Bytes)
    (preKeys postKeys : List (List Nat)) (hr : preRoot.length = 32) :
    partialTrie (transitionQueryStore original extra preRoot postRoot preKeys postKeys) preRoot preKeys =
      partialTrie original preRoot preKeys :=
  postRetained_preReplay (transitionQueryStore_front _ _ _ _ _ _ hr) preRoot preKeys
    (fun _ h => List.mem_append.mpr (Or.inl h))

theorem transitionQueryStore_post (original extra : List Bytes) (preRoot postRoot : Bytes)
    (preKeys postKeys : List (List Nat)) (hr : preRoot.length = 32) (hp : postRoot.length = 32) :
    partialTrie (transitionQueryStore original extra preRoot postRoot preKeys postKeys ++ extra) postRoot postKeys =
      partialTrie (original ++ extra) postRoot postKeys :=
  postRetained_partialTrie (transitionQueryStore_front _ _ _ _ _ _ hr) postRoot postKeys hp
    (fun _ h => List.mem_append.mpr (Or.inr h))

theorem transitionQueryStore_cost (original extra : List Bytes) (preRoot postRoot : Bytes)
    (preKeys postKeys : List (List Nat)) (hr : preRoot.length = 32) :
    storeCost (transitionQueryStore original extra preRoot postRoot preKeys postKeys) ≤ storeCost original :=
  postRetained_cost (transitionQueryStore_front _ _ _ _ _ _ hr)

end ZkFormal.NearV3.Assembly
