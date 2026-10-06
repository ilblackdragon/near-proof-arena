import ZkFormal.NearV3.Sched.Link.EntryLink

/-!
# Public data: the instance record of a `SchedPub`, and `RawOk`

`instOf sp` is the AIR's per-instance public record (`InstPub`) of the scheduler public data
`sp`: the raw requests are the resolved ones (`rawOf`) with a non-empty increase list, which
`convRaw` keeps anyway (`convRaw_instOf`).

`rawOk_of`: `RawOk (instOf sp)` holds whenever the sender keys of `sp.raw` are distinct, each
sender's `to_shard`s are distinct (A8), and `n ≤ 256`. The resolved `(s, r)` pairs are then
distinct, so there are at most `n² ≤ 2^16` of them. `Pub/Prep.lean` derives the hypotheses from
`prepD0`.
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler NearSpec

/-- The AIR's public instance record of the scheduler public data `sp`. -/
def instOf (sp : SchedPub) : InstPub :=
  ⟨sp.ids, sp.params, sp.allowed,
    (rawOf sp.ids sp.raw).filter (fun q => !(incsOf sp.params q.bm).isEmpty),
    sp.seed, sp.allShardsHash⟩

theorem convRaw_filter (p : Params) (n : Nat) (raw : List RawReq) :
    convRaw p n (raw.filter (fun q => !(incsOf p q.bm).isEmpty)) = convRaw p n raw := by
  induction raw with
  | nil => rfl
  | cons q t ih =>
    simp only [List.filter_cons]
    cases h : incsOf p q.bm with
    | nil => simp [convRaw, h] at ih ⊢; exact ih
    | cons a l => simp [convRaw, h] at ih ⊢; exact ih

theorem convRaw_instOf (sp : SchedPub) :
    convRaw sp.params sp.ids.length (instOf sp).raw = convRaw sp.params sp.ids.length (rawOf sp.ids sp.raw) :=
  convRaw_filter _ _ _

/-! ## `indexOf` -/

theorem indexOf_go_spec (x : Nat) : ∀ (ids : List Nat) (k i : Nat), indexOf.go x ids k = some i →
    k ≤ i ∧ i < k + ids.length ∧ ids[i - k]? = some x
  | [], _, _, h => by simp [indexOf.go] at h
  | y :: ys, k, i, h => by
    simp only [indexOf.go] at h
    split at h
    · rename_i hy
      simp only [Option.some.injEq] at h; subst h; subst hy
      simp
    · obtain ⟨h1, h2, h3⟩ := indexOf_go_spec x ys (k + 1) i h
      refine ⟨by omega, by simp; omega, ?_⟩
      have : i - k = (i - (k + 1)) + 1 := by omega
      rw [this]; simpa using h3

theorem indexOf_spec {ids : List Nat} {x i : Nat} (h : indexOf ids x = some i) :
    i < ids.length ∧ ids[i]? = some x := by
  have := indexOf_go_spec x ids 0 i h
  simpa using this

theorem indexOf_inj {ids : List Nat} {x y i : Nat} (hx : indexOf ids x = some i)
    (hy : indexOf ids y = some i) : x = y := by
  have h1 := (indexOf_spec hx).2
  have h2 := (indexOf_spec hy).2
  rw [h1] at h2; exact Option.some.inj h2

/-! ## Keys of `toBTreeMap` are strictly increasing; its entries come from the input -/

theorem mapInsert_keys {β : Type} (k : Nat) (v : β) :
    ∀ (acc : List (Nat × β)), ∀ x ∈ (mapInsert k v acc).map Prod.fst, x = k ∨ x ∈ acc.map Prod.fst
  | [], x, hx => by simp [mapInsert] at hx; exact Or.inl hx
  | (k', v') :: t, x, hx => by
    simp only [mapInsert] at hx
    split at hx
    · simp at hx; rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by simp [hx])
    · split at hx
      · simp at hx; rcases hx with hx | hx | hx
        · exact Or.inl hx
        · exact Or.inr (by simp [hx])
        · exact Or.inr (by simp [hx])
      · simp only [List.map_cons, List.mem_cons] at hx
        rcases hx with hx | hx
        · exact Or.inr (by simp [hx])
        · rcases mapInsert_keys k v t x hx with h | h
          · exact Or.inl h
          · exact Or.inr (by simp [h])

theorem mapInsert_sorted {β : Type} (k : Nat) (v : β) :
    ∀ (acc : List (Nat × β)), (acc.map Prod.fst).Pairwise (· < ·) →
      ((mapInsert k v acc).map Prod.fst).Pairwise (· < ·)
  | [], _ => by simp [mapInsert]
  | (k', v') :: t, h => by
    simp only [List.map_cons, List.pairwise_cons] at h
    simp only [mapInsert]
    split
    · rename_i e; subst e
      simp only [List.map_cons, List.pairwise_cons]; exact h
    · split
      · rename_i _ hlt
        simp only [List.map_cons, List.pairwise_cons, List.mem_cons]
        refine ⟨?_, h.1, h.2⟩
        intro x hx; rcases hx with hx | hx
        · omega
        · have := h.1 x hx; omega
      · rename_i hne hlt
        simp only [List.map_cons, List.pairwise_cons]
        refine ⟨?_, mapInsert_sorted k v t h.2⟩
        intro x hx
        rcases mapInsert_keys k v t x hx with e | e
        · omega
        · exact h.1 x e

theorem toBTreeMap_sorted {β : Type} (l : List (Nat × β)) :
    ((toBTreeMap l).map Prod.fst).Pairwise (· < ·) := by
  unfold toBTreeMap
  suffices H : ∀ (l : List (Nat × β)) (acc : List (Nat × β)), (acc.map Prod.fst).Pairwise (· < ·) →
      ((l.foldl (fun acc (kv : Nat × β) => mapInsert kv.1 kv.2 acc) acc).map Prod.fst).Pairwise (· < ·) by
    exact H l [] (by simp)
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons kv t ih => intro acc h; exact ih _ (mapInsert_sorted _ _ _ h)

theorem mapInsert_mem {β : Type} (k : Nat) (v : β) :
    ∀ (acc : List (Nat × β)), ∀ e ∈ mapInsert k v acc, e = (k, v) ∨ e ∈ acc
  | [], e, he => by simp [mapInsert] at he; exact Or.inl he
  | (k', v') :: t, e, he => by
    simp only [mapInsert] at he
    split at he
    · simp at he; rcases he with he | he
      · exact Or.inl he
      · exact Or.inr (by simp [he])
    · split at he
      · simp at he; rcases he with he | he | he
        · exact Or.inl he
        · exact Or.inr (by simp [he])
        · exact Or.inr (by simp [he])
      · simp only [List.mem_cons] at he
        rcases he with he | he
        · exact Or.inr (by simp [he])
        · rcases mapInsert_mem k v t e he with h | h
          · exact Or.inl h
          · exact Or.inr (by simp [h])

theorem toBTreeMap_mem {β : Type} (l : List (Nat × β)) : ∀ e ∈ toBTreeMap l, e ∈ l := by
  unfold toBTreeMap
  suffices H : ∀ (l acc : List (Nat × β)), ∀ e ∈ l.foldl (fun acc (kv : Nat × β) => mapInsert kv.1 kv.2 acc) acc,
      e ∈ l ∨ e ∈ acc by
    intro e he
    rcases H l [] e he with h | h
    · exact h
    · simp at h
  intro l
  induction l with
  | nil => intro acc e he; exact Or.inr he
  | cons kv t ih =>
    intro acc e he
    rcases ih _ e he with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases mapInsert_mem _ _ _ e h with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr h

/-! ## `RawOk` -/

theorem nodup_flatMap_of {α β : Type} (f : α → List β) :
    ∀ (l : List α), (∀ x ∈ l, (f x).Nodup) → l.Pairwise (fun a b => ∀ k ∈ f a, k ∉ f b) →
      (l.flatMap f).Nodup
  | [], _, _ => by simp
  | a :: t, h1, h2 => by
    rw [List.pairwise_cons] at h2
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨h1 a (by simp), nodup_flatMap_of f t (fun x hx => h1 x (List.mem_cons_of_mem _ hx)) h2.2, ?_⟩
    intro x hx y hy e
    subst e
    obtain ⟨b, hb, hyb⟩ := List.mem_flatMap.1 hy
    exact h2.1 b hb x hx hyb

theorem nodup_filterMap_of {α β : Type} (f : α → Option β)
    (hinj : ∀ a a' b, f a = some b → f a' = some b → a = a') :
    ∀ (l : List α), l.Nodup → (l.filterMap f).Nodup
  | [], _ => by simp
  | a :: t, h => by
    rw [List.nodup_cons] at h
    rw [List.filterMap_cons]
    cases hfa : f a with
    | none => exact nodup_filterMap_of f hinj t h.2
    | some b =>
      rw [List.nodup_cons]
      refine ⟨?_, nodup_filterMap_of f hinj t h.2⟩
      intro hb
      obtain ⟨a', ha', hfa'⟩ := List.mem_filterMap.1 hb
      exact h.1 (hinj a a' b hfa hfa' ▸ ha')

/-- The link indices of the resolved requests. -/
def rawKeys (ids : List Nat) (raw : List (Nat × List BandwidthRequest)) : List Nat :=
  raw.flatMap fun e => match indexOf ids e.1 with
    | none => []
    | some s => (e.2.map (·.toShard)).filterMap fun t => (indexOf ids t).map (s * ids.length + ·)

theorem rawOf_rawKeys (ids : List Nat) (raw : List (Nat × List BandwidthRequest)) :
    (rawOf ids raw).map (fun q => q.s * ids.length + q.r) = rawKeys ids raw := by
  unfold rawOf rawKeys
  rw [List.map_flatMap]
  congr 1
  funext e
  obtain ⟨sender, brs⟩ := e
  simp only
  cases hs : indexOf ids sender with
  | none => simp
  | some s =>
    induction brs with
    | nil => simp
    | cons b t ih =>
      simp only [List.filterMap_cons, List.map_cons]
      cases hr : indexOf ids b.toShard with
      | none => simpa using ih
      | some r => simpa using ih

theorem keysOf_lt (ids : List Nat) (raw : List (Nat × List BandwidthRequest)) :
    ∀ k ∈ rawKeys ids raw, k < ids.length * ids.length := by
  intro k hk
  simp only [rawKeys, List.mem_flatMap] at hk
  obtain ⟨e, -, he⟩ := hk
  split at he
  · simp at he
  · rename_i s hs
    simp only [List.mem_filterMap, List.mem_map] at he
    obtain ⟨t, -, ht⟩ := he
    cases hr : indexOf ids t with
    | none => simp [hr] at ht
    | some r =>
      simp only [hr, Option.map_some, Option.some.injEq] at ht
      have h1 := (indexOf_spec hs).1
      have h2 := (indexOf_spec hr).1
      subst ht
      have : s * ids.length + r < (s + 1) * ids.length := by rw [Nat.succ_mul]; omega
      exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ (by omega))

theorem keysOf_nodup (ids : List Nat) (raw : List (Nat × List BandwidthRequest))
    (hk : (raw.map Prod.fst).Nodup) (hd : ∀ e ∈ raw, (e.2.map (·.toShard)).Nodup) :
    (rawKeys ids raw).Nodup := by
  unfold rawKeys
  apply nodup_flatMap_of
  · intro e he
    split
    · simp
    · rename_i s hs
      refine nodup_filterMap_of _ ?_ _ (hd e he)
      intro a a' b hb hb'
      cases ha : indexOf ids a with
      | none => simp [ha] at hb
      | some r =>
        cases ha' : indexOf ids a' with
        | none => simp [ha'] at hb'
        | some r' =>
          simp only [ha, ha', Option.map_some, Option.some.injEq] at hb hb'
          have : r = r' := by omega
          subst this
          exact indexOf_inj ha ha'
  · have hp : (raw.map Prod.fst).Pairwise (· ≠ ·) := List.nodup_iff_pairwise_ne.mp hk
    rw [List.pairwise_map] at hp
    refine hp.imp ?_
    intro e e' hne
    intro k hk hk'
    split at hk
    · simp at hk
    · rename_i s hs
      split at hk'
      · simp at hk'
      · rename_i s' hs'
        simp only [List.mem_filterMap, List.mem_map] at hk hk'
        obtain ⟨t, -, ht⟩ := hk
        obtain ⟨t', -, ht'⟩ := hk'
        cases hr : indexOf ids t with
        | none => simp [hr] at ht
        | some r =>
          cases hr' : indexOf ids t' with
          | none => simp [hr'] at ht'
          | some r' =>
            simp only [hr, hr', Option.map_some, Option.some.injEq] at ht ht'
            have h1 := (indexOf_spec hr).1
            have h2 := (indexOf_spec hr').1
            have hss : s = s' := by
              have e1 : (s * ids.length + r) / ids.length = s := by
                rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h1]; simp
              have e2 : (s' * ids.length + r') / ids.length = s' := by
                rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h2]; simp
              rw [← e1, ← e2, ht, ht']
            subst hss
            exact hne (indexOf_inj hs hs')

/-- **`RawOk` of the instance record**, from distinct sender keys, distinct `to_shard`s per
sender (A8) and `n ≤ 256`. -/
theorem rawOk_of (sp : SchedPub) (hn : sp.ids.length ≤ 256)
    (hk : (sp.raw.map Prod.fst).Nodup) (hd : ∀ e ∈ sp.raw, (e.2.map (·.toShard)).Nodup) :
    RawOk (instOf sp) := by
  refine ⟨?_, ?_⟩
  · have h1 : (instOf sp).raw.length ≤ (rawOf sp.ids sp.raw).length := List.length_filter_le _ _
    have h2 : (rawKeys sp.ids sp.raw).length ≤ (List.range (sp.ids.length * sp.ids.length)).length :=
      length_le_of_nodup_subset _ _ (keysOf_nodup _ _ hk hd)
        (fun x hx => List.mem_range.2 (keysOf_lt _ _ x hx))
    rw [← rawOf_rawKeys, List.length_map, List.length_range] at h2
    have h3 : sp.ids.length * sp.ids.length ≤ 256 * 256 := Nat.mul_le_mul hn hn
    show (instOf sp).raw.length ≤ 2 ^ 16
    omega
  · intro q hq
    simp only [instOf, List.mem_filter] at hq
    obtain ⟨hq, hne⟩ := hq
    simp only [rawOf, List.mem_flatMap, List.mem_filterMap] at hq
    obtain ⟨e, -, br, -, hb⟩ := hq
    cases hs : indexOf sp.ids e.1 with
    | none => simp [hs] at hb
    | some s =>
      cases hr : indexOf sp.ids br.toShard with
      | none => simp [hs, hr] at hb
      | some r =>
        simp only [hs, hr, Option.some.injEq] at hb
        subst hb
        refine ⟨(indexOf_spec hs).1, (indexOf_spec hr).1, ?_⟩
        simpa [instOf, List.isEmpty_iff] using hne

end ZkFormal.NearV3.Sched
