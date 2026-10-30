import NearSpecV3.Successor.TierO6
import NearSpecV3.Logged.TrieHash

/-! # L0 row validation: masked and dead d2-core guards (Gate-B, `allFeatures`)

Each lemma states why a d2-core guard of the canonical checker (`checkReshardCoreObs` /
`checkD2CoreGWith`, which share the guard sequence) can never be the first failing check, or can
never fail at all. The coverage tool (`tools/d3/lean_chunk_coverage.py`, `promote_row`) names these
lemmas in the rows' evidence; it checks that each named lemma is declared in this file.

* `L0-D2-006` (`invalid: empty chain segment`) is subsumed by `L0-D2-021`
  (`segment does not start at prev_block_hash`): with no block, the guard compares `[]` with the chunk
  header's `prev_block_hash`, which the decoder reads as exactly 32 bytes.
* `L0-D2-007` (`epoch table not strictly ascending`) is subsumed by `L0-D2-008` (`epoch table does
  not match the referenced epochs`): the referenced list is `dedupSorted`, which is strictly ascending.
* `L0-D2-009` (`epoch_id not in the epoch table`) is subsumed by `L0-D2-008`: the referenced list
  contains the claim's `epoch_id`.
* `L0-D2-038` (`bandwidth scheduler params (assert panics)`) never fails: the PV 86 configuration
  satisfies `BandwidthSchedulerParams::calculate`'s assertions for every shard count.
* `L0-D2-039` (`main base_state does not hash to prev_state_root`) never fails: a trie revealed from a
  hash-addressed store hashes to the root it was revealed from (`Logged.hashOf_revealAll`).
-/

namespace NearSpecV3.L0Guards
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Successor

/-! ## L0-D2-006 ⊂ L0-D2-021 -/

theorem takeN_length : ∀ (n : Nat) (bs out rest : Bytes), takeN n bs = some (out, rest) → out.length = n
  | 0, bs, out, rest, h => by simp [takeN] at h; obtain ⟨rfl, -⟩ := h; rfl
  | n + 1, [], out, rest, h => by simp [takeN] at h
  | n + 1, b :: bs, out, rest, h => by
    simp only [takeN] at h
    cases hr : takeN n bs with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨o, r⟩ := p
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [takeN_length n bs o r hr]

theorem readHash_length {bs out rest : Bytes} (h : readHash bs = some (out, rest)) : out.length = 32 :=
  takeN_length 32 bs out rest h

/-- `pChunkInner` reads `prev_block_hash` with `pHash` (`Wire.lean`), which yields 32 bytes. -/
theorem pHash_length {w : String} {bs out rest : Bytes} (h : pHash w bs = .ok (out, rest)) :
    out.length = 32 := by
  unfold pHash lift at h
  split at h
  · rename_i x hx
    cases h
    exact readHash_length hx
  · cases h

/-- The empty-segment guard: with no block, the start guard (`L0-D2-021`) compares `[]` with
`prev_block_hash`, so it fails whenever `prev_block_hash` is non-empty. -/
theorem empty_segment_fails_start (hashes : List Bytes) (pbh : Bytes) (hb : hashes = [])
    (hp : pbh.length = 32) : (hashes.headD [] == pbh) = false := by
  subst hb
  cases pbh with
  | nil => simp at hp
  | cons _ _ => rfl

/-! ## L0-D2-009 ⊂ L0-D2-008 -/

/-- If the epoch table's ids equal the referenced epochs (`L0-D2-008` passes), the claim's own epoch
is in the table (`L0-D2-009` passes). -/
theorem epoch_in_table_of_referenced (c : Claim) (rest : List Bytes)
    (h8 : (c.epochs.map (·.epochId) == dedupSorted (c.epochId :: rest)) = true) :
    (c.epochs.find? (·.epochId == c.epochId)).isSome = true := by
  have htab : c.epochs.map (·.epochId) = dedupSorted (c.epochId :: rest) := by simpa using h8
  have hm : c.epochId ∈ c.epochs.map (·.epochId) := by
    rw [htab]; exact mem_dedupSorted _ _ List.mem_cons_self
  obtain ⟨r, hr, hre⟩ := List.mem_map.mp hm
  cases hf : c.epochs.find? (·.epochId == c.epochId) with
  | some _ => rfl
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp [hre]) (hf r hr)

/-! ## L0-D2-007 ⊂ L0-D2-008 -/

theorem bytesLt_irrefl : ∀ a : Bytes, bytesLt a a = false
  | [] => rfl
  | a :: as => by simp [bytesLt, bytesLt_irrefl as]

/-- Trichotomy of the byte order. -/
theorem bytesLt_total : ∀ a b : Bytes, bytesLt a b = false → bytesLt b a = false → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [bytesLt] at h
  | _ :: _, [], _, h => by simp [bytesLt] at h
  | x :: xs, y :: ys, h1, h2 => by
    simp only [bytesLt] at h1 h2
    by_cases hxy : x.toNat < y.toNat
    · simp [hxy] at h1
    · by_cases hyx : y.toNat < x.toNat
      · simp [hyx] at h2
      · simp [hxy, hyx] at h1 h2
        have : x = y := UInt8.toNat_inj.mp (by omega)
        subst this
        rw [bytesLt_total xs ys h1 h2]

theorem bytesLt_trans : ∀ a b c : Bytes, bytesLt a b = true → bytesLt b c = true → bytesLt a c = true
  | [], [], _, h, _ => by simp [bytesLt] at h
  | [], _ :: _, [], _, h => by simp [bytesLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [bytesLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [bytesLt] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [bytesLt] at h1 h2 ⊢
    by_cases hxz : x.toNat < z.toNat
    · simp only [hxz, ↓reduceIte]
    · simp only [hxz, ↓reduceIte]
      by_cases hxy : x.toNat < y.toNat
      · by_cases hyz : y.toNat < z.toNat
        · omega
        · simp only [hyz, ↓reduceIte] at h2
          by_cases hzy : z.toNat < y.toNat
          · simp only [hzy, ↓reduceIte, Bool.false_eq_true] at h2
          · omega
      · simp only [hxy, ↓reduceIte] at h1
        by_cases hyx : y.toNat < x.toNat
        · simp only [hyx, ↓reduceIte, Bool.false_eq_true] at h1
        · simp only [hyx, ↓reduceIte] at h1
          by_cases hyz : y.toNat < z.toNat
          · omega
          · simp only [hyz, ↓reduceIte] at h2
            by_cases hzy : z.toNat < y.toNat
            · simp only [hzy, ↓reduceIte, Bool.false_eq_true] at h2
            · simp only [hzy, ↓reduceIte] at h2
              have hzx : ¬ z.toNat < x.toNat := by omega
              simp only [hzx, ↓reduceIte]
              exact bytesLt_trans xs ys zs h1 h2

/-- Non-strictly ascending: no element is smaller than its predecessor. -/
def Asc : List (Bytes × Option Bytes) → Prop
  | a :: b :: rest => bytesLt b.1 a.1 = false ∧ Asc (b :: rest)
  | _ => True

theorem asc_insertSorted (p : Bytes × Option Bytes) :
    ∀ l, Asc l → Asc (insertSorted p l)
  | [], _ => trivial
  | [q], _ => by
    simp only [insertSorted]
    split
    · rename_i h
      refine ⟨?_, trivial⟩
      cases hq : bytesLt q.1 p.1
      · rfl
      · have := bytesLt_trans p.1 q.1 p.1 h hq
        rw [bytesLt_irrefl] at this; cases this
    · rename_i h
      exact ⟨by simpa using h, trivial⟩
  | q :: r :: rest, ⟨hqr, hrest⟩ => by
    simp only [insertSorted]
    split
    · rename_i h
      refine ⟨?_, hqr, hrest⟩
      cases hq : bytesLt q.1 p.1
      · rfl
      · have := bytesLt_trans p.1 q.1 p.1 h hq
        rw [bytesLt_irrefl] at this; cases this
    · rename_i h
      have ih := asc_insertSorted p (r :: rest) hrest
      have hp : bytesLt p.1 q.1 = false := by simpa using h
      revert ih
      simp only [insertSorted]
      split
      · intro ih; exact ⟨hp, ih⟩
      · intro ih; exact ⟨hqr, ih⟩

theorem asc_sortKV (l : List (Bytes × Option Bytes)) : Asc (sortKV l) := by
  unfold sortKV
  suffices ∀ acc, Asc acc → Asc (l.foldl (fun acc p => insertSorted p acc) acc) from this [] trivial
  induction l with
  | nil => intro acc h; exact h
  | cons p ps ih => intro acc h; exact ih _ (asc_insertSorted p acc h)

/-- The fold of `dedupStep` over a non-strictly ascending list: strictly ascending, and its head
(if any) is the list's head key. -/
theorem dedup_foldr_spec : ∀ L : List (Bytes × Option Bytes), Asc L →
    strictlyAscending (L.foldr dedupStep []) = true ∧
      (L.foldr dedupStep []).head? = L.head?.map (·.1)
  | [], _ => ⟨rfl, rfl⟩
  | [kv], _ => by obtain ⟨k, v⟩ := kv; exact ⟨rfl, rfl⟩
  | kv :: kv2 :: rest, ⟨h12, hrest⟩ => by
    obtain ⟨ih1, ih2⟩ := dedup_foldr_spec (kv2 :: rest) hrest
    obtain ⟨k, v⟩ := kv
    rw [List.foldr_cons]
    generalize hacc : (kv2 :: rest).foldr dedupStep [] = acc at ih1 ih2
    cases acc with
    | nil => simp at ih2
    | cons k' tl =>
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at ih2
      subst ih2
      simp only [dedupStep]
      split
      · rename_i heq
        have : k = kv2.1 := by simpa using heq
        subst this
        exact ⟨ih1, rfl⟩
      · rename_i hne
        refine ⟨?_, rfl⟩
        simp only [strictlyAscending, ih1, Bool.and_true]
        have hne' : k ≠ kv2.1 := by simpa using hne
        cases hlt : bytesLt k kv2.1
        · exact absurd (bytesLt_total _ _ hlt h12) hne'
        · rfl

theorem strictlyAscending_dedupSorted (l : List Bytes) : strictlyAscending (dedupSorted l) = true := by
  rw [dedupSorted_eq]
  exact (dedup_foldr_spec _ (asc_sortKV _)).1

/-- If the epoch table's ids equal the referenced epochs (`L0-D2-008` passes), they are strictly
ascending (`L0-D2-007` passes). -/
theorem ascending_of_referenced (ids referenced : List Bytes) (l : List Bytes)
    (hr : referenced = dedupSorted l) (h8 : (ids == referenced) = true) :
    strictlyAscending ids = true := by
  have : ids = referenced := by simpa using h8
  rw [this, hr]; exact strictlyAscending_dedupSorted l

/-! ## L0-D2-038 and L0-D2-039: checks that never fail -/

theorem scheduler_params_pv86 (n : Nat) :
    (Scheduler.Params.calculate Scheduler.Config.pv86 n).isSome = true := by
  simp [Scheduler.Params.calculate, Scheduler.Config.pv86]

theorem base_state_hashes (merged : List Bytes) (fuel : Nat) (root : Bytes) :
    (revealAll (mkHStore merged) fuel root).hashOf = root :=
  Logged.hashOf_revealAll (Logged.HInv_mkHStore merged) fuel root

end NearSpecV3.L0Guards
