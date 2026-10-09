import ReexecV3D3.ReadCanon
import ReexecV3D3.NormalForm

/-! Read-set filtering preserves precisely the queried answers. -/
namespace ReexecV3D3.Read
open NearSpec NearSpecV3 NearSpecV3.D2

/-- Hash-based filtering of a canonical pool is literal store restriction. -/
theorem hGet_filter_hash {P : List Bytes} (hu : UH P) (keep : Bytes → Bool) (h : Bytes) :
    hGet (mkHStore (P.filter fun v => keep (sha256 v))) h =
      if keep h then hGet (mkHStore P) h else none := by
  have hu' : UH (P.filter fun v => keep (sha256 v)) :=
    hu.sub (fun _ hv => (List.mem_filter.mp hv).1)
  by_cases hk : keep h = true
  · rw [if_pos hk]
    cases he : hGet (mkHStore P) h with
    | none =>
      apply hGet_none_of
      intro v hv hh
      have hm := (List.mem_filter.mp hv).1
      have hg := hGet_UH_mem hu hm
      rw [hh, he] at hg
      cases hg
    | some v =>
      obtain ⟨hh, hv⟩ := hGet_some he
      have hv' : v ∈ P.filter (fun x => keep (sha256 x)) :=
        List.mem_filter.mpr ⟨hv, by simpa [hh] using hk⟩
      rw [← hh]
      exact hGet_UH_mem hu' hv'
  · rw [if_neg hk]
    apply hGet_none_of
    intro v hv hh
    exact hk (hh ▸ (List.mem_filter.mp hv).2)

/-- Only hashes of the selected transition contribute to its pool. -/
theorem mem_readHashes {keys : List (Nat × Bytes)} {tag : Nat} {h : Bytes} :
    h ∈ readHashes keys tag ↔ (tag, h) ∈ keys := by
  simp only [readHashes, List.mem_filterMap]
  constructor
  · rintro ⟨⟨t, v⟩, hm, he⟩
    dsimp only at he
    split at he
    · rename_i ht
      have ht' : t = tag := by simpa using ht
      have hv : v = h := Option.some.inj he
      simpa [ht', hv] using hm
    · cases he
  · intro hm
    exact ⟨(tag, h), hm, by simp⟩

/-- A second restriction to the same read keys removes no additional values. -/
theorem filter_readHashes_idempotent (keys : List (Nat × Bytes)) (tag : Nat) (P : List Bytes) :
    (P.filter fun v => (readHashes keys tag).contains (sha256 v)).filter
      (fun v => (readHashes keys tag).contains (sha256 v)) =
    P.filter (fun v => (readHashes keys tag).contains (sha256 v)) := by
  simp only [List.filter_filter, Bool.and_self]

theorem restrictPools_length (keys : List (Nat × Bytes)) (X : Pools) :
    (restrictPools keys X).2.length = X.2.length := by
  simp [restrictPools]

/-- The main pool contains exactly the successful answers for tag zero. -/
theorem restrictPools_main_get (keys : List (Nat × Bytes)) (X : Pools) (hu : UH X.1)
    (h : Bytes) :
    hGet (mkHStore (restrictPools keys X).1) h =
      if (0, h) ∈ keys then hGet (mkHStore X.1) h else none := by
  rw [restrictPools, hGet_filter_hash hu]
  simp only [List.contains_iff_mem, mem_readHashes]

/-- Indexed implicit-pool restriction is pointwise a sublist operation. -/
theorem restrictImplicit_sub (keys : List (Nat × Bytes)) :
    ∀ (L : List (List Bytes)) (start : Nat),
      SubL (L.zipIdx start |>.map fun (vs, k) =>
        vs.filter (fun v => (readHashes keys (k + 1)).contains (sha256 v))) L
  | [], _ => trivial
  | vs :: rest, start => by
    simp only [List.zipIdx_cons, List.map_cons]
    exact ⟨List.filter_sublist, restrictImplicit_sub keys rest (start + 1)⟩

theorem restrictPools_sub (keys : List (Nat × Bytes)) (X : Pools) :
    SubP (restrictPools keys X) X :=
  ⟨List.filter_sublist, restrictImplicit_sub keys X.2 0⟩

/-- Repeating the same per-transition restriction is a fixed point. -/
theorem restrictImplicit_idempotent (keys : List (Nat × Bytes)) :
    ∀ (L : List (List Bytes)) (start : Nat),
      (((L.zipIdx start).map fun (vs, k) =>
        vs.filter (fun v => (readHashes keys (k + 1)).contains (sha256 v))).zipIdx start).map
          (fun (vs, k) => vs.filter (fun v => (readHashes keys (k + 1)).contains (sha256 v))) =
      (L.zipIdx start).map (fun (vs, k) =>
        vs.filter (fun v => (readHashes keys (k + 1)).contains (sha256 v)))
  | [], _ => rfl
  | vs :: rest, start => by
    simp only [List.zipIdx_cons, List.map_cons]
    rw [filter_readHashes_idempotent, restrictImplicit_idempotent keys rest (start + 1)]

theorem restrictPools_idempotent (keys : List (Nat × Bytes)) (X : Pools) :
    restrictPools keys (restrictPools keys X) = restrictPools keys X := by
  apply Prod.ext
  · exact filter_readHashes_idempotent keys 0 X.1
  · exact restrictImplicit_idempotent keys X.2 0

/-- The tagged recorded stores represented by a pair of canonical pools. -/
def poolStore (X : Pools) : Nat × Bytes → Option Bytes :=
  storesOfW (mkHStore X.1) (X.2.map mkHStore)

/-- Pool filtering implements the exact partial-store restriction, including
queries whose original answer was missing. -/
theorem poolStore_restrict (keys : List (Nat × Bytes)) (X : Pools)
    (g1 : GoodPool X.1) (g2 : GoodL X.2) :
    poolStore (restrictPools keys X) = Logged.SM.restrict (poolStore X) keys := by
  funext key
  rcases key with ⟨tag, h⟩
  cases tag with
  | zero =>
    have hh := restrictPools_main_get keys X g1.uh h
    by_cases hm : (0, h) ∈ keys <;>
      simpa [poolStore, storesOfW, Logged.SM.restrict, hm] using hh
  | succ k =>
    simp only [poolStore, storesOfW, restrictPools, List.getElem?_map,
      List.getElem?_zipIdx, Option.map_map, Nat.zero_add]
    cases he : X.2[k]? with
    | none => simp [Logged.SM.restrict, poolStore, storesOfW, List.getElem?_map, he]
    | some P =>
      have hp : P ∈ X.2 := List.mem_of_getElem? he
      have hu := (g2.mem P hp).uh
      simp only [Option.map_some, Function.comp_def]
      rw [hGet_filter_hash hu]
      simp [Logged.SM.restrict, poolStore, storesOfW, List.getElem?_map, he,
        List.contains_iff_mem, mem_readHashes]

end ReexecV3D3.Read
