import ReexecV3D3.TrieQ
import ReexecV3D3.Canon

/-!
# Value pools: one value per hash, byte order, and the store they answer

`poolOf vals` (the store's answers for the hashes of `vals`, sorted) answers every lookup exactly
like the store built from `vals` (`hGet_poolOf`). A list with one value per hash (`UH`) answers
by membership alone, so any rearrangement of it is the same store (`hGet_UH_congr`), and
`poolOf` of a rearrangement of a sorted pool is that pool (`poolOf_perm`).
-/

namespace ReexecV3D3

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## The byte order is a total order -/

theorem bytesLe_refl : ∀ a : Bytes, bytesLe a a = true
  | [] => rfl
  | x :: xs => by simp [bytesLe, bytesLe_refl xs]

theorem bytesLe_antisymm : ∀ a b : Bytes, bytesLe a b = true → bytesLe b a = true → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [bytesLe] at h
  | _ :: _, [], h, _ => by simp [bytesLe] at h
  | x :: xs, y :: ys, h1, h2 => by
    simp only [bytesLe] at h1 h2
    by_cases a1 : x.toNat < y.toNat
    · rw [if_neg (by omega)] at h2
      by_cases e : y = x
      · subst e; omega
      · rw [if_neg e] at h2; cases h2
    · rw [if_neg a1] at h1
      by_cases e : x = y
      · subst e
        rw [if_pos rfl] at h1
        rw [if_neg (by omega), if_pos rfl] at h2
        rw [bytesLe_antisymm xs ys h1 h2]
      · rw [if_neg e] at h1; cases h1

theorem bytesLe_trans : ∀ a b c : Bytes, bytesLe a b = true → bytesLe b c = true → bytesLe a c = true
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [bytesLe] at h
  | _ :: _, _ :: _, [], _, h => by simp [bytesLe] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [bytesLe] at h1 h2 ⊢
    by_cases a1 : x.toNat < y.toNat
    · by_cases a2 : y.toNat < z.toNat
      · rw [if_pos (by omega)]
      · rw [if_neg a2] at h2
        by_cases e2 : y = z
        · subst e2; rw [if_pos a1]
        · rw [if_neg e2] at h2; cases h2
    · rw [if_neg a1] at h1
      by_cases e1 : x = y
      · subst e1
        rw [if_pos rfl] at h1
        by_cases a2 : x.toNat < z.toNat
        · rw [if_pos a2]
        · rw [if_neg a2] at h2 ⊢
          by_cases e2 : x = z
          · subst e2; rw [if_pos rfl] at h2 ⊢; exact bytesLe_trans xs ys zs h1 h2
          · rw [if_neg e2] at h2; cases h2
      · rw [if_neg e1] at h1; cases h1

/-- Sorted (non-strict, every pair) in byte order. -/
def Srt (l : List Bytes) : Prop := l.Pairwise fun a b => bytesLe a b = true

theorem srt_of_sortedAdj : ∀ l : List Bytes, SortedAdj bytesLe l → Srt l
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | x :: y :: t, ⟨hxy, hs⟩ => by
    have ih := srt_of_sortedAdj (y :: t) hs
    refine List.Pairwise.cons ?_ ih
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hxy
    · exact bytesLe_trans _ _ _ hxy (List.rel_of_pairwise_cons ih hz)

theorem srt_isort (l : List Bytes) : Srt (isort bytesLe l) :=
  srt_of_sortedAdj _ (isort_sorted bytesLe bytesLe_total l)

/-- Two sorted rearrangements of each other are equal. -/
theorem srt_perm_eq : ∀ {l m : List Bytes}, l.Perm m → Srt l → Srt m → l = m
  | [], [], _, _, _ => rfl
  | [], _ :: _, hp, _, _ => absurd hp.length_eq (by simp)
  | _ :: _, [], hp, _, _ => absurd hp.length_eq (by simp)
  | a :: l, b :: m, hp, hl, hm => by
    have hab : a = b := by
      have ha : a ∈ b :: m := hp.subset List.mem_cons_self
      have hb : b ∈ a :: l := hp.symm.subset List.mem_cons_self
      rcases List.mem_cons.mp ha with e | ha
      · exact e
      rcases List.mem_cons.mp hb with e | hb
      · exact e.symm
      exact bytesLe_antisymm _ _ (List.rel_of_pairwise_cons hl hb) (List.rel_of_pairwise_cons hm ha)
    subst hab
    rw [srt_perm_eq (hp.cons_inv) hl.of_cons hm.of_cons]

/-! ## One value per hash -/

/-- Unique hashes: no two different values of the list have the same SHA-256. -/
def UH (l : List Bytes) : Prop := ∀ u ∈ l, ∀ v ∈ l, sha256 u = sha256 v → u = v

theorem UH.sub {l m : List Bytes} (h : UH m) (hs : ∀ x ∈ l, x ∈ m) : UH l :=
  fun u hu v hv e => h u (hs u hu) v (hs v hv) e

theorem hGet_UH_mem {l : List Bytes} (hu : UH l) {v : Bytes} (hv : v ∈ l) :
    hGet (mkHStore l) (sha256 v) = some v := by
  rw [hGet_mkHStore]
  cases hf : l.reverse.find? (fun x => sha256 x == sha256 v) with
  | none =>
    rw [List.find?_eq_none] at hf
    have := hf v (List.mem_reverse.mpr hv)
    simp at this
  | some w =>
    have h1 := List.find?_some hf
    have h2 := List.mem_reverse.mp (List.mem_of_find?_eq_some hf)
    simp only [beq_iff_eq] at h1
    rw [hu w h2 v hv h1]

theorem hGet_none_of {l : List Bytes} {h : Bytes} (hn : ∀ v ∈ l, sha256 v ≠ h) :
    hGet (mkHStore l) h = none := by
  rw [hGet_mkHStore, List.find?_eq_none]
  intro v hv e
  simp only [beq_iff_eq] at e
  exact hn v (List.mem_reverse.mp hv) e

/-- A list with one value per hash answers by membership. -/
theorem hGet_UH_congr {l m : List Bytes} (hl : UH l) (hm : UH m) (hlm : ∀ x, x ∈ l ↔ x ∈ m) :
    ∀ h, hGet (mkHStore l) h = hGet (mkHStore m) h := by
  intro h
  by_cases hx : ∃ v ∈ l, sha256 v = h
  · obtain ⟨v, hv, rfl⟩ := hx
    rw [hGet_UH_mem hl hv, hGet_UH_mem hm ((hlm v).mp hv)]
  · have hx' : ∀ v ∈ l, sha256 v ≠ h := fun v hv e => hx ⟨v, hv, e⟩
    rw [hGet_none_of hx', hGet_none_of (fun v hv => hx' v ((hlm v).mpr hv))]

/-! ## `poolOf` -/

theorem mem_poolOf {vals : List Bytes} {x : Bytes} (hx : x ∈ poolOf vals) : x ∈ vals :=
  mem_normValsH hx

theorem poolOf_get {vals : List Bytes} {w : Bytes} (hw : w ∈ poolOf vals) :
    hGet (mkHStore vals) (sha256 w) = some w := by
  unfold poolOf normValsH at hw
  rw [mem_isort] at hw
  have := mem_dedupLastBy id _ w hw
  rw [List.mem_filterMap] at this
  obtain ⟨y, -, hy⟩ := this
  have := (hGet_some hy).1
  rw [this]; exact hy

theorem poolOf_UH (vals : List Bytes) : UH (poolOf vals) := by
  intro u hu v hv e
  have h1 := poolOf_get hu
  have h2 := poolOf_get hv
  rw [e, h2] at h1
  exact (Option.some.inj h1).symm

theorem poolOf_nodup (vals : List Bytes) : (poolOf vals).Nodup := normValsH_nodup _ _

theorem poolOf_srt (vals : List Bytes) : Srt (poolOf vals) := srt_isort _

/-- **The pool answers like the store.** -/
theorem hGet_poolOf (vals : List Bytes) (h : Bytes) :
    hGet (mkHStore (poolOf vals)) h = hGet (mkHStore vals) h := by
  by_cases hx : h ∈ vals.map sha256
  · exact hGet_normValsH vals _ h hx
  · have hn : ∀ v ∈ vals, sha256 v ≠ h := fun v hv e => hx (List.mem_map.mpr ⟨v, hv, e⟩)
    rw [hGet_none_of hn, hGet_none_of (fun v hv => hn v (mem_poolOf hv))]

theorem filterMap_hGet_UH {l : List Bytes} (hu : UH l) :
    ∀ m : List Bytes, (∀ x ∈ m, x ∈ l) → (m.map sha256).filterMap (hGet (mkHStore l)) = m
  | [], _ => rfl
  | x :: xs, hs => by
    simp only [List.map_cons, List.filterMap_cons]
    rw [hGet_UH_mem hu (hs x List.mem_cons_self)]
    simp only
    rw [filterMap_hGet_UH hu xs (fun y hy => hs y (List.mem_cons_of_mem _ hy))]

theorem dedupLastBy_id_nodup : ∀ (l : List Bytes), l.Nodup → dedupLastBy id l = l
  | [], _ => rfl
  | e :: es, hn => by
    rw [List.nodup_cons] at hn
    unfold dedupLastBy
    have : es.any (fun x => id x == id e) = false := by
      rw [List.any_eq_false]
      intro x hx e'
      simp only [id, beq_iff_eq] at e'
      exact hn.1 (e' ▸ hx)
    rw [this]
    simp only [Bool.false_eq_true, ite_false]
    rw [dedupLastBy_id_nodup es hn.2]

/-- `poolOf` of a rearrangement of a sorted pool with one value per hash is that pool. -/
theorem poolOf_perm {l P : List Bytes} (hp : l.Perm P) (hu : UH P) (hn : P.Nodup) (hs : Srt P) :
    poolOf l = P := by
  have hul : UH l := hu.sub (fun x hx => hp.subset hx)
  have hnl : l.Nodup := hp.symm.nodup hn
  unfold poolOf normValsH
  rw [filterMap_hGet_UH hul l (fun x hx => hx), dedupLastBy_id_nodup l hnl]
  exact srt_perm_eq ((isort_perm _ _).trans hp) (srt_isort _) hs

/-! ## Placement -/

theorem layout_perm (R : Bytes) (P : List Bytes) : ((layout R P).1 ++ (layout R P).2).Perm P := by
  unfold layout
  exact List.filter_append_perm _ _

theorem layout_sub1 (R : Bytes) (P : List Bytes) : (layout R P).1.Sublist P := List.filter_sublist
theorem layout_sub2 (R : Bytes) (P : List Bytes) : (layout R P).2.Sublist P := List.filter_sublist

end ReexecV3D3
