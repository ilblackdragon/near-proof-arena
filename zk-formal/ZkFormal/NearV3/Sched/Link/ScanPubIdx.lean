import ZkFormal.NearV3.Sched.Link.ScanPub
import ZkFormal.V2.PubIdx

/-!
# `ScanPub` from the shared public-record interface `PubIdx`

If the public `SPAR` sends are exactly `render`'s `par` records (`PubIdx`, which R1 instantiates
at assembly), then for each instance `τ`, the scan-link hypothesis `ScanPub` holds with `τ`'s
instance record. The other instances' records have a different head, and the codec, shard and
link records have a different tag.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2
open NearSpecV3 NearSpecV3.Scheduler

/-- The default instance record of `render`. -/
def instD : InstPub := ⟨[], ⟨0, 0, 0, 0, 0⟩, #[], [], [], []⟩

/-- The `par` records of one instance. -/
def parBlock (τ : Nat) (P : InstPub) : List (List Nat) :=
  [parCodec τ P] ++ (if P.raw.isEmpty then [] else [parScan τ P]) ++ rawRecs τ P ++
    shardRecs τ P ++ linkRecs τ P

theorem render_par (Ps : List InstPub) (fwd : List (Nat × Nat)) :
    (render Ps fwd).par = (List.range Ps.length).flatMap fun τ => parBlock τ (Ps.getD τ instD) := by
  rfl

/-- Counting over a duplicate-free family of blocks where only block `τ` can contain `M`. -/
theorem count_flatMap_one (enc : Nat → Fp) (g : Nat → List (List Nat)) (M : List Fp) (τ : Nat) :
    ∀ (idx : List Nat), idx.Nodup → τ ∈ idx →
      (∀ τ' ∈ idx, τ' ≠ τ → ∀ r ∈ g τ', r.map enc ≠ M) →
      ((idx.flatMap g).map (·.map enc)).count M = ((g τ).map (·.map enc)).count M
  | [], _, h, _ => by simp at h
  | a :: t, hnd, h, hz => by
    rw [List.nodup_cons] at hnd
    rw [List.flatMap_cons, List.map_append, List.count_append]
    by_cases ha : a = τ
    · subst ha
      have : ((t.flatMap g).map (·.map enc)).count M = 0 := by
        rw [List.count_eq_zero]
        intro hm
        obtain ⟨r, hr, e⟩ := List.mem_map.1 hm
        obtain ⟨τ', hτ', hr'⟩ := List.mem_flatMap.1 hr
        exact hz τ' (List.mem_cons_of_mem _ hτ') (fun e' => hnd.1 (e' ▸ hτ')) r hr' (by simpa using e)
      omega
    · have h0 : ((g a).map (·.map enc)).count M = 0 := by
        rw [List.count_eq_zero]
        intro hm
        obtain ⟨r, hr, e⟩ := List.mem_map.1 hm
        exact hz a List.mem_cons_self ha r hr (by simpa using e)
      rw [h0, count_flatMap_one enc g M τ t hnd.2 (by simpa [ha, Ne.symm ha] using h)
        (fun τ' h' => hz τ' (List.mem_cons_of_mem _ h'))]
      simp

theorem count_zero_of (enc : Nat → Fp) (L : List (List Nat)) (M : List Fp)
    (h : ∀ r ∈ L, r.map enc ≠ M) : (L.map (·.map enc)).count M = 0 := by
  rw [List.count_eq_zero]
  intro hm
  obtain ⟨r, hr, e⟩ := List.mem_map.1 hm
  exact h r hr (by simpa using e)

/-- A record whose head or tag differs from `M`'s is not `M`. -/
theorem ne_of_head {r : List Nat} {M : List Fp} {a b : Nat} (hr : r.head? = some a)
    (hM : M.head? = some (Fp.ofNat b)) (ha : a < 2013265921) (hb : b < 2013265921) (hab : a ≠ b) :
    r.map Fp.ofNat ≠ M := by
  intro e; subst e
  cases r with
  | nil => simp at hr
  | cons x t =>
    simp only [List.head?_cons, Option.some.injEq] at hr; subst hr
    simp only [List.map_cons, List.head?_cons, Option.some.injEq] at hM
    exact hab (ofNat_inj' ha hb hM)

theorem ne_of_tag {r : List Nat} {M : List Fp} {a : Nat} (hr : r[1]? = some a)
    (hM : M[1]? = some (Fp.ofNat 1) ∨ M[1]? = some (Fp.ofNat 2)) (ha : a = 0 ∨ a = 3 ∨ a = 4) :
    r.map Fp.ofNat ≠ M := by
  intro e; subst e
  rw [List.getElem?_map, hr] at hM
  simp only [Option.map_some, Option.some.injEq] at hM
  rcases hM with hM | hM <;> rcases ha with rfl | rfl | rfl <;>
    exact absurd (ofNat_inj' (by decide) (by decide) hM) (by decide)

/-- **`ScanPub` from `PubIdx`.** -/
theorem scanPub_of_idx {AP : AirP} {pub : List Fp} (I : PubIdx AP pub Fp.ofNat)
    (Ps : List InstPub) (fwd : List (Nat × Nat)) (hrec : I.recs B_SPAR true = (render Ps fwd).par)
    (hlen : Ps.length < 2013265921) {τ : Nat} (hτ : τ < Ps.length) :
    ScanPub AP pub τ (Ps.getD τ instD) := by
  refine ⟨fun M hM htag => ?_⟩
  rw [I.count, hrec, render_par]
  rw [count_flatMap_one Fp.ofNat _ M τ _ List.nodup_range (List.mem_range.2 hτ) ?_]
  · unfold scanMsgs scanRecs parBlock
    simp only [List.map_append, List.count_append]
    have h1 : ([parCodec τ (Ps.getD τ instD)].map (·.map Fp.ofNat)).count M = 0 :=
      count_zero_of _ _ _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ne_of_tag (by simp [parCodec]) (by simpa [PT_SCAN, PT_RAW] using htag) (Or.inl rfl))
    have h2 : ((shardRecs τ (Ps.getD τ instD)).map (·.map Fp.ofNat)).count M = 0 :=
      count_zero_of _ _ _ (fun r hr => by
        simp only [shardRecs, List.mem_flatMap, List.mem_map] at hr
        obtain ⟨side, -, x, -, rfl⟩ := hr
        exact ne_of_tag (by simp [PT_SHD]) (by simpa [PT_SCAN, PT_RAW] using htag) (Or.inr (Or.inl rfl)))
    have h3 : ((linkRecs τ (Ps.getD τ instD)).map (·.map Fp.ofNat)).count M = 0 :=
      count_zero_of _ _ _ (fun r hr => by
        simp only [linkRecs, List.mem_map] at hr
        obtain ⟨l, -, rfl⟩ := hr
        exact ne_of_tag (by simp [PT_LINK]) (by simpa [PT_SCAN, PT_RAW] using htag) (Or.inr (Or.inr rfl)))
    rw [h1, h2, h3]
    simp
  · intro τ' hmem hne r hr
    have hτ' : τ' < Ps.length := List.mem_range.1 hmem
    have hhead : r.head? = some τ' := by
      simp only [parBlock, List.mem_append, List.mem_singleton] at hr
      rcases hr with (((rfl | hr) | hr) | hr) | hr
      · simp [parCodec]
      · split at hr
        · simp at hr
        · simp only [List.mem_singleton] at hr; subst hr; simp [parScan]
      · simp only [rawRecs, List.mem_map] at hr
        obtain ⟨⟨q, c⟩, -, rfl⟩ := hr; simp
      · simp only [shardRecs, List.mem_flatMap, List.mem_map] at hr
        obtain ⟨side, -, x, -, rfl⟩ := hr; simp
      · simp only [linkRecs, List.mem_map] at hr
        obtain ⟨l, -, rfl⟩ := hr; simp
    exact ne_of_head hhead hM (by omega) (by omega) hne

end ZkFormal.NearV3.Sched
