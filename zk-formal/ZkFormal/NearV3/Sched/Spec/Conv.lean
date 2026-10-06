import ZkFormal.NearV3.Sched.Model

/-!
# ZkFormal.NearV3.Sched.Spec.Conv — request conversion = raw requests + `incsOf`

Lane `v3-sched`. For the PV 86 parameters:

* `requestValues_strict` — the 40 request values are strictly increasing and above `base`;
* `increases_eq_incsFrom` — `increases` (the spec's skip-if-not-above-running-total walk) is
  the list of differences of the values over the set bits (`incsOf`): no set bit is skipped;
* `convertRequests_eq_convRaw` — `convertRequests` = `convRaw` of the raw requests with
  resolved shard indices (`rawOf`);
* `incsOf_length_le`, `incsOf_pos` — at most 40 increases, each positive.
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler NearSpec

/-! ## PV 86 parameters -/

theorem pv86_calc {n : Nat} {p : Params} (hp : Params.calculate Config.pv86 n = some p) :
    p = ⟨Nat.min (305696 / Nat.max 1 (n - 1)) 100000, 4500000, 4194304, 4194304, 4500000⟩ := by
  simp only [Params.calculate, Config.pv86] at hp
  simp at hp
  exact hp.symm

theorem pv86_base_le {n : Nat} {p : Params} (hp : Params.calculate Config.pv86 n = some p) :
    p.base ≤ 100000 ∧ p.maxSingleGrant = 4194304 := by
  rw [pv86_calc hp]
  exact ⟨Nat.min_le_right _ _, rfl⟩

/-! ## The request values -/

theorem requestValues_length (p : Params) : (requestValues p).length = 40 := by
  simp [requestValues]

theorem requestValues_get (p : Params) {i : Nat} (hi : i < 40) :
    (requestValues p)[i]! = p.base + (p.maxSingleGrant - p.base) * (i + 1) / 40 := by
  have h : i < (requestValues p).length := by rw [requestValues_length]; exact hi
  rw [getElem!_pos (requestValues p) i h]
  simp [requestValues]

theorem requestValues_strict {n : Nat} {p : Params} (_hn : 1 ≤ n)
    (hp : Params.calculate Config.pv86 n = some p) :
    (requestValues p).length = 40 ∧
    (∀ i, i < 39 → (requestValues p)[i]! < (requestValues p)[i + 1]!) ∧
    p.base < (requestValues p)[0]! := by
  obtain ⟨hb, hg⟩ := pv86_base_le hp
  refine ⟨requestValues_length p, fun i hi => ?_, ?_⟩
  · rw [requestValues_get p (by omega), requestValues_get p (by omega), hg]
    have hd : 40 ≤ 4194304 - p.base := by omega
    have he : (4194304 - p.base) * (i + 1 + 1) = (4194304 - p.base) * (i + 1) + (4194304 - p.base) :=
      Nat.mul_succ _ _
    rw [he]
    omega
  · rw [requestValues_get p (by omega), hg]
    omega

/-- Pairwise strictness from adjacent strictness. -/
theorem strict_of_adj (vals : List Nat)
    (hadj : ∀ i, i + 1 < vals.length → vals[i]! < vals[i + 1]!) :
    ∀ a c, a < c → c < vals.length → vals[a]! < vals[c]! := by
  intro a c hac hc
  induction c with
  | zero => omega
  | succ c ih =>
    have h1 := hadj c hc
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hac) with h | h
    · exact Nat.lt_trans (ih h (by omega)) h1
    · subst h; exact h1

/-! ## `increases` = `incsFrom` over the set bits -/

theorem increases_eq_incsFrom_gen (vals : List Nat) (bm : List UInt8)
    (hmono : ∀ a c, a < c → c < vals.length → vals[a]! < vals[c]!) :
    ∀ k i cur, i + k = vals.length → (∀ c, i ≤ c → c < vals.length → cur < vals[c]!) →
      increases vals bm i (vals.drop i) cur
        = incsFrom vals cur ((List.range' i k).filter (getBit bm))
  | 0, i, cur, hk, _ => by
    have : vals.drop i = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]; simp [increases, incsFrom]
  | k + 1, i, cur, hk, hcur => by
    have hi : i < vals.length := by omega
    rw [List.drop_eq_getElem_cons hi, List.range'_succ]
    have hvi : vals[i]! = vals[i] := getElem!_pos vals i hi
    have hgd : vals.getD i 0 = vals[i] := by simp [List.getD_eq_getElem?_getD, hi]
    have hc := hcur i (Nat.le_refl _) hi
    rw [hvi] at hc
    simp only [increases, List.filter_cons]
    by_cases hb : getBit bm i = true
    · simp only [hb, hc, and_self, ↓reduceIte, incsFrom, hgd]
      congr 1
      apply increases_eq_incsFrom_gen vals bm hmono k (i + 1) vals[i] (by omega)
      intro c hc1 hc2
      have := hmono i c (by omega) hc2
      rwa [hvi] at this
    · simp only [hb, false_and, ↓reduceIte, Bool.false_eq_true]
      exact increases_eq_incsFrom_gen vals bm hmono k (i + 1) cur (by omega)
        (fun c hc1 hc2 => hcur c (by omega) hc2)

theorem increases_eq_incsFrom {n : Nat} {p : Params} (hn : 1 ≤ n)
    (hp : Params.calculate Config.pv86 n = some p) (bm : List UInt8) :
    increases (requestValues p) bm 0 (requestValues p) p.base = incsOf p bm := by
  obtain ⟨hlen, hadj, h0⟩ := requestValues_strict hn hp
  have hmono := strict_of_adj (requestValues p) (fun i hi => hadj i (by omega))
  have h := increases_eq_incsFrom_gen (requestValues p) bm hmono 40 0 p.base (by omega)
    (fun c _ hc => by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; exact h0
      · exact Nat.lt_trans h0 (hmono 0 c h hc))
  simpa [incsOf, setBits, List.range_eq_range'] using h

/-! ## Length and positivity of the increases -/

theorem incsFrom_length (vals : List Nat) :
    ∀ (prev : Nat) (cs : List Nat), (incsFrom vals prev cs).length = cs.length
  | _, [] => rfl
  | prev, c :: cs => by simp [incsFrom, incsFrom_length vals _ cs]

theorem incsOf_length_le (p : Params) (bm : List UInt8) : (incsOf p bm).length ≤ 40 := by
  simp only [incsOf, incsFrom_length, setBits]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem increases_pos (vals : List Nat) (bm : List UInt8) :
    ∀ (vs : List Nat) (i cur : Nat), ∀ x ∈ increases vals bm i vs cur, 0 < x
  | [], _, _, x, hx => by simp [increases] at hx
  | v :: vs, i, cur, x, hx => by
    simp only [increases] at hx
    split at hx
    · rename_i h
      rcases List.mem_cons.mp hx with hx | hx
      · subst hx; omega
      · exact increases_pos vals bm vs _ _ x hx
    · exact increases_pos vals bm vs _ _ x hx

theorem incsOf_pos {n : Nat} {p : Params} (hn : 1 ≤ n)
    (hp : Params.calculate Config.pv86 n = some p) (bm : List UInt8) :
    ∀ x ∈ incsOf p bm, 0 < x := by
  rw [← increases_eq_incsFrom hn hp bm]
  exact increases_pos _ _ _ _ _

/-! ## `convertRequests` = `convRaw ∘ rawOf` -/

/-- Raw requests with resolved shard indices, in the spec's order (unknown shards dropped). -/
def rawOf (ids : List Nat) (rs : List (Nat × List BandwidthRequest)) : List RawReq :=
  rs.flatMap fun (sender, brs) => brs.filterMap fun br =>
    match indexOf ids sender, indexOf ids br.toShard with
    | some s, some r => some ⟨s, r, br.bitmap⟩
    | _, _ => none

theorem convertRequests_eq_convRaw {ids : List Nat} {p : Params} (hn : 1 ≤ ids.length)
    (hp : Params.calculate Config.pv86 ids.length = some p)
    (requests : List (Nat × List BandwidthRequest)) :
    convertRequests p ids requests = convRaw p ids.length (rawOf ids (toBTreeMap requests)) := by
  simp only [convertRequests, convRaw, rawOf, List.filterMap_flatMap, List.filterMap_filterMap]
  congr 1
  funext x
  obtain ⟨sender, brs⟩ := x
  simp only
  congr 1
  funext br
  simp only [convertRequest, increases_eq_incsFrom hn hp]
  cases indexOf ids sender <;> cases indexOf ids br.toShard <;> simp only [Option.bind] <;>
    cases incsOf p br.bitmap <;> rfl

end ZkFormal.NearV3.Sched
