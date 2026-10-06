import ZkFormal.Size.Dedup
import ZkFormal.V2.SizeSched

/-!
# ZkFormal.Size.Sched — the header-free deduplicated proof-size bound `sizeMaxDedup`

`V2.SizeSched.sizeMaxSched` bounds `sizeBound` (one full Merkle path per query position and
oracle).  This file bounds the deduplicated `Size.sizeBoundD` (the honest proof's length,
`Size.size32D`) by a closed, kernel-evaluable formula `sizeMaxDedup A prm` in the AIR's
static column counts:

* main / aux / quotient oracles (depth `≤ N = maxLogLde`):
  `4·Σ_T min nq 2^(maxLog_T + logBlowup) · cols_T + 64·dsum nq N` each
  (`dsum nq N = Σ_{j<N} min nq 2^j`: the top `⌈log₂ nq⌉` levels are charged once);
* FRI: the worst case over the **deployed commit schedule including roll-in forced commits**
  (the DP of `V2.SizeSched`, generalised to any per-commit cost, `phiG`), with the
  deduplicated cost of one commit of arity `2^a` from remaining distance `d`:
  `costD nq B d a = 4·min nq 2^(B+d-a)·8·2^a + 64·dsum nq (B+d-a)`.

Main results:
* `sizeBoundD_le_dedup`: `sizeBoundD (Iop.verifier F K A prm) hdr ≤ sizeMaxDedup A prm` on
  every admissible header (no side condition on `prm`);
* `sizeMaxDedup_le_sched`: `sizeMaxDedup A prm ≤ sizeMaxSched A prm` (never worse).
-/

namespace ZkFormal.Size

open ArenaCore Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Prover ZkFormal.Prover.SizeBound
  ZkFormal.V2.SizeSched

/-! ## The commit-schedule DP for an arbitrary per-commit cost -/

/-- Candidates of `phiG d u` (`cost d a`: one commitment of arity log `a` from distance `d`). -/
def candsG (M R : Nat) (cap : Nat → Nat) (cost : Nat → Nat → Nat) (d : Nat)
    (prev : List (List Nat)) (u : Nat) : List Nat :=
  ((List.range (R + 1)).map fun v =>
    if u ≤ v ∧ (d - min M d = 0 ∨ v ≤ cap (d - min M d)) then
      cost d (min M d) + phiAt prev (min M d - 1) v else 0) ++
  ((List.range M).flatMap fun x => (List.range (R + 1)).map fun v =>
    if x + 1 < d ∧ u < v ∧ v ≤ cap (d - (x + 1)) then
      cost d (x + 1) + phiAt prev x v else 0)

def pushG (M R : Nat) (cap : Nat → Nat) (cost : Nat → Nat → Nat) (d : Nat)
    (t : List (List Nat)) : List (List Nat) :=
  ((List.range (R + 1)).map fun u => (candsG M R cap cost d t u).foldr max 0) :: t

def tabG (M R : Nat) (cap : Nat → Nat) (cost : Nat → Nat → Nat) : Nat → List (List Nat)
  | 0 => [(List.range (R + 1)).map fun _ => 0]
  | d + 1 => pushG M R cap cost (d + 1) (tabG M R cap cost d)

def phiG (M R : Nat) (cap : Nat → Nat) (cost : Nat → Nat → Nat) (d u : Nat) : Nat :=
  phiAt (tabG M R cap cost d) 0 u

def phiMaxG (M R : Nat) (cap : Nat → Nat) (cost : Nat → Nat → Nat) (L : Nat) : Nat :=
  ((tabG M R cap cost L).map fun r => r.getD 0 0).foldr max 0

section DP
variable (M R : Nat) (cap : Nat → Nat) (cost : Nat → Nat → Nat)

/-- The P1 DP is the instance `cost = stepCost B`. -/
theorem tab_eq_tabG (B : Nat) : ∀ d, tab M B R cap d = tabG M R cap (stepCost B) d
  | 0 => rfl
  | d + 1 => by
    rw [tab, tabG, tab_eq_tabG B d]
    rfl

theorem phiMax_eq (B L : Nat) : phiMax M B R cap L = phiMaxG M R cap (stepCost B) L := by
  unfold phiMax phiMaxG; rw [tab_eq_tabG]

theorem tabG_getD (u : Nat) : ∀ d k, k ≤ d →
    phiAt (tabG M R cap cost d) k u = phiG M R cap cost (d - k) u
  | d, 0, _ => rfl
  | d + 1, k + 1, hk => by
    have := tabG_getD u d k (by omega)
    rw [show d + 1 - (k + 1) = d - k by omega, ← this]
    simp [phiAt, tabG, pushG]

theorem phiG_zero (u : Nat) : phiG M R cap cost 0 u = 0 := by
  simp only [phiG, phiAt, tabG, List.getD_cons_zero]
  rw [getD_map_range]; split <;> rfl

theorem phiG_succ (d u : Nat) (hu : u ≤ R) :
    phiG M R cap cost (d + 1) u = (candsG M R cap cost (d + 1) (tabG M R cap cost d) u).foldr max 0 := by
  simp only [phiG, phiAt, tabG, pushG, List.getD_cons_zero]
  rw [getD_map_range, if_pos (by omega)]

theorem phiG_gt (d u : Nat) (hu : R < u) : phiG M R cap cost d u = 0 := by
  cases d with
  | zero => exact phiG_zero M R cap cost u
  | succ d =>
    simp only [phiG, phiAt, tabG, pushG, List.getD_cons_zero]
    rw [getD_map_range, if_neg (by omega)]

theorem phiG_full (hM : 1 ≤ M) (d u v : Nat) (hd : 1 ≤ d) (huv : u ≤ v) (hv : v ≤ R)
    (hc : d - min M d = 0 ∨ v ≤ cap (d - min M d)) :
    cost d (min M d) + phiG M R cap cost (d - min M d) v ≤ phiG M R cap cost d u := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [phiG_succ M R cap cost d u (by omega)]
  apply le_foldr_max
  apply List.mem_append_left
  refine List.mem_map.mpr ⟨v, List.mem_range.mpr (by omega), ?_⟩
  rw [if_pos ⟨huv, hc⟩, tabG_getD M R cap cost v d _ (by omega)]
  congr 2
  omega

theorem phiG_roll (x d u v : Nat) (hx : x < M) (hxd : x + 1 < d) (huv : u < v) (hv : v ≤ R)
    (hc : v ≤ cap (d - (x + 1))) :
    cost d (x + 1) + phiG M R cap cost (d - (x + 1)) v ≤ phiG M R cap cost d u := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [phiG_succ M R cap cost d u (by omega)]
  apply le_foldr_max
  apply List.mem_append_right
  refine List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx, ?_⟩
  refine List.mem_map.mpr ⟨v, List.mem_range.mpr (by omega), ?_⟩
  rw [if_pos ⟨hxd, huv, hc⟩, tabG_getD M R cap cost v d _ (by omega)]
  congr 2
  omega

theorem phiG_le_phiMaxG (L d : Nat) (hd : d ≤ L) :
    phiG M R cap cost d 0 ≤ phiMaxG M R cap cost L := by
  rw [← show L - (L - d) = d by omega, ← tabG_getD M R cap cost 0 L (L - d) (by omega)]
  unfold phiAt phiMaxG
  cases hk : (tabG M R cap cost L)[L - d]? with
  | none =>
    have : (tabG M R cap cost L).getD (L - d) [] = [] := by
      simp [List.getD_eq_getElem?_getD, hk]
    rw [this]; exact Nat.zero_le _
  | some r =>
    have : (tabG M R cap cost L).getD (L - d) [] = r := by
      simp [List.getD_eq_getElem?_getD, hk]
    rw [this]
    exact le_foldr_max (List.mem_map.mpr ⟨r, List.mem_of_getElem? hk, rfl⟩)

theorem tabG_mem (u : Nat) : ∀ d r, r ∈ tabG M R cap cost d →
    ∃ k ≤ d, r.getD u 0 = phiG M R cap cost k u
  | 0, r, hr => by
    simp only [tabG, List.mem_singleton] at hr
    exact ⟨0, Nat.le_refl _, by subst hr; rfl⟩
  | d + 1, r, hr => by
    simp only [tabG, pushG, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨d + 1, Nat.le_refl _, rfl⟩
    · obtain ⟨k, hk, e⟩ := tabG_mem u d r hr
      exact ⟨k, by omega, e⟩

/-- **DP comparison**: a pointwise cost bound `c₁ ≤ k·c₂` lifts to the DP values. -/
theorem phiG_le_mul (hM : 1 ≤ M) (c1 c2 : Nat → Nat → Nat) (k : Nat)
    (hc : ∀ d a, 1 ≤ a → a ≤ M → a ≤ d → c1 d a ≤ k * c2 d a) :
    ∀ d u, phiG M R cap c1 d u ≤ k * phiG M R cap c2 d u := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro u
  cases d with
  | zero => rw [phiG_zero]; exact Nat.zero_le _
  | succ d =>
    by_cases hu : R < u
    · rw [phiG_gt M R cap c1 _ u hu]; exact Nat.zero_le _
    rw [phiG_succ M R cap c1 d u (by omega)]
    apply foldr_max_le (Nat.zero_le _)
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
      have hv := List.mem_range.mp hv
      split
      · rename_i hcd
        rw [tabG_getD M R cap c1 v d _ (by omega),
          show d - (min M (d + 1) - 1) = d + 1 - min M (d + 1) by omega]
        have h1 := ih (d + 1 - min M (d + 1)) (by omega) v
        have h2 := hc (d + 1) (min M (d + 1)) (by omega) (Nat.min_le_left _ _)
          (Nat.min_le_right _ _)
        have h3 := phiG_full M R cap c2 hM (d + 1) u v (by omega) hcd.1 (by omega) hcd.2
        have h4 := Nat.mul_le_mul_left k h3
        rw [Nat.mul_add] at h4
        omega
      · exact Nat.zero_le _
    · obtain ⟨x, hx, hy⟩ := List.mem_flatMap.mp hy
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
      have hx := List.mem_range.mp hx
      have hv := List.mem_range.mp hv
      split
      · rename_i hcd
        rw [tabG_getD M R cap c1 v d _ (by omega), show d - x = d + 1 - (x + 1) by omega]
        have h1 := ih (d + 1 - (x + 1)) (by omega) v
        have h2 := hc (d + 1) (x + 1) (by omega) (by omega) (by omega)
        have h3 := phiG_roll M R cap c2 x (d + 1) u v hx hcd.1 hcd.2.1 (by omega) hcd.2.2
        have h4 := Nat.mul_le_mul_left k h3
        rw [Nat.mul_add] at h4
        omega
      · exact Nat.zero_le _

theorem phiMaxG_le_mul (hM : 1 ≤ M) (c1 c2 : Nat → Nat → Nat) (k L : Nat)
    (hc : ∀ d a, 1 ≤ a → a ≤ M → a ≤ d → c1 d a ≤ k * c2 d a) :
    phiMaxG M R cap c1 L ≤ k * phiMaxG M R cap c2 L := by
  unfold phiMaxG
  apply foldr_max_le (Nat.zero_le _)
  intro y hy
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
  obtain ⟨j, hj, e⟩ := tabG_mem M R cap c1 0 L r hr
  rw [e]
  exact Nat.le_trans (phiG_le_mul M R cap hM c1 c2 k hc j 0)
    (Nat.mul_le_mul_left k (phiG_le_phiMaxG M R cap c2 L j hj))

end DP

/-! ## The schedule's cost is below the DP, for any per-commit cost -/

section
variable (A : Air) (prm : Params) (hdr : List Nat)

/-- `V2.SizeSched.go_sched` for an arbitrary per-commit cost `fc` dominated by `cost`. -/
theorem go_schedG (R : Nat) (cap : Nat → Nat) (cost : Nat → Nat → Nat)
    (fc : Nat × Nat → Nat) (ℓ : Nat)
    (hfc : ∀ c a, c + a ≤ ℓ → fc (c, a) ≤ cost (ℓ - c) a) (hcap : ∀ e, cap e ≤ R)
    (hfact : ∀ x, x < ℓ → cntP (rollInAt A prm hdr) 0 x ≤ cap (ℓ - x)) :
    ∀ fuel c, ((friCommits.go A prm hdr ℓ c fuel).map fc).sum ≤
      phiG (max prm.maxArityLog 1) R cap cost (ℓ - c) (cntP (rollInAt A prm hdr) 0 c)
  | 0, c => by simp [friCommits.go]
  | fuel + 1, c => by
    have hM : 1 ≤ max prm.maxArityLog 1 := Nat.le_max_right _ _
    rw [friCommits.go]
    dsimp only
    split
    · simp
    · rename_i hcl
      have hu : cntP (rollInAt A prm hdr) 0 c ≤ R := Nat.le_trans (hfact c (by omega)) (hcap _)
      simp only [List.map_cons, List.sum_cons]
      have hend : ∀ nxt, nxt = ℓ → ℓ - c ≤ max prm.maxArityLog 1 →
          fc (c, nxt - c) + ((friCommits.go A prm hdr ℓ nxt fuel).map fc).sum ≤
            phiG (max prm.maxArityLog 1) R cap cost (ℓ - c) (cntP (rollInAt A prm hdr) 0 c) := by
        intro nxt hn hle
        rw [hn, go_nil A prm hdr ℓ ℓ fuel (Nat.le_refl _)]
        have hmin : min (max prm.maxArityLog 1) (ℓ - c) = ℓ - c := Nat.min_eq_right hle
        have := phiG_full (max prm.maxArityLog 1) R cap cost hM
          (ℓ - c) (cntP (rollInAt A prm hdr) 0 c) (cntP (rollInAt A prm hdr) 0 c) (by omega)
          (Nat.le_refl _) hu (Or.inl (by omega))
        rw [hmin] at this
        have h2 := hfc c (ℓ - c) (by omega)
        simp only [List.map_nil, List.sum_nil]
        omega
      split
      · rename_i i hi
        have hp : rollInAt A prm hdr i = true := List.find?_some hi
        have hmem := List.mem_of_find?_eq_some hi
        simp only [List.mem_map, List.mem_range] at hmem
        obtain ⟨x, hx, hxi⟩ := hmem
        by_cases hiℓ : i < ℓ
        · rw [Nat.min_eq_left (by omega)]
          have ih := go_schedG R cap cost fc ℓ hfc hcap hfact fuel i
          have hv1 : cntP (rollInAt A prm hdr) 0 c + 1 ≤ cntP (rollInAt A prm hdr) 0 i := by
            have e1 := cntP_add (rollInAt A prm hdr) c 0 (x + 1)
            rw [Nat.zero_add, show c + (x + 1) = i by omega] at e1
            have e2 := cntP_last (rollInAt A prm hdr) c x (by rw [show c + x + 1 = i by omega]; exact hp)
            have e3 := cntP_mono (rollInAt A prm hdr) c 0 x
            simp only [cntP, Nat.zero_add] at e3
            omega
          have hv2 := hfact i hiℓ
          have hroll := phiG_roll (max prm.maxArityLog 1) R cap cost x
            (ℓ - c) (cntP (rollInAt A prm hdr) 0 c) (cntP (rollInAt A prm hdr) 0 i)
            (by omega) (by omega) (by omega) (Nat.le_trans hv2 (hcap _))
            (by rw [show ℓ - c - (x + 1) = ℓ - i by omega]; exact hv2)
          rw [show ℓ - c - (x + 1) = ℓ - i by omega] at hroll
          have h2 := hfc c (i - c) (by omega)
          rw [show i - c = x + 1 by omega] at h2 ⊢
          omega
        · rw [Nat.min_eq_right (by omega)]
          exact hend ℓ rfl (by omega)
      · by_cases hlt : c + max prm.maxArityLog 1 < ℓ
        · rw [Nat.min_eq_left (by omega)]
          have ih := go_schedG R cap cost fc ℓ hfc hcap hfact fuel (c + max prm.maxArityLog 1)
          have hmin : min (max prm.maxArityLog 1) (ℓ - c) = max prm.maxArityLog 1 :=
            Nat.min_eq_left (by omega)
          have hv := hfact _ hlt
          have hmono := cntP_mono (rollInAt A prm hdr) 0 c (max prm.maxArityLog 1)
          have hfull := phiG_full (max prm.maxArityLog 1) R cap cost hM
            (ℓ - c) (cntP (rollInAt A prm hdr) 0 c)
            (cntP (rollInAt A prm hdr) 0 (c + max prm.maxArityLog 1)) (by omega) hmono
            (Nat.le_trans hv (hcap _))
            (Or.inr (by rw [hmin, show ℓ - c - max prm.maxArityLog 1 =
              ℓ - (c + max prm.maxArityLog 1) by omega]; exact hv))
          rw [hmin, show ℓ - c - max prm.maxArityLog 1 = ℓ - (c + max prm.maxArityLog 1) by omega]
            at hfull
          have h2 := hfc c (max prm.maxArityLog 1) (by omega)
          rw [show c + max prm.maxArityLog 1 - c = max prm.maxArityLog 1 by omega]
          omega
        · rw [Nat.min_eq_right (by omega)]
          exact hend ℓ rfl (by omega)

/-! ## Deduplicated FRI openings -/

/-- Deduplicated bytes of the FRI oracle committed at layer `p.1` with arity log `p.2`
(query domain `2^n0`): `openSizeD nq [(n0 - p.1 - p.2, 8·2^p.2)]`. -/
def fcostD (nq n0 : Nat) (p : Nat × Nat) : Nat :=
  4 * (min nq (2 ^ (n0 - p.1 - p.2)) * (8 * 2 ^ p.2)) + 64 * dsum nq (n0 - p.1 - p.2)

/-- Header-free deduplicated cost of one commitment of arity log `a` from remaining
distance `d` (`B = logBlowup + finalLog`). -/
def costD (nq B d a : Nat) : Nat :=
  4 * (min nq (2 ^ (B + d - a)) * (8 * 2 ^ a)) + 64 * dsum nq (B + d - a)

theorem fcostD_le (nq n0 B ℓ c a : Nat) (hn0 : n0 ≤ ℓ + B) (hca : c + a ≤ ℓ) :
    fcostD nq n0 (c, a) ≤ costD nq B (ℓ - c) a := by
  unfold fcostD costD
  simp only
  have hle : n0 - c - a ≤ B + (ℓ - c) - a := by omega
  have h1 := min_pow_mono nq hle
  have h2 := dsum_mono nq hle
  have h3 := Nat.mul_le_mul_right (8 * 2 ^ a) h1
  omega

theorem costD_le (nq B d a : Nat) : costD nq B d a ≤ nq * stepCost B d a := by
  unfold costD stepCost
  have h1 : min nq (2 ^ (B + d - a)) * (8 * 2 ^ a) ≤ nq * (8 * 2 ^ a) :=
    Nat.mul_le_mul_right _ (Nat.min_le_left _ _)
  have h2 := dsum_le_mul nq (B + d - a)
  rw [Nat.mul_add, Nat.mul_left_comm nq 64]
  have h3 : 4 * (nq * (8 * 2 ^ a)) = nq * (32 * 2 ^ a) := by
    rw [Nat.mul_left_comm, ← Nat.mul_assoc 4 8]
  have := Nat.mul_le_mul_left 4 h1
  have := Nat.mul_le_mul_left 64 h2
  omega

theorem openSizeD_friOracleAt (nq i : Nat) :
    ((friOracleAt A prm hdr i).map (openSizeD nq)).sum =
      lkSum (fun i a => fcostD nq (queryLog A prm hdr) (i, a)) (friCommits A prm hdr) i := by
  unfold friOracleAt lkSum
  cases (friCommits A prm hdr).lookup i with
  | none => rfl
  | some a => simp [openSizeD, treeLog, fcostD]

/-- Header-free worst-case deduplicated FRI opening bytes (all `nq` positions). -/
def friDedupMax (A : Air) (prm : Params) : Nat :=
  phiMaxG (max prm.maxArityLog 1) A.tables.length (capE A prm)
    (costD (prm.numChunks * prm.posPerChunk) (prm.logBlowup + prm.finalLog))
    (prm.maxLogLde - prm.logBlowup - prm.finalLog)

theorem friCommits_dedup (nq : Nat) (h : headerOk A prm hdr = true) :
    ((friCommits A prm hdr).map (fcostD nq (queryLog A prm hdr))).sum ≤
      phiMaxG (max prm.maxArityLog 1) A.tables.length (capE A prm)
        (costD nq (prm.logBlowup + prm.finalLog)) (prm.maxLogLde - prm.logBlowup - prm.finalLog) := by
  have hq := queryLog_le A prm hdr h
  have hgo := go_schedG A prm hdr A.tables.length (capE A prm)
    (costD nq (prm.logBlowup + prm.finalLog)) (fcostD nq (queryLog A prm hdr))
    (finalLayer A prm hdr)
    (fun c a hca => fcostD_le nq _ _ _ c a (by unfold finalLayer; omega) hca)
    (capE_le A prm) (roll_count A prm hdr h) (finalLayer A prm hdr) 0
  simp only [Nat.sub_zero, cntP] at hgo
  refine Nat.le_trans hgo (phiG_le_phiMaxG _ _ _ _ _ _ ?_)
  unfold finalLayer; omega

theorem fri_open_le_dedup (nq : Nat) (h : headerOk A prm hdr = true) :
    ((schedOracles (friSchedule A prm hdr)).map (openSizeD nq)).sum ≤
      phiMaxG (max prm.maxArityLog 1) A.tables.length (capE A prm)
        (costD nq (prm.logBlowup + prm.finalLog)) (prm.maxLogLde - prm.logBlowup - prm.finalLog) := by
  rw [schedOracles_fri, sum_map_flatMap]
  simp only [openSizeD_friOracleAt]
  have h1 := sum_lkSum_le (fun i a => fcostD nq (queryLog A prm hdr) (i, a))
    (List.range (finalLayer A prm hdr)) List.nodup_range (friCommits A prm hdr)
  exact Nat.le_trans h1 (friCommits_dedup A prm hdr nq h)

/-! ## Main / aux / quotient openings -/

/-- Rows of a trace-side oracle: `min nq 2^(maxLog_T + logBlowup)` positions per table. -/
def rowsMax (A : Air) (prm : Params) (nq : Nat) (G : Air.Table → Nat) : Nat :=
  (A.tables.map fun T => min nq (2 ^ (T.maxLog + prm.logBlowup)) * G T).sum

theorem open_layout_leD (nq : Nat) (h : headerOk A prm hdr = true)
    (G : Air.Table → Nat) (f : TLayout → Nat)
    (hfg : ∀ (T : Air.Table) (l : Nat), f (mkL prm T l) = G T) :
    openSizeD nq ((layout A prm hdr).map fun L => (L.lde, f L))
      ≤ 4 * rowsMax A prm nq G + 64 * dsum nq prm.maxLogLde := by
  unfold openSizeD rowsMax
  rw [List.map_map]
  have h1 : ((layout A prm hdr).map ((fun m => min nq (2 ^ m.1) * m.2) ∘ fun L => (L.lde, f L))).sum
      ≤ (A.tables.map fun T => min nq (2 ^ (T.maxLog + prm.logBlowup)) * G T).sum := by
    rw [layout_eq, List.map_map]
    refine Nat.le_trans (SizeBound.sum_map_le (l := A.tables.zip hdr)
      (g := fun p : Air.Table × Nat => min nq (2 ^ (p.1.maxLog + prm.logBlowup)) * G p.1) ?_) ?_
    · intro p hp
      have := maxLog_of_headerOk A prm hdr h p hp
      show min nq (2 ^ (p.2 + prm.logBlowup)) * f (mkL prm p.1 p.2) ≤ _
      rw [hfg]
      exact Nat.mul_le_mul_right _ (min_pow_mono nq (by omega))
    · exact sum_zip_fst_le (fun T : Air.Table => min nq (2 ^ (T.maxLog + prm.logBlowup)) * G T)
        A.tables hdr
  have h2 : treeLog ((layout A prm hdr).map fun L => (L.lde, f L)) ≤ prm.maxLogLde := by
    apply treeLog_le_of
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨L, hL, rfl⟩ := hp
    exact lde_le_of_headerOk A prm hdr h L hL
  have h3 := dsum_mono nq h2
  omega

end

/-! ## The bound -/

/-- **Header-free deduplicated proof-size bound.** -/
def sizeMaxDedup (A : Air) (prm : Params) : Nat :=
  let nq := prm.numChunks * prm.posPerChunk
  let N := prm.maxLogLde
  prefixMax A prm +
    (4 * rowsMax A prm nq (fun T => T.width) + 64 * dsum nq N) +
    (4 * rowsMax A prm nq (fun T => 8 * T.auxCount prm.auxGroup) + 64 * dsum nq N) +
    (4 * rowsMax A prm nq (fun T => 8 * T.quotCount prm.auxGroup) + 64 * dsum nq N) +
    friDedupMax A prm

/-- **Generic deduplicated size bound**: on every admissible header,
`sizeBoundD ≤ sizeMaxDedup` (no side condition on the parameters). -/
theorem sizeBoundD_le_dedup {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]
    [DecidableEq K] (A : Air) (prm : Params) (hdr : List Nat) (h : headerOk A prm hdr = true) :
    sizeBoundD (Iop.verifier F K A prm) hdr ≤ sizeMaxDedup A prm := by
  show prefixSize (schedule A prm hdr) +
    ((schedOracles (schedule A prm hdr)).map (openSizeD (prm.numChunks * prm.posPerChunk))).sum ≤ _
  rw [schedOracles_schedule]
  simp only [List.cons_append, List.nil_append, List.map_cons, List.sum_cons]
  have hp := prefix_le A prm hdr h
  have h1 := open_layout_leD A prm hdr (prm.numChunks * prm.posPerChunk) h
    (fun T => T.width) (fun L => L.width) (fun _ _ => rfl)
  have h2 := open_layout_leD A prm hdr (prm.numChunks * prm.posPerChunk) h
    (fun T => 8 * T.auxCount prm.auxGroup) (fun L => 8 * L.aux) (fun _ _ => rfl)
  have h3 := open_layout_leD A prm hdr (prm.numChunks * prm.posPerChunk) h
    (fun T => 8 * T.quotCount prm.auxGroup) (fun L => 8 * L.quot) (fun _ _ => rfl)
  have h4 := fri_open_le_dedup A prm hdr (prm.numChunks * prm.posPerChunk) h
  unfold sizeMaxDedup friDedupMax
  dsimp only at h1 h2 h3 ⊢
  omega

theorem rowsMax_le (A : Air) (prm : Params) (nq : Nat) (G : Air.Table → Nat) :
    rowsMax A prm nq G ≤ nq * (A.tables.map G).sum := by
  unfold rowsMax
  rw [← SizeBound.sum_map_mul]
  exact SizeBound.sum_map_le fun T _ => Nat.mul_le_mul_right _ (Nat.min_le_left _ _)

/-- `friDedupMax` never exceeds the P1 bound `nq · friSchedMax`. -/
theorem friDedupMax_le (A : Air) (prm : Params) :
    friDedupMax A prm ≤ prm.numChunks * prm.posPerChunk * friSchedMax A prm := by
  unfold friDedupMax friSchedMax
  rw [phiMax_eq]
  exact phiMaxG_le_mul _ _ _ (Nat.le_max_right _ _) _ _ _ _
    fun d a _ _ _ => costD_le _ _ d a

/-- **`sizeMaxDedup` refines `sizeMaxSched`** (P1): the deduplicated bound is never worse. -/
theorem sizeMaxDedup_le_sched (A : Air) (prm : Params) :
    sizeMaxDedup A prm ≤ sizeMaxSched A prm := by
  have hf := friDedupMax_le A prm
  have r1 := rowsMax_le A prm (prm.numChunks * prm.posPerChunk) (fun T => T.width)
  have r2 := rowsMax_le A prm (prm.numChunks * prm.posPerChunk) (fun T => 8 * T.auxCount prm.auxGroup)
  have r3 := rowsMax_le A prm (prm.numChunks * prm.posPerChunk) (fun T => 8 * T.quotCount prm.auxGroup)
  have hd := dsum_le_mul (prm.numChunks * prm.posPerChunk) prm.maxLogLde
  unfold sizeMaxDedup sizeMaxSched
  dsimp only
  generalize prm.numChunks * prm.posPerChunk = nq at *
  rw [Nat.mul_add nq, Nat.mul_add nq, Nat.mul_add nq, Nat.mul_left_comm nq 4, Nat.mul_left_comm nq 4,
    Nat.mul_left_comm nq 4, Nat.mul_left_comm nq 64]
  have := Nat.mul_le_mul_left 4 r1
  have := Nat.mul_le_mul_left 4 r2
  have := Nat.mul_le_mul_left 4 r3
  have := Nat.mul_le_mul_left 64 hd
  omega

end ZkFormal.Size
