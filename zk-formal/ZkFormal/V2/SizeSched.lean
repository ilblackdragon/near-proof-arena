import ZkFormal.Prover.SizeBound

/-!
# ZkFormal.V2.SizeSched — a schedule-exact FRI proof-size bound (V3-D0 P1)

`Prover.SizeBound.sizeMax` charges **every** FRI fold layer a full Merkle path
(the potential `pot κ N 0 (N - logBlowup - finalLog)`).  The deployed schedule
(`Stark.friCommits`) only commits layer 0, roll-in layers, and every
`maxArityLog`-th layer after the previous commitment; one opened commitment of arity
`2^a` at layer `c` costs `nq · (32·2^a + 64·(n0 - c - a))` (`SizeBound.fcost`).
This file bounds the FRI openings by a worst-case dynamic program over the actual
schedule.

## Accounting

Write `B = logBlowup + finalLog`, `M = max maxArityLog 1`, `ℓ = finalLayer`
(`n0 = ℓ + B` when `ℓ > 0`) and measure layers by their **remaining distance**
`d = ℓ - c`.  A commitment from distance `d` with arity log `a` lands at distance
`d - a` and costs at most `stepCost B d a = 32·2^a + 64·(B + d - a)` per query — a
function of `d` and `a` only, not of the header.

*Roll-in caps.*  Table `T` rolls in at layer `j = n0 - lde_T`, i.e. at remaining
distance `lde_T - B = log_T - finalLog ≤ T.maxLog - finalLog`; the table of largest
LDE rolls in at layer `0` (not counted).  Hence for every layer `x < ℓ`, the number
of roll-in layers in `(0, x]` is at most
`capE e = #{T : e ≤ T.maxLog - finalLog} - 1` with `e = ℓ - x` (`roll_count`).

*DP.*  `phi d u` (`u` = roll-ins already passed, `0 ≤ u ≤ R = #tables`) is the
maximum, over the transitions the schedule can take from distance `d`, of
`stepCost + phi (d - a) v`:
* a *regular* step `a = min M d` (no roll-in in the window, or the window reaches
  `ℓ`) to any `v ≥ u` admissible at the landing distance (`v ≤ capE (d - a)`, or
  `d = a`);
* a *roll-in* step `1 ≤ a ≤ M`, `a < d`, to any `v > u` with `v ≤ capE (d - a)`.
`go_sched` shows that the schedule's FRI cost from layer `c` is at most
`phi (ℓ - c) (#roll-ins in (0, c])`, with no side condition on `prm`.  The
header-free bound is `friSchedMax = max_{d ≤ N - B} phi d 0` (`phiMax`), computed by
a memo table (`tab`), so it is kernel-evaluable.

`sizeMaxSched` keeps every other term of `sizeMax` and replaces the FRI potential by
`nq · friSchedMax`; `sizeMaxSched_le` shows it never exceeds `sizeMax A prm κ`
(each DP step is below the potential of the layers it skips).
-/

namespace ZkFormal.V2.SizeSched

open ArenaCore Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Prover ZkFormal.Prover.SizeBound

/-! ## Counting a predicate on a window of layers -/

/-- `cntP p c k = #{j ∈ [c+1, c+k] : p j}`. -/
def cntP (p : Nat → Bool) : Nat → Nat → Nat
  | _, 0 => 0
  | c, k + 1 => (if p (c + 1) then 1 else 0) + cntP p (c + 1) k

theorem cntP_add (p : Nat → Bool) : ∀ a c k, cntP p c (a + k) = cntP p c a + cntP p (c + a) k
  | 0, c, k => by simp [cntP]
  | a + 1, c, k => by
    rw [show a + 1 + k = (a + k) + 1 by omega]
    simp only [cntP]
    rw [cntP_add p a (c + 1) k, show c + 1 + a = c + (a + 1) by omega]
    omega

theorem cntP_mono (p : Nat → Bool) (c a k : Nat) : cntP p c a ≤ cntP p c (a + k) := by
  rw [cntP_add]; omega

theorem cntP_last (p : Nat → Bool) (c k : Nat) (h : p (c + k + 1) = true) :
    cntP p c k + 1 ≤ cntP p c (k + 1) := by
  rw [cntP_add p k c 1]
  simp [cntP, h]

theorem cntP_le_pred {p q : Nat → Bool} (h : ∀ j, p j = true → q j = true) :
    ∀ k c, cntP p c k ≤ cntP q c k
  | 0, c => by simp [cntP]
  | k + 1, c => by
    simp only [cntP]
    have ih := cntP_le_pred h k (c + 1)
    have : (if p (c + 1) = true then 1 else 0) ≤ (if q (c + 1) = true then 1 else 0) := by
      by_cases hp : p (c + 1) = true
      · simp [hp, h _ hp]
      · simp [hp]
    omega

theorem cntP_or (p q : Nat → Bool) :
    ∀ k c, cntP (fun j => p j || q j) c k ≤ cntP p c k + cntP q c k
  | 0, c => by simp [cntP]
  | k + 1, c => by
    simp only [cntP]
    have ih := cntP_or p q k (c + 1)
    rcases Bool.eq_false_or_eq_true (p (c + 1)) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (q (c + 1)) with h2 | h2 <;> simp [h1, h2] <;> omega

theorem cntP_false : ∀ k c, cntP (fun _ => false) c k = 0
  | 0, _ => rfl
  | k + 1, c => by simp [cntP, cntP_false k (c + 1)]

theorem cntP_any {α : Type} (f : Nat → α → Bool) :
    ∀ (ls : List α) (k c : Nat),
      cntP (fun j => ls.any (f j)) c k ≤ (ls.map fun y => cntP (fun j => f j y) c k).sum
  | [], k, c => by simp [cntP_false]
  | y :: ls, k, c => by
    simp only [List.any_cons, List.map_cons, List.sum_cons]
    have h1 := cntP_or (fun j => f j y) (fun j => ls.any (f j)) k c
    have h2 := cntP_any f ls k c
    omega

theorem cntP_single (y n0 : Nat) :
    ∀ k c, cntP (fun j => y + j == n0) c k ≤ if n0 ≤ y + c + k ∧ y + c < n0 then 1 else 0
  | 0, c => by simp [cntP]
  | k + 1, c => by
    simp only [cntP]
    have ih := cntP_single y n0 k (c + 1)
    by_cases h1 : y + (c + 1) = n0
    · have hb : (y + (c + 1) == n0) = true := by simp [h1]
      have hc1 : ¬ (n0 ≤ y + (c + 1) + k ∧ y + (c + 1) < n0) := by omega
      have hc2 : n0 ≤ y + c + (k + 1) ∧ y + c < n0 := by omega
      rw [if_neg hc1] at ih
      rw [if_pos hc2]
      simp only [hb]
      simp
      omega
    · have hb : (y + (c + 1) == n0) = false := by simp [h1]
      simp only [hb]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      refine Nat.le_trans ih ?_
      by_cases hc : n0 ≤ y + (c + 1) + k ∧ y + (c + 1) < n0
      · rw [if_pos hc, if_pos (show n0 ≤ y + c + (k + 1) ∧ y + c < n0 by omega)]
        exact Nat.le_refl _
      · rw [if_neg hc]; exact Nat.zero_le _

/-! ## Generic list lemmas -/

theorem sum_map_lt {α : Type} (f g : α → Nat) :
    ∀ l : List α, (∀ x ∈ l, f x ≤ g x) → (∃ x ∈ l, f x + 1 ≤ g x) →
      (l.map f).sum + 1 ≤ (l.map g).sum
  | [], _, ⟨_, hx, _⟩ => by cases hx
  | a :: l, h, ⟨x, hx, hfx⟩ => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · have := sum_map_le (l := l) (f := f) (g := g) fun y hy => h y (by simp [hy])
      omega
    · have := sum_map_lt f g l (fun y hy => h y (by simp [hy])) ⟨x, hx, hfx⟩
      have := h a (by simp)
      omega

theorem foldr_max_mem : ∀ l : List Nat, l.foldr max 0 = 0 ∨ l.foldr max 0 ∈ l
  | [] => Or.inl rfl
  | a :: l => by
    simp only [List.foldr_cons]
    rcases foldr_max_mem l with h | h
    · right; rw [h, Nat.max_zero]; exact List.mem_cons_self
    · right
      rw [Nat.max_def]
      split
      · exact List.mem_cons_of_mem _ h
      · exact List.mem_cons_self

theorem getD_map_range (f : Nat → Nat) (n u : Nat) :
    ((List.range n).map f).getD u 0 = if u < n then f u else 0 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : u < n <;> simp [h]

/-! ## The worst-case DP over the commit schedule -/

/-- Per-query cost bound of a commitment of arity log `a` from remaining distance `d`. -/
def stepCost (B d a : Nat) : Nat := 32 * 2 ^ a + 64 * (B + d - a)

/-- Entry `u` of row `k` of a table (rows newest first). -/
def phiAt (t : List (List Nat)) (k u : Nat) : Nat := (t.getD k []).getD u 0

/-- The candidate values of `phi d u`, given the rows for distances `d-1, d-2, …`. -/
def cands (M B R : Nat) (cap : Nat → Nat) (d : Nat) (prev : List (List Nat)) (u : Nat) :
    List Nat :=
  ((List.range (R + 1)).map fun v =>
    if u ≤ v ∧ (d - min M d = 0 ∨ v ≤ cap (d - min M d)) then
      stepCost B d (min M d) + phiAt prev (min M d - 1) v else 0) ++
  ((List.range M).flatMap fun x => (List.range (R + 1)).map fun v =>
    if x + 1 < d ∧ u < v ∧ v ≤ cap (d - (x + 1)) then
      stepCost B d (x + 1) + phiAt prev x v else 0)

/-- Push the row for distance `d` onto the rows `t` for distances `d-1, …, 0`. -/
def push (M B R : Nat) (cap : Nat → Nat) (d : Nat) (t : List (List Nat)) : List (List Nat) :=
  ((List.range (R + 1)).map fun u => (cands M B R cap d t u).foldr max 0) :: t

/-- Memo table: rows for distances `d, d-1, …, 0`, each indexed by `u ≤ R`. -/
def tab (M B R : Nat) (cap : Nat → Nat) : Nat → List (List Nat)
  | 0 => [(List.range (R + 1)).map fun _ => 0]
  | d + 1 => push M B R cap (d + 1) (tab M B R cap d)

/-- Worst-case FRI opening cost (per query) from remaining distance `d`, `u` roll-ins passed. -/
def phi (M B R : Nat) (cap : Nat → Nat) (d u : Nat) : Nat := phiAt (tab M B R cap d) 0 u

/-- `max_{d ≤ L} phi d 0`. -/
def phiMax (M B R : Nat) (cap : Nat → Nat) (L : Nat) : Nat :=
  ((tab M B R cap L).map fun r => r.getD 0 0).foldr max 0

section DP
variable (M B R : Nat) (cap : Nat → Nat)

theorem tab_getD (u : Nat) : ∀ d k, k ≤ d → phiAt (tab M B R cap d) k u = phi M B R cap (d - k) u
  | d, 0, _ => rfl
  | d + 1, k + 1, hk => by
    have := tab_getD u d k (by omega)
    rw [show d + 1 - (k + 1) = d - k by omega, ← this]
    simp [phiAt, tab, push]

theorem phi_zero (u : Nat) : phi M B R cap 0 u = 0 := by
  simp only [phi, phiAt, tab, List.getD_cons_zero]
  rw [getD_map_range]; split <;> rfl

theorem phi_succ (d u : Nat) (hu : u ≤ R) :
    phi M B R cap (d + 1) u = (cands M B R cap (d + 1) (tab M B R cap d) u).foldr max 0 := by
  simp only [phi, phiAt, tab, push, List.getD_cons_zero]
  rw [getD_map_range, if_pos (by omega)]

theorem phi_gt (d u : Nat) (hu : R < u) : phi M B R cap d u = 0 := by
  cases d with
  | zero => exact phi_zero M B R cap u
  | succ d =>
    simp only [phi, phiAt, tab, push, List.getD_cons_zero]
    rw [getD_map_range, if_neg (by omega)]

theorem phi_full (hM : 1 ≤ M) (d u v : Nat) (hd : 1 ≤ d) (huv : u ≤ v) (hv : v ≤ R)
    (hc : d - min M d = 0 ∨ v ≤ cap (d - min M d)) :
    stepCost B d (min M d) + phi M B R cap (d - min M d) v ≤ phi M B R cap d u := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [phi_succ M B R cap d u (by omega)]
  apply le_foldr_max
  apply List.mem_append_left
  refine List.mem_map.mpr ⟨v, List.mem_range.mpr (by omega), ?_⟩
  rw [if_pos ⟨huv, hc⟩, tab_getD M B R cap v d _ (by omega)]
  congr 2
  omega

theorem phi_roll (x d u v : Nat) (hx : x < M) (hxd : x + 1 < d) (huv : u < v) (hv : v ≤ R)
    (hc : v ≤ cap (d - (x + 1))) :
    stepCost B d (x + 1) + phi M B R cap (d - (x + 1)) v ≤ phi M B R cap d u := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [phi_succ M B R cap d u (by omega)]
  apply le_foldr_max
  apply List.mem_append_right
  refine List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx, ?_⟩
  refine List.mem_map.mpr ⟨v, List.mem_range.mpr (by omega), ?_⟩
  rw [if_pos ⟨hxd, huv, hc⟩, tab_getD M B R cap v d _ (by omega)]
  congr 2
  omega

theorem phi_le_phiMax (L d : Nat) (hd : d ≤ L) : phi M B R cap d 0 ≤ phiMax M B R cap L := by
  rw [← show L - (L - d) = d by omega, ← tab_getD M B R cap 0 L (L - d) (by omega)]
  unfold phiAt phiMax
  cases hk : (tab M B R cap L)[L - d]? with
  | none =>
    have : (tab M B R cap L).getD (L - d) [] = [] := by
      simp [List.getD_eq_getElem?_getD, hk]
    rw [this]; exact Nat.zero_le _
  | some r =>
    have : (tab M B R cap L).getD (L - d) [] = r := by
      simp [List.getD_eq_getElem?_getD, hk]
    rw [this]
    exact le_foldr_max (List.mem_map.mpr ⟨r, List.mem_of_getElem? hk, rfl⟩)

theorem tab_mem (u : Nat) : ∀ d r, r ∈ tab M B R cap d → ∃ k ≤ d, r.getD u 0 = phi M B R cap k u
  | 0, r, hr => by
    simp only [tab, List.mem_singleton] at hr
    exact ⟨0, Nat.le_refl _, by subst hr; rfl⟩
  | d + 1, r, hr => by
    simp only [tab, push, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨d + 1, Nat.le_refl _, rfl⟩
    · obtain ⟨k, hk, e⟩ := tab_mem u d r hr
      exact ⟨k, by omega, e⟩

/-- Every DP value is below the per-layer potential `pot κ (B+d) 0 d`. -/
theorem phi_le_pot (hM : 1 ≤ M) (κ : Nat) (hκ : ∀ a, 1 ≤ a → a ≤ M → 32 * 2 ^ a ≤ a * κ) :
    ∀ d u, phi M B R cap d u ≤ pot κ (B + d) 0 d := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro u
  cases d with
  | zero => rw [phi_zero]; exact Nat.zero_le _
  | succ d =>
    by_cases hu : R < u
    · rw [phi_gt M B R cap _ u hu]; exact Nat.zero_le _
    rw [phi_succ M B R cap d u (by omega)]
    -- one step of arity `a` followed by a DP value at distance `d+1-a`
    have step : ∀ a k v, 1 ≤ a → a ≤ M → a ≤ d + 1 → k = a - 1 →
        stepCost B (d + 1) a + phiAt (tab M B R cap d) k v ≤ pot κ (B + (d + 1)) 0 (d + 1) := by
      intro a k v ha1 haM had hk
      subst hk
      rw [tab_getD M B R cap v d _ (by omega), show d - (a - 1) = d + 1 - a by omega]
      have h1 := ih (d + 1 - a) (by omega) v
      have hsplit := pot_add κ (B + (d + 1)) a 0 (d + 1 - a)
      rw [show a + (d + 1 - a) = d + 1 by omega, Nat.zero_add] at hsplit
      have hshift := pot_shift κ (B + (d + 1 - a)) a 0 (d + 1 - a)
      rw [show B + (d + 1 - a) + a = B + (d + 1) by omega, Nat.zero_add] at hshift
      have hge := pot_ge κ (B + (d + 1)) (a - 1) 0
      rw [show a - 1 + 1 = a by omega, Nat.zero_add] at hge
      have hk := hκ a ha1 haM
      rw [Nat.mul_comm a κ] at hk
      unfold stepCost
      generalize 2 ^ a = e at *
      generalize κ * a = t at *
      omega
    apply foldr_max_le (Nat.zero_le _)
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
      split
      · exact step _ _ v (by omega) (Nat.min_le_left _ _) (Nat.min_le_right _ _) rfl
      · exact Nat.zero_le _
    · obtain ⟨x, hx, hy⟩ := List.mem_flatMap.mp hy
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
      have hx := List.mem_range.mp hx
      split
      · exact step (x + 1) x v (by omega) (by omega) (by omega) (by omega)
      · exact Nat.zero_le _
where
  pot_shift (κ n s : Nat) : ∀ c k, pot κ (n + s) (c + s) k = pot κ n c k
    | _, 0 => rfl
    | c, k + 1 => by
      simp only [pot]
      rw [show c + s + 1 = (c + 1) + s by omega, pot_shift κ n s (c + 1) k]
      congr 2
      omega

theorem phiMax_le_pot (hM : 1 ≤ M) (κ N L : Nat) (hκ : ∀ a, 1 ≤ a → a ≤ M → 32 * 2 ^ a ≤ a * κ)
    (hL : B + L ≤ N ∨ L = 0) : phiMax M B R cap L ≤ pot κ N 0 L := by
  unfold phiMax
  apply foldr_max_le (Nat.zero_le _)
  intro y hy
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
  obtain ⟨k, hk, e⟩ := tab_mem M B R cap 0 L r hr
  rw [e]
  cases k with
  | zero => rw [phi_zero]; exact Nat.zero_le _
  | succ k =>
    refine Nat.le_trans (phi_le_pot M B R cap hM κ hκ _ 0) ?_
    exact Nat.le_trans (pot_mono_n0 κ (by omega) _ 0) (pot_mono_k κ N 0 hk)

end DP

/-! ## The schedule's cost is below the DP -/

section
variable (A : Air) (prm : Params) (hdr : List Nat)

theorem go_nil (ℓ c fuel : Nat) (h : ℓ ≤ c) : friCommits.go A prm hdr ℓ c fuel = [] := by
  cases fuel <;> simp [friCommits.go, h]

theorem fcost_le_step (n0 B ℓ c a : Nat) (hn0 : n0 ≤ ℓ + B) (hca : c + a ≤ ℓ) :
    fcost n0 (c, a) ≤ stepCost B (ℓ - c) a := by
  unfold fcost stepCost
  simp only
  generalize 2 ^ a = e
  omega

/-- **The schedule against the DP**: from committed layer `c`, the remaining FRI
opening cost is at most `phi (ℓ - c) (#roll-ins in (0, c])`. -/
theorem go_sched (R : Nat) (cap : Nat → Nat) (n0 ℓ : Nat)
    (hn0 : n0 ≤ ℓ + (prm.logBlowup + prm.finalLog)) (hcap : ∀ e, cap e ≤ R)
    (hfact : ∀ x, x < ℓ → cntP (rollInAt A prm hdr) 0 x ≤ cap (ℓ - x)) :
    ∀ fuel c, ((friCommits.go A prm hdr ℓ c fuel).map (fcost n0)).sum ≤
      phi (max prm.maxArityLog 1) (prm.logBlowup + prm.finalLog) R cap (ℓ - c)
        (cntP (rollInAt A prm hdr) 0 c)
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
      -- the final step to `ℓ` (arity `ℓ - c ≤ M`)
      have hend : ∀ nxt, nxt = ℓ → ℓ - c ≤ max prm.maxArityLog 1 →
          fcost n0 (c, nxt - c) + ((friCommits.go A prm hdr ℓ nxt fuel).map (fcost n0)).sum ≤
            phi (max prm.maxArityLog 1) (prm.logBlowup + prm.finalLog) R cap (ℓ - c)
              (cntP (rollInAt A prm hdr) 0 c) := by
        intro nxt hn hle
        rw [hn, go_nil A prm hdr ℓ ℓ fuel (Nat.le_refl _)]
        have hmin : min (max prm.maxArityLog 1) (ℓ - c) = ℓ - c := Nat.min_eq_right hle
        have := phi_full (max prm.maxArityLog 1) (prm.logBlowup + prm.finalLog) R cap hM
          (ℓ - c) (cntP (rollInAt A prm hdr) 0 c) (cntP (rollInAt A prm hdr) 0 c) (by omega)
          (Nat.le_refl _) hu (Or.inl (by omega))
        rw [hmin] at this
        have h2 := fcost_le_step n0 (prm.logBlowup + prm.finalLog) ℓ c (ℓ - c) hn0 (by omega)
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
          have ih := go_sched R cap n0 ℓ hn0 hcap hfact fuel i
          -- roll-in step of arity `i - c = x + 1`
          have hv1 : cntP (rollInAt A prm hdr) 0 c + 1 ≤ cntP (rollInAt A prm hdr) 0 i := by
            have e1 := cntP_add (rollInAt A prm hdr) c 0 (x + 1)
            rw [Nat.zero_add, show c + (x + 1) = i by omega] at e1
            have e2 := cntP_last (rollInAt A prm hdr) c x (by rw [show c + x + 1 = i by omega]; exact hp)
            have e3 := cntP_mono (rollInAt A prm hdr) c 0 x
            simp only [cntP, Nat.zero_add] at e3
            omega
          have hv2 := hfact i hiℓ
          have hroll := phi_roll (max prm.maxArityLog 1) (prm.logBlowup + prm.finalLog) R cap x
            (ℓ - c) (cntP (rollInAt A prm hdr) 0 c) (cntP (rollInAt A prm hdr) 0 i)
            (by omega) (by omega) (by omega) (Nat.le_trans hv2 (hcap _))
            (by rw [show ℓ - c - (x + 1) = ℓ - i by omega]; exact hv2)
          rw [show ℓ - c - (x + 1) = ℓ - i by omega] at hroll
          have h2 := fcost_le_step n0 (prm.logBlowup + prm.finalLog) ℓ c (i - c) hn0 (by omega)
          rw [show i - c = x + 1 by omega] at h2 ⊢
          omega
        · rw [Nat.min_eq_right (by omega)]
          exact hend ℓ rfl (by omega)
      · by_cases hlt : c + max prm.maxArityLog 1 < ℓ
        · rw [Nat.min_eq_left (by omega)]
          have ih := go_sched R cap n0 ℓ hn0 hcap hfact fuel (c + max prm.maxArityLog 1)
          have hmin : min (max prm.maxArityLog 1) (ℓ - c) = max prm.maxArityLog 1 :=
            Nat.min_eq_left (by omega)
          have hv := hfact _ hlt
          have hmono := cntP_mono (rollInAt A prm hdr) 0 c (max prm.maxArityLog 1)
          have hfull := phi_full (max prm.maxArityLog 1) (prm.logBlowup + prm.finalLog) R cap hM
            (ℓ - c) (cntP (rollInAt A prm hdr) 0 c)
            (cntP (rollInAt A prm hdr) 0 (c + max prm.maxArityLog 1)) (by omega) hmono
            (Nat.le_trans hv (hcap _))
            (Or.inr (by rw [hmin, show ℓ - c - max prm.maxArityLog 1 =
              ℓ - (c + max prm.maxArityLog 1) by omega]; exact hv))
          rw [hmin, show ℓ - c - max prm.maxArityLog 1 = ℓ - (c + max prm.maxArityLog 1) by omega]
            at hfull
          have h2 := fcost_le_step n0 (prm.logBlowup + prm.finalLog) ℓ c
            (max prm.maxArityLog 1) hn0 (by omega)
          rw [show c + max prm.maxArityLog 1 - c = max prm.maxArityLog 1 by omega]
          omega
        · rw [Nat.min_eq_right (by omega)]
          exact hend ℓ rfl (by omega)

/-! ## Counting roll-in layers -/

/-- Header-free cap on the roll-in layers at remaining distance `≥ e`. -/
def capE (A : Air) (prm : Params) (e : Nat) : Nat :=
  (A.tables.map fun T => if e ≤ T.maxLog - prm.finalLog then 1 else 0).sum - 1

theorem capE_le (e : Nat) : capE A prm e ≤ A.tables.length := by
  have := sum_map_const_le (fun T : Air.Table => if e ≤ T.maxLog - prm.finalLog then 1 else 0) 1
    A.tables (fun T _ => by split <;> omega)
  unfold capE
  omega

theorem maxLog_of_headerOk (h : headerOk A prm hdr = true) :
    ∀ p ∈ A.tables.zip hdr, p.2 ≤ p.1.maxLog := by
  intro p hp
  simp only [headerOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, hall⟩, _⟩, _⟩ := h
  obtain ⟨T, l⟩ := p
  exact (hall (T, l) hp).1.1.2

/-- **Roll-in count**: for `x < ℓ`, at most `capE (ℓ - x)` layers in `(0, x]` roll in. -/
theorem roll_count (h : headerOk A prm hdr = true) :
    ∀ x, x < finalLayer A prm hdr →
      cntP (rollInAt A prm hdr) 0 x ≤ capE A prm (finalLayer A prm hdr - x) := by
  intro x hx
  have hℓ : finalLayer A prm hdr = queryLog A prm hdr - prm.logBlowup - prm.finalLog := rfl
  generalize hn0 : queryLog A prm hdr = n0 at hℓ
  -- step 1: drop `0 < j`
  have s1 := cntP_le_pred (p := rollInAt A prm hdr)
    (q := fun j => (layout A prm hdr).any fun L => L.lde + j == n0)
    (by intro j hj; unfold rollInAt at hj; rw [hn0] at hj
        simp only [Bool.and_eq_true] at hj; exact hj.2) x 0
  -- step 2: split over tables
  have s2 := cntP_any (fun j (L : TLayout) => L.lde + j == n0) (layout A prm hdr) x 0
  -- step 3: one layer per table, none for the largest
  have s3 := sum_map_le (l := layout A prm hdr)
    (f := fun L => cntP (fun j => L.lde + j == n0) 0 x)
    (g := fun L => if n0 ≤ L.lde + x ∧ L.lde < n0 then 1 else 0)
    (fun L _ => by have := cntP_single L.lde n0 x 0; simpa using this)
  -- step 4: the largest LDE is attained
  have hne : ∃ L ∈ layout A prm hdr, L.lde = n0 := by
    rcases foldr_max_mem ((layout A prm hdr).map (·.lde)) with h0 | h0
    · exfalso
      have : queryLog A prm hdr = 0 := h0
      omega
    · have : queryLog A prm hdr ∈ (layout A prm hdr).map (·.lde) := h0
      rw [hn0] at this
      obtain ⟨L, hL, e⟩ := List.mem_map.mp this
      exact ⟨L, hL, e⟩
  have s4 := sum_map_lt (fun L : TLayout => if n0 ≤ L.lde + x ∧ L.lde < n0 then 1 else 0)
    (fun L => if n0 ≤ L.lde + x then 1 else 0) (layout A prm hdr)
    (fun L _ => by split <;> split <;> omega)
    (by obtain ⟨L, hL, e⟩ := hne
        exact ⟨L, hL, by rw [if_neg (by omega), if_pos (by omega)]; exact Nat.le_refl _⟩)
  -- step 5: tables' maximal heights
  have s5 : ((layout A prm hdr).map fun L => if n0 ≤ L.lde + x then 1 else 0).sum ≤
      (A.tables.map fun T =>
        if finalLayer A prm hdr - x ≤ T.maxLog - prm.finalLog then 1 else 0).sum := by
    rw [layout_eq, List.map_map]
    refine Nat.le_trans (sum_map_le (l := A.tables.zip hdr) (f := _) (g := fun p : Air.Table × Nat =>
      if finalLayer A prm hdr - x ≤ p.1.maxLog - prm.finalLog then 1 else 0) ?_) ?_
    · intro p hp
      have := maxLog_of_headerOk A prm hdr h p hp
      show (if n0 ≤ p.2 + prm.logBlowup + x then 1 else 0) ≤ _
      by_cases h1 : n0 ≤ p.snd + prm.logBlowup + x
      · rw [if_pos h1, if_pos (by omega)]; exact Nat.le_refl _
      · rw [if_neg h1]; exact Nat.zero_le _
    · exact sum_zip_fst_le (fun T : Air.Table =>
        if finalLayer A prm hdr - x ≤ T.maxLog - prm.finalLog then 1 else 0) A.tables hdr
  unfold capE
  omega

/-! ## FRI openings -/

/-- Header-free worst-case FRI opening cost per query position. -/
def friSchedMax (A : Air) (prm : Params) : Nat :=
  phiMax (max prm.maxArityLog 1) (prm.logBlowup + prm.finalLog) A.tables.length (capE A prm)
    (prm.maxLogLde - prm.logBlowup - prm.finalLog)

theorem friCommits_sched (h : headerOk A prm hdr = true) :
    ((friCommits A prm hdr).map (fcost (queryLog A prm hdr))).sum ≤ friSchedMax A prm := by
  have hq := queryLog_le A prm hdr h
  have hgo := go_sched A prm hdr A.tables.length (capE A prm) (queryLog A prm hdr)
    (finalLayer A prm hdr) (by unfold finalLayer; omega) (capE_le A prm)
    (roll_count A prm hdr h) (finalLayer A prm hdr) 0
  simp only [Nat.sub_zero, cntP] at hgo
  refine Nat.le_trans hgo (phi_le_phiMax _ _ _ _ _ _ ?_)
  unfold finalLayer; omega

theorem fri_open_le_sched (nq : Nat) (h : headerOk A prm hdr = true) :
    ((schedOracles (friSchedule A prm hdr)).map (openSize nq)).sum ≤ nq * friSchedMax A prm := by
  rw [schedOracles_fri, sum_map_flatMap]
  simp only [openSize_friOracleAt]
  have h1 := sum_lkSum_le (fun i a => nq * fcost (queryLog A prm hdr) (i, a))
    (List.range (finalLayer A prm hdr)) List.nodup_range (friCommits A prm hdr)
  have h2 := sum_map_mul nq (fcost (queryLog A prm hdr)) (friCommits A prm hdr)
  have h3 := Nat.mul_le_mul_left nq (friCommits_sched A prm hdr h)
  refine Nat.le_trans h1 ?_
  rw [h2]; exact h3

end

/-! ## The bound -/

/-- **Header-free, schedule-exact proof-size bound**: `sizeMax` with the FRI potential
replaced by the worst-case cost of the deployed commit schedule. -/
def sizeMaxSched (A : Air) (prm : Params) : Nat :=
  let nq := prm.numChunks * prm.posPerChunk
  let N := prm.maxLogLde
  prefixMax A prm +
    nq * (4 * (A.tables.map fun T => T.width).sum + 64 * N) +
    nq * (4 * (A.tables.map fun T => 8 * T.auxCount prm.auxGroup).sum + 64 * N) +
    nq * (4 * (A.tables.map fun T => 8 * T.quotCount prm.auxGroup).sum + 64 * N) +
    nq * friSchedMax A prm

/-- **Generic schedule-exact size bound**: on every admissible header,
`sizeBound ≤ sizeMaxSched` (no side condition on the parameters). -/
theorem sizeBound_le_sched {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]
    [DecidableEq K] (A : Air) (prm : Params) (hdr : List Nat) (h : headerOk A prm hdr = true) :
    sizeBound (Iop.verifier F K A prm) hdr ≤ sizeMaxSched A prm := by
  show prefixSize (schedule A prm hdr) +
    ((schedOracles (schedule A prm hdr)).map (openSize (prm.numChunks * prm.posPerChunk))).sum ≤ _
  rw [schedOracles_schedule]
  simp only [List.cons_append, List.nil_append, List.map_cons, List.sum_cons]
  have hp := prefix_le A prm hdr h
  have h1 := open_layout_le A prm hdr (prm.numChunks * prm.posPerChunk) h
    (fun T => T.width) (fun L => L.width) (fun _ _ => rfl)
  have h2 := open_layout_le A prm hdr (prm.numChunks * prm.posPerChunk) h
    (fun T => 8 * T.auxCount prm.auxGroup) (fun L => 8 * L.aux) (fun _ _ => rfl)
  have h3 := open_layout_le A prm hdr (prm.numChunks * prm.posPerChunk) h
    (fun T => 8 * T.quotCount prm.auxGroup) (fun L => 8 * L.quot) (fun _ _ => rfl)
  have h4 := fri_open_le_sched A prm hdr (prm.numChunks * prm.posPerChunk) h
  unfold sizeMaxSched
  dsimp only at h1 h2 h3 ⊢
  omega

/-- `friSchedMax` never exceeds the per-layer potential of `sizeMax`. -/
theorem friSchedMax_le (A : Air) (prm : Params) (κ : Nat)
    (hκ : ∀ a, 1 ≤ a → a ≤ max prm.maxArityLog 1 → 32 * 2 ^ a ≤ a * κ) :
    friSchedMax A prm ≤
      pot κ prm.maxLogLde 0 (prm.maxLogLde - prm.logBlowup - prm.finalLog) :=
  phiMax_le_pot _ _ _ _ (Nat.le_max_right _ _) κ _ _ hκ (by omega)

/-- **`sizeMaxSched` refines `sizeMax`** for every admissible per-layer arity cost `κ`
(in particular `κ = 86` at the deployed `maxArityLog = 3`). -/
theorem sizeMaxSched_le (A : Air) (prm : Params) (κ : Nat)
    (hκ : ∀ a, 1 ≤ a → a ≤ max prm.maxArityLog 1 → 32 * 2 ^ a ≤ a * κ) :
    sizeMaxSched A prm ≤ sizeMax A prm κ := by
  have := Nat.mul_le_mul_left (prm.numChunks * prm.posPerChunk) (friSchedMax_le A prm κ hκ)
  unfold sizeMaxSched sizeMax
  dsimp only
  omega

end ZkFormal.V2.SizeSched
