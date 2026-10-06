import ZkFormal.NearV3.Sched.Model
import ZkFormal.NearV3.Sched.Spec.DistDefs

/-!
# ZkFormal.NearV3.Sched.Spec.LinkPass — `increase_allowances` + `grant_base_bandwidth` in closed form

Lane `v3-sched`. The spec runs `tryGrant base` on every link (sender-major) starting from
budgets `MSB` and allowances `min(min(a0 + fair, u64::MAX), MA)`. For PV 86 (`pv86_facts`):
`n·base ≤ MSB − MSG + 100000 ≤ MSB`, so every budget check on an allowed link passes (a sender
or receiver is granted at most `n` times), and `grantMore` never saturates. Hence the fold equals
the closed form `linkPass` (`linkPass_eq`).

Proof: the state after `i` full sender rows and `j` links of row `i` is `lpSt i j` (budgets
`MSB − base·count`, allowances/grants updated on the allowed links `< i·n + j`); one step
`lpSt i j → lpSt i (j+1)` (`lp_step`), row boundary `lpSt i n = lpSt (i+1) 0` (`lp_row`).
The core argument (`linkPass_eq_gen`) only uses `n·base ≤ MSB` and `MA ≤ u64::MAX`.
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler NearSpec

/-! ## PV 86 parameters -/

theorem lp_calc {n : Nat} {p : Params} (hp : Params.calculate Config.pv86 n = some p) :
    p = ⟨Nat.min (305696 / Nat.max 1 (n - 1)) 100000, 4500000, 4194304, 4194304, 4500000⟩ := by
  simp only [Params.calculate, Config.pv86] at hp
  simp at hp
  exact hp.symm

theorem pv86_facts {n : Nat} {p : Params} (hn : 1 ≤ n)
    (hp : Params.calculate Config.pv86 n = some p) :
    p.maxShardBandwidth = 4500000 ∧ p.maxSingleGrant = 4194304 ∧ p.maxAllowance = 4500000 ∧
    p.base = min (305696 / max 1 (n - 1)) 100000 ∧
    n * p.base ≤ 4500000 - 4194304 + 100000 ∧
    p.base ≤ p.maxShardBandwidth / n := by
  have h := lp_calc hp
  subst h
  have hbase : Nat.min (305696 / Nat.max 1 (n - 1)) 100000 = min (305696 / max 1 (n - 1)) 100000 :=
    rfl
  have hnb : n * Nat.min (305696 / Nat.max 1 (n - 1)) 100000 ≤ 405696 := by
    rw [hbase]
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have : n = 1 := by omega
      subst this; decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hm : max 1 (m + 1 - 1) = m := by simp; omega
      rw [hm, Nat.succ_mul]
      have h1 : m * min (305696 / m) 100000 ≤ m * (305696 / m) :=
        Nat.mul_le_mul_left m (Nat.min_le_left _ _)
      have h2 : m * (305696 / m) ≤ 305696 := Nat.mul_div_le 305696 m
      have h3 : min (305696 / m) 100000 ≤ 100000 := Nat.min_le_right _ _
      omega
  refine ⟨rfl, rfl, rfl, hbase, hnb, ?_⟩
  show Nat.min (305696 / Nat.max 1 (n - 1)) 100000 ≤ 4500000 / n
  rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
  omega

/-! ## Array helpers -/

theorem lp_ofFn_get! {α : Type} [Inhabited α] {m : Nat} (f : Fin m → α) {k : Nat} (hk : k < m) :
    (Array.ofFn f)[k]! = f ⟨k, hk⟩ := by
  rw [getElem!_pos (Array.ofFn f) k (by simpa using hk)]
  simp

theorem lp_set_ofFn {α : Type} {m : Nat} (f : Fin m → α) (k : Nat) (v : α) :
    (Array.ofFn f).set! k v = Array.ofFn fun x => if x.1 = k then v else f x := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds (by simpa using h1)]
    simp only [Array.getElem_ofFn]
    by_cases h : k = i
    · subst h; simp
    · simp [h, Ne.symm h]

/-! ## The intermediate states -/

section
variable (n : Nat) (p : Params) (allowed : Array Bool) (a0 : Array Nat) (rng : Rng)

/-- Allowed links among the first `j` of sender row `s`. -/
def lpRow (s j : Nat) : Nat := ((List.range j).filter fun r => allowed[s * n + r]!).length

/-- Allowed links into receiver `r` among the first `i` sender rows. -/
def lpCol (r i : Nat) : Nat := ((List.range i).filter fun s => allowed[s * n + r]!).length

/-- Base grants of sender `s` after `i` rows and `j` links of row `i`. -/
def lpCS (i j s : Nat) : Nat :=
  if s < i then lpRow n allowed s n else if s = i then lpRow n allowed s j else 0

/-- Base grants of receiver `r` after `i` rows and `j` links of row `i`. -/
def lpCR (i j r : Nat) : Nat :=
  lpCol n allowed r i + if r < j ∧ allowed[i * n + r]! = true then 1 else 0

/-- Allowance after `increase_allowances`. -/
def lpA1 (l : Nat) : Nat := Nat.min (a0[l]! + p.maxShardBandwidth / n) p.maxAllowance

/-- Is link `l` already granted at position `k` of the pass? -/
def lpDone (k l : Nat) : Prop := l < k ∧ allowed[l]! = true

instance (k l : Nat) : Decidable (lpDone allowed k l) := by unfold lpDone; infer_instance

/-- The state after `i` rows and `j` links of row `i`. -/
def lpSt (i j : Nat) : St where
  senderBudget := Array.ofFn (n := n) fun s => p.maxShardBandwidth - p.base * lpCS n allowed i j s
  receiverBudget := Array.ofFn (n := n) fun r => p.maxShardBandwidth - p.base * lpCR n allowed i j r
  allowance := Array.ofFn (n := n * n) fun l =>
    if lpDone allowed (i * n + j) l then lpA1 n p a0 l - p.base else lpA1 n p a0 l
  granted := Array.ofFn (n := n * n) fun l => if lpDone allowed (i * n + j) l then p.base else 0
  rng := rng

end

theorem lpRow_succ (n : Nat) (allowed : Array Bool) (s j : Nat) :
    lpRow n allowed s (j + 1) = lpRow n allowed s j + if allowed[s * n + j]! = true then 1 else 0 := by
  simp only [lpRow, List.range_succ, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]
  split <;> simp_all

theorem lpCol_succ (n : Nat) (allowed : Array Bool) (r i : Nat) :
    lpCol n allowed r (i + 1) = lpCol n allowed r i + if allowed[i * n + r]! = true then 1 else 0 := by
  simp only [lpCol, List.range_succ, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]
  split <;> simp_all

theorem lpRow_le (n : Nat) (allowed : Array Bool) (s j : Nat) : lpRow n allowed s j ≤ j := by
  simp only [lpRow]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem lpCol_le (n : Nat) (allowed : Array Bool) (r i : Nat) : lpCol n allowed r i ≤ i := by
  simp only [lpCol]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-! ## One step and one row -/

theorem lp_divmod {n i j : Nat} (hj : j < n) : (i * n + j) / n = i ∧ (i * n + j) % n = j := by
  have hn : 0 < n := by omega
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hj]; rfl
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

/-- A not-allowed link changes nothing. -/
theorem lp_step_skip (n : Nat) (p : Params) (allowed : Array Bool) (a0 : Array Nat) (rng : Rng)
    {i j : Nat} (ha : allowed[i * n + j]! = false) :
    lpSt n p allowed a0 rng i (j + 1) = lpSt n p allowed a0 rng i j := by
  have hcs : lpCS n allowed i (j + 1) = lpCS n allowed i j := by
    funext s
    simp only [lpCS]
    split
    · rfl
    · split
      · rename_i h; subst h; rw [lpRow_succ, ha]; simp
      · rfl
  have hcr : lpCR n allowed i (j + 1) = lpCR n allowed i j := by
    funext r
    simp only [lpCR]
    by_cases hr : r = j
    · subst hr; simp [ha]
    · have : (r < j + 1) ↔ (r < j) := by omega
      simp only [this]
  have hd : ∀ l, lpDone allowed (i * n + (j + 1)) l ↔ lpDone allowed (i * n + j) l := by
    intro l
    simp only [lpDone]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rcases Nat.lt_or_ge l (i * n + j) with h | h
      · exact h
      · have : l = i * n + j := by omega
        subst this; rw [ha] at h2; exact absurd h2 (by decide)
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  simp only [lpSt, hcs, hcr, hd]

/-- An allowed link is granted `base`. -/
theorem lp_step_grant (n : Nat) (p : Params) (allowed : Array Bool) (a0 : Array Nat) (rng : Rng)
    (hb : n * p.base ≤ p.maxShardBandwidth) (hbu : p.base ≤ u64Max)
    {i j : Nat} (hi : i < n) (hj : j < n) (ha : allowed[i * n + j]! = true) :
    (tryGrant n allowed (lpSt n p allowed a0 rng i j) (i * n + j) p.base).2
      = lpSt n p allowed a0 rng i (j + 1) := by
  obtain ⟨hdiv, hmod⟩ := lp_divmod (i := i) hj
  have hl : i * n + j < n * n := by
    have := Nat.mul_le_mul_right n (show i + 1 ≤ n by omega)
    rw [Nat.succ_mul] at this; omega
  -- budgets before the step
  have hsb : (lpSt n p allowed a0 rng i j).senderBudget[i]!
      = p.maxShardBandwidth - p.base * lpRow n allowed i j := by
    simp [lpSt, lp_ofFn_get! _ hi, lpCS]
  have hrb : (lpSt n p allowed a0 rng i j).receiverBudget[j]!
      = p.maxShardBandwidth - p.base * lpCol n allowed j i := by
    simp [lpSt, lp_ofFn_get! _ hj, lpCR]
  have hal : (lpSt n p allowed a0 rng i j).allowance[i * n + j]! = lpA1 n p a0 (i * n + j) := by
    simp [lpSt, lp_ofFn_get! _ hl, lpDone]
  have hrow : p.base * (lpRow n allowed i j + 1) ≤ p.maxShardBandwidth := by
    have := Nat.mul_le_mul_left p.base (show lpRow n allowed i j + 1 ≤ n by
      have := lpRow_le n allowed i j; omega)
    rw [Nat.mul_comm p.base n] at this; omega
  have hcol : p.base * (lpCol n allowed j i + 1) ≤ p.maxShardBandwidth := by
    have := Nat.mul_le_mul_left p.base (show lpCol n allowed j i + 1 ≤ n by
      have := lpCol_le n allowed j i; omega)
    rw [Nat.mul_comm p.base n] at this; omega
  rw [Nat.mul_succ] at hrow hcol
  have hns : ¬ (p.maxShardBandwidth - p.base * lpRow n allowed i j < p.base ∨
      p.maxShardBandwidth - p.base * lpCol n allowed j i < p.base) := by omega
  simp only [tryGrant, ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hdiv, hmod, hsb, hrb,
    hal, hns, grantMore]
  -- the granted entry before the step is 0
  have hg0 : (Array.ofFn (n := n * n) fun l =>
      if lpDone allowed (i * n + j) l then p.base else 0)[i * n + j]! = 0 := by
    simp [lp_ofFn_get! _ hl, lpDone]
  simp only [lpSt, hg0, Nat.zero_add, hbu, ↓reduceIte, lp_set_ofFn, St.mk.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · congr 1; funext s
    simp only [lpCS]
    by_cases hs : s.1 = i
    · simp only [hs, ↓reduceIte, Nat.lt_irrefl, lpRow_succ, ha, Nat.mul_succ]; omega
    · simp [hs]
  · congr 1; funext r
    simp only [lpCR]
    by_cases hr : r.1 = j
    · simp only [hr, ↓reduceIte, Nat.lt_succ_self, ha, and_self, Nat.mul_succ]
      omega
    · have : (r.1 < j + 1) ↔ (r.1 < j) := by omega
      simp [hr, this]
  · congr 1; funext l
    by_cases hx : l.1 = i * n + j
    · simp [hx, lpDone, ha]
    · have : lpDone allowed (i * n + (j + 1)) l ↔ lpDone allowed (i * n + j) l := by
        simp only [lpDone]
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
      simp [hx, this]
  · congr 1; funext l
    by_cases hx : l.1 = i * n + j
    · simp [hx, lpDone, ha]
    · have : lpDone allowed (i * n + (j + 1)) l ↔ lpDone allowed (i * n + j) l := by
        simp only [lpDone]
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
      simp [hx, this]

theorem lp_step (n : Nat) (p : Params) (allowed : Array Bool) (a0 : Array Nat) (rng : Rng)
    (hb : n * p.base ≤ p.maxShardBandwidth) (hbu : p.base ≤ u64Max)
    {i j : Nat} (hi : i < n) (hj : j < n) :
    (tryGrant n allowed (lpSt n p allowed a0 rng i j) (i * n + j) p.base).2
      = lpSt n p allowed a0 rng i (j + 1) := by
  cases ha : allowed[i * n + j]!
  · rw [lp_step_skip n p allowed a0 rng ha]
    simp [tryGrant, ha]
  · exact lp_step_grant n p allowed a0 rng hb hbu hi hj ha

theorem lp_row (n : Nat) (p : Params) (allowed : Array Bool) (a0 : Array Nat) (rng : Rng) (i : Nat) :
    lpSt n p allowed a0 rng i n = lpSt n p allowed a0 rng (i + 1) 0 := by
  have hcs : ∀ s, lpCS n allowed i n s = lpCS n allowed (i + 1) 0 s := by
    intro s
    simp only [lpCS]
    by_cases h1 : s < i
    · simp [h1, show s < i + 1 by omega]
    · by_cases h2 : s = i
      · subst h2; simp
      · simp [h1, h2, show ¬ s < i + 1 by omega]
        intro h; subst h; simp [lpRow]
  have hcr : ∀ r : Fin n, lpCR n allowed i n r = lpCR n allowed (i + 1) 0 r := by
    intro r
    simp only [lpCR, lpCol_succ, r.2, true_and]
    simp
  have hk : (i + 1) * n + 0 = i * n + n := by rw [Nat.succ_mul]; rfl
  simp only [lpSt, hcs, hk]
  simp only [St.mk.injEq, and_true, true_and]
  congr 1; funext r; rw [hcr r]

/-! ## The fold -/

theorem lp_fold (n : Nat) (p : Params) (allowed : Array Bool) (a0 : Array Nat) (rng : Rng)
    (hb : n * p.base ≤ p.maxShardBandwidth) (hbu : p.base ≤ u64Max) (st1 : St)
    (h0 : st1 = lpSt n p allowed a0 rng 0 0) :
    ∀ i, i ≤ n → (List.range (i * n)).foldl (fun st l => (tryGrant n allowed st l p.base).2) st1
      = lpSt n p allowed a0 rng i 0 := by
  intro i
  induction i with
  | zero => intro _; simpa using h0
  | succ i ih =>
    intro hi
    have hrow : ∀ j, j ≤ n → (List.range (i * n + j)).foldl
        (fun st l => (tryGrant n allowed st l p.base).2) st1 = lpSt n p allowed a0 rng i j := by
      intro j
      induction j with
      | zero => intro _; exact ih (by omega)
      | succ j ihj =>
        intro hj
        rw [show i * n + (j + 1) = (i * n + j) + 1 by omega, List.range_succ, List.foldl_append,
          ihj (by omega)]
        exact lp_step n p allowed a0 rng hb hbu (by omega) (by omega)
    rw [Nat.succ_mul, hrow n (Nat.le_refl _), lp_row]

theorem lp_min_u64 {y : Nat} (hy : y ≤ u64Max) (x : Nat) :
    Nat.min (Nat.min x u64Max) y = Nat.min x y := by
  simp only [Nat.min_def]
  split <;> split <;> (try split) <;> omega

theorem lp_init (n : Nat) (p : Params) (allowed : Array Bool) (a0 : Array Nat) (rng : Rng)
    (hMA : p.maxAllowance ≤ u64Max) (ha0 : a0.size = n * n) :
    ({ senderBudget := Array.replicate n p.maxShardBandwidth
       receiverBudget := Array.replicate n p.maxShardBandwidth
       allowance := a0.map (fun a => Nat.min (Nat.min (a + p.maxShardBandwidth / n) u64Max)
         p.maxAllowance)
       granted := Array.replicate (n * n) 0
       rng := rng } : St) = lpSt n p allowed a0 rng 0 0 := by
  simp only [lpSt, St.mk.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Array.ext
    · simp
    · intro s h1 h2; simp [lpCS, lpRow]
  · apply Array.ext
    · simp
    · intro s h1 h2; simp [lpCR, lpCol]
  · apply Array.ext
    · simp [ha0]
    · intro l h1 h2
      simp only [Array.getElem_map, Array.getElem_ofFn, lpDone, Nat.zero_mul, Nat.add_zero,
        Nat.not_lt_zero, false_and, ↓reduceIte, lpA1]
      rw [getElem!_pos a0 l (by simpa using h1)]
      exact lp_min_u64 hMA _
  · apply Array.ext
    · simp
    · intro l h1 h2; simp [lpDone]

theorem lp_final (n : Nat) (p : Params) (allowed : Array Bool) (a0 : Array Nat) (rng : Rng) :
    lpSt n p allowed a0 rng n 0 =
      { senderBudget := (linkPass n p allowed a0).sb,
        receiverBudget := (linkPass n p allowed a0).rb,
        allowance := (linkPass n p allowed a0).a2,
        granted := (linkPass n p allowed a0).g2,
        rng := rng } := by
  simp only [lpSt, linkPass, St.mk.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Array.ext
    · simp
    · intro s h1 h2; simp [lpCS, lpRow]
  · apply Array.ext
    · simp
    · intro r h1 h2; simp at h1; simp [lpCR, lpCol]
  · apply Array.ext
    · simp
    · intro l h1 h2; simp [lpDone, lpA1]
  · apply Array.ext
    · simp
    · intro l h1 h2; simp [lpDone]

/-- The link pass in closed form, under the two arithmetic facts it needs. -/
theorem linkPass_eq_gen {n : Nat} {p : Params} (hb : n * p.base ≤ p.maxShardBandwidth)
    (hMA : p.maxAllowance ≤ u64Max) (hbu : p.base ≤ u64Max)
    (allowed : Array Bool) (a0 : Array Nat) (ha0 : a0.size = n * n) (rng : Rng) :
    (List.range (n * n)).foldl (fun st l => (tryGrant n allowed st l p.base).2)
      ({ senderBudget := Array.replicate n p.maxShardBandwidth
         receiverBudget := Array.replicate n p.maxShardBandwidth
         allowance := a0.map (fun a => Nat.min (Nat.min (a + p.maxShardBandwidth / n) u64Max)
           p.maxAllowance)
         granted := Array.replicate (n * n) 0
         rng := rng } : St) =
      { senderBudget := (linkPass n p allowed a0).sb,
        receiverBudget := (linkPass n p allowed a0).rb,
        allowance := (linkPass n p allowed a0).a2,
        granted := (linkPass n p allowed a0).g2,
        rng := rng } := by
  rw [lp_fold n p allowed a0 rng hb hbu _ (lp_init n p allowed a0 rng hMA ha0) n (Nat.le_refl _),
    lp_final]

theorem linkPass_eq {n : Nat} {p : Params} (hn : 1 ≤ n)
    (hp : Params.calculate Config.pv86 n = some p)
    (allowed : Array Bool) (a0 : Array Nat) (_hal : allowed.size = n * n)
    (ha0 : a0.size = n * n) (rng : Rng) :
    let st1 : St :=
      { senderBudget := Array.replicate n p.maxShardBandwidth
        receiverBudget := Array.replicate n p.maxShardBandwidth
        allowance := a0.map (fun a => Nat.min (Nat.min (a + p.maxShardBandwidth / n) u64Max)
          p.maxAllowance)
        granted := Array.replicate (n * n) 0
        rng := rng }
    (List.range (n * n)).foldl (fun st l => (tryGrant n allowed st l p.base).2) st1 =
      { senderBudget := (linkPass n p allowed a0).sb,
        receiverBudget := (linkPass n p allowed a0).rb,
        allowance := (linkPass n p allowed a0).a2,
        granted := (linkPass n p allowed a0).g2,
        rng := rng } := by
  intro st1
  obtain ⟨hmsb, -, hma, -, hnb, -⟩ := pv86_facts hn hp
  have hbase : p.base ≤ n * p.base := by
    have := Nat.mul_le_mul_right p.base hn
    rwa [Nat.one_mul] at this
  exact linkPass_eq_gen (by omega) (by rw [hma]; decide) (by unfold u64Max; omega)
    allowed a0 ha0 rng

/-! ## The link counts are `DistDefs.cntS` / `cntR` -/

theorem linkPass_cntS (n : Nat) (p : Params) (allowed : Array Bool) (a0 : Array Nat) {s : Nat}
    (hs : s < n) : (linkPass n p allowed a0).cntS[s]! = cntS n allowed s := by
  rw [getElem!_pos _ s (by simp [linkPass, hs])]
  simp [linkPass, cntS]

theorem linkPass_cntR (n : Nat) (p : Params) (allowed : Array Bool) (a0 : Array Nat) {r : Nat}
    (hr : r < n) : (linkPass n p allowed a0).cntR[r]! = cntR n allowed r := by
  rw [getElem!_pos _ r (by simp [linkPass, hr])]
  simp [linkPass, cntR]

end ZkFormal.NearV3.Sched
