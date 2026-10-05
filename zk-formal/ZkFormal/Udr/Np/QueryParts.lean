import ZkFormal.Udr.Np.Domain
import ZkFormal.Udr.Np.Statements
import ZkFormal.Udr.Main

/-!
# ZkFormal.Udr.Np.QueryParts — the FRI run of a transcript; query-phase sublemmas

* `mkRun`: the `Fri.Run Fp8` read from a transcript (`friF`, `rollG`, `betaOf`,
  `gammaOf`, the final polynomial);
* `eFri`: the radii `e i = eRad (n0 - i)`;
* generic counting through the position maps (`count_le_of_cover`), inverse
  position maps (`permInvK`), and the zero columns of a fully batched word;
* the open sublemmas of `QueryStmt` as named propositions:
  `LocalBridgeStmt` (a passing verifier position yields a passing FRI path and
  the layer-0 DEEP identity) and `GoodStmt` (the drawn FRI challenges are good).
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-! ## Counting through a covering map -/

theorem sum_ite_eq_count {α : Type} (l : List α) (B : α → Prop) :
    (l.map fun j => (open Classical in if B j then 1 else 0)).sum = count l B := by
  classical
  induction l with
  | nil => simp [count]
  | cons a l ih => rw [List.map_cons, List.sum_cons, ih, count_cons]; omega

/-- If every `p ∈ l` with `A p` is the image `π j` of some `j ∈ I` with `B j`,
then `#A ≤ #B` (provided `l` is duplicate-free). -/
theorem count_le_of_cover {α β : Type} (l : List α) (hl : l.Nodup) (I : List β) (π : β → α)
    (A : α → Prop) (B : β → Prop) (h : ∀ p ∈ l, A p → ∃ j ∈ I, π j = p ∧ B j) :
    count l A ≤ count I B := by
  classical
  refine Nat.le_trans (count_mono_mem l (F := fun p => ∃ j ∈ I, π j = p ∧ B j) h) ?_
  refine Nat.le_trans (count_exists_mem_le l I (fun j p => π j = p ∧ B j)) ?_
  rw [← sum_ite_eq_count]
  refine sum_le_of_le _ _ _ fun j _ => ?_
  by_cases hB : B j
  · simp only [hB, ↓reduceIte]
    exact count_le_one_of_unique hl _ fun a b ha hb => ha.1 ▸ hb.1
  · have : count l (fun p => π j = p ∧ B j) ≤ count l (fun _ => False) :=
      count_mono _ fun _ h => hB h.2
    rw [count_const] at this
    simp only [hB, ↓reduceIte] at this ⊢
    exact this

/-! ## Inverse position maps -/

/-- Inverse of `permK`. -/
def permInvK (n0 ℓ : Nat) : Nat → Nat → Nat
  | 0, p => p
  | k + 1, p => permInvK n0 ℓ k (p / 2) + (p % 2) * 2 ^ (n0 - ℓ + k)

theorem permInvK_spec (n0 ℓ : Nat) : ∀ k p, p < 2 ^ (n0 - ℓ + k) →
    permInvK n0 ℓ k p < 2 ^ (n0 - ℓ + k) ∧ permK n0 ℓ k (permInvK n0 ℓ k p) = p
  | 0, p, hp => ⟨by simpa [permInvK] using hp, rfl⟩
  | k + 1, p, hp => by
    have hh : 0 < 2 ^ (n0 - ℓ + k) := Nat.pow_pos (by omega)
    rw [show n0 - ℓ + (k + 1) = n0 - ℓ + k + 1 by omega, Nat.pow_succ] at hp ⊢
    obtain ⟨h1, h2⟩ := permInvK_spec n0 ℓ k (p / 2) (by omega)
    simp only [permInvK]
    generalize permInvK n0 ℓ k (p / 2) = q at h1 h2
    have hm : p % 2 ≤ 1 := by omega
    have hpm : p % 2 * 2 ^ (n0 - ℓ + k) ≤ 2 ^ (n0 - ℓ + k) := by
      calc p % 2 * 2 ^ (n0 - ℓ + k) ≤ 1 * 2 ^ (n0 - ℓ + k) := Nat.mul_le_mul_right _ hm
        _ = _ := Nat.one_mul _
    refine ⟨by omega, ?_⟩
    rw [permK_succ]
    have e1 : (q + p % 2 * 2 ^ (n0 - ℓ + k)) % 2 ^ (n0 - ℓ + k) = q := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]
    have e2 : (q + p % 2 * 2 ^ (n0 - ℓ + k)) / 2 ^ (n0 - ℓ + k) = p % 2 := by
      rw [Nat.add_mul_div_right _ _ hh, Nat.div_eq_of_lt h1, Nat.zero_add]
    rw [e1, e2, h2]; omega

/-- `permK` covers its range. -/
theorem permK_surj (n0 ℓ k p : Nat) (hp : p < 2 ^ (n0 - ℓ + k)) :
    ∃ j, j < 2 ^ (n0 - ℓ + k) ∧ permK n0 ℓ k j = p :=
  ⟨_, (permInvK_spec n0 ℓ k p hp).1, (permInvK_spec n0 ℓ k p hp).2⟩

/-! ## Batching: columns of a fully batched word -/

theorem batchAll_zero_cols {K : Type} [Field K] :
    ∀ (rs : List K) (W : Word Nat K), (∀ p c, 2 ^ rs.length ≤ c → W p c = 0) →
      ∀ p c, 1 ≤ c → batchAll rs W p c = 0
  | [], W, h, p, c, hc => h p c (by simpa using hc)
  | r :: rs, W, h, p, c, hc => by
    refine batchAll_zero_cols rs (batchStep W r) (fun p c hc => ?_) p c hc
    simp only [batchStep, line, evenCols, oddCols]
    rw [h p (2 * c) (by simp [List.length_cons, Nat.pow_succ] at hc ⊢; omega),
      h p (2 * c + 1) (by simp [List.length_cons, Nat.pow_succ] at hc ⊢; omega)]
    grind

/-! ## The FRI run -/

section
variable (A : Air) (prm : Params)

/-- The FRI run of a transcript: `γ i` is the roll-in challenge entering
layer `i + 1`. -/
def mkRun (τ : PTn) : Fri.Run Fp8 where
  f := friF A prm τ
  G := rollG A prm τ
  β := betaOf A prm τ
  γ i := gammaOf A prm τ (i + 1)
  pr k := (τ.elems.getD 2 []).getD k 0

/-- FRI radii: `e i = eRad (n0 - i)`. -/
def eFri (τ : PTn) (i : Nat) : Nat := eRad prm (n0Of A prm τ - i)

end

/-! ## Open sublemmas of `QueryStmt` -/

/-- **Local bridge.** At the query phase of a shaped transcript accepted by
`global`, if the verifier's checks pass at the verifier position
`permAt 0 j` of the natural layer-0 index `j`, then the FRI path through `j`
passes (`passK`), and layer 0 agrees with the batched DEEP word of the
largest class there.  (`5 ≤ n0`: some table exists.) -/
def LocalBridgeStmt : Prop :=
  ∀ (A : Air) (prm : Params), NpOk A prm → ∀ (τ : PTn) (hn0 : n0Of A prm τ ≤ 27),
    Shaped (Vnp A prm) τ → (Vnp A prm).AtQuery τ →
    (Vnp A prm).global ((Vnp A prm).prep τ.erase) = true → 5 ≤ n0Of A prm τ →
    ∀ j, j < 2 ^ n0Of A prm τ →
      (Vnp A prm).ChecksPass τ (permAt A prm τ 0 j) ((Vnp A prm).trueOpenings τ (permAt A prm τ 0 j)) →
      Fri.passK (mkSetup A prm τ hn0) (mkRun A prm τ) (ellOf A prm τ) j ∧
        friF A prm τ 0 j () = deepAtPos A prm τ (n0Of A prm τ) (permAt A prm τ 0 j)

/-- **Good FRI challenges.** At the query phase, `FriGoodSoFar` (every drawn
FRI challenge satisfies its strong-line condition) is `Fri.GoodChallenges`. -/
def GoodStmt : Prop :=
  ∀ (A : Air) (prm : Params), NpOk A prm → ∀ (τ : PTn) (hn0 : n0Of A prm τ ≤ 27),
    Shaped (Vnp A prm) τ → (Vnp A prm).AtQuery τ →
    (Vnp A prm).global ((Vnp A prm).prep τ.erase) = true →
    FriGoodSoFar A prm τ → Fri.GoodChallenges (mkSetup A prm τ hn0) (mkRun A prm τ) (eFri A prm τ)

end ZkFormal.Udr.Np
