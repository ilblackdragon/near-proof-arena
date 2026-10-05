import ZkFormal.Udr.Np.Bridge3

/-!
# ZkFormal.Udr.Np.Bridge4 — FRI words on verifier positions; the verifier's check unfolded

* `checkAt_true`: what `checkAt` passing says (the commit loop as a `foldl` of `stepV`);
* `Fv i q`: the FRI word of layer `i` at verifier position `q`;
* the FRI word at committed layers is the committed oracle; at other layers
  it is the fold plus roll-in; the fold of the run at natural index `j'` is the
  verifier's `foldPos` at verifier position `2·permAt (i+1) j'`.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-! ## The verifier's check, unfolded -/

def rollInV (c : Ctx Fp8) (op : List (List (List Fp))) (x i : Nat) (v : Fp8) : Fp8 :=
  match c.gammas.lookup i with
  | some γ => v + γ * deepAt (F := Fp) c op (c.n0 - i) x
  | none => v

/-- What one step of the commit loop does. -/
def StepSpec (c : Ctx Fp8) (op : List (List (List Fp))) (x : Nat)
    (f : Bool × Fp8 → (Nat × Nat) × List (List Fp) → Bool × Fp8) : Prop :=
  ∀ acc e, (f acc e).2 = foldLeaf (F := Fp) c e.1.1 e.1.2 ((x >>> e.1.1) >>> e.1.2) (ksOfRow (e.2.getD 0 [])) ∧
    ((f acc e).1 = true → acc.1 = true ∧
      (ksOfRow (F := Fp) (e.2.getD 0 [])).getD ((x >>> e.1.1) % 2 ^ e.1.2) 0 =
        (if e.1.1 = 0 then acc.2 else rollInV c op x e.1.1 acc.2) ∧
      (ksOfRow (F := Fp) (K := Fp8) (e.2.getD 0 [])).length = 2 ^ e.1.2)

theorem checkAt_true (c : Ctx Fp8) (x : Nat) (op : List (List (List Fp)))
    (h : checkAt (F := Fp) c x op = true) :
    ∃ f, StepSpec c op x f ∧
    c.ok = true ∧ ((c.commits.zip (op.drop 3)).foldl f (true, deepAt (F := Fp) c op c.n0 x)).1 = true ∧
      (op.drop 3).length = c.commits.length ∧
      (if c.ℓ = 0 then ((c.commits.zip (op.drop 3)).foldl f (true, deepAt (F := Fp) c op c.n0 x)).2
        else rollInV c op x c.ℓ ((c.commits.zip (op.drop 3)).foldl f (true, deepAt (F := Fp) c op c.n0 x)).2) =
        c.finalPoly.getD 0 0 + c.finalPoly.getD 1 0 *
          Fp8.ofBase (domPoint (K := Fp8) c.n0 (c.n0 - c.ℓ) (x >>> c.ℓ)) := by
  unfold checkAt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨_, ?_, h1, h2, h3, ?_⟩
  · intro acc e
    refine ⟨rfl, fun hf => ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨hf1, hf2, hf3⟩ := hf
    refine ⟨hf1, ?_, hf3⟩
    rw [hf2]
    by_cases h0 : e.1.1 = 0
    · simp [h0]
    · simp only [h0, ↓reduceIte, rollInV]
      cases e.1.1 <;> cases c.gammas.lookup _ <;> rfl
  · refine Eq.trans ?_ h4
    by_cases hℓ : c.ℓ = 0
    · simp only [hℓ, ↓reduceIte]
    · simp only [hℓ, ↓reduceIte, rollInV]
      generalize ((c.commits.zip (op.drop 3)).foldl _ (true, deepAt (F := Fp) c op c.n0 x)).2 = v
      cases c.gammas.lookup c.ℓ <;> rfl

/-! ## Base-field embedding of inverses -/

theorem ofBase_ne_zero {a : Fp} (h : a ≠ 0) : Fp8.ofBase a ≠ 0 := fun e => h (Fp8.ofBase_inj e)

theorem ofBase_inv {a : Fp} (h : a ≠ 0) : Fp8.ofBase a⁻¹ = (Fp8.ofBase a)⁻¹ := by
  have h1 : Fp8.ofBase a * Fp8.ofBase a⁻¹ = 1 := by
    rw [← Fp8.ofBase_mul, Field.mul_inv_cancel h]; rfl
  have h2 := Field.inv_mul_cancel (ofBase_ne_zero h)
  calc Fp8.ofBase a⁻¹ = ((Fp8.ofBase a)⁻¹ * Fp8.ofBase a) * Fp8.ofBase a⁻¹ := by rw [h2, Semiring.one_mul]
    _ = (Fp8.ofBase a)⁻¹ * (Fp8.ofBase a * Fp8.ofBase a⁻¹) := by rw [Semiring.mul_assoc]
    _ = _ := by rw [h1, Semiring.mul_one]

theorem fp_two_ne_zero : (2 : Fp) ≠ 0 := by decide +kernel

/-! ## FRI words on verifier positions -/

section
variable (A : Air) (prm : Params)

/-- The FRI word of layer `i` at verifier position `q`. -/
def Fv (τ : PTn) (i q : Nat) : Fp8 :=
  friF A prm τ i (permInvK (n0Of A prm τ) (ellOf A prm τ) (ellOf A prm τ - i) q) ()

variable {A prm}

theorem permInv_permAt (τ : PTn) (hl : ellOf A prm τ ≤ n0Of A prm τ) (i : Nat) (hi : i ≤ ellOf A prm τ)
    (j' : Nat) (hj : j' < 2 ^ (n0Of A prm τ - i)) :
    permInvK (n0Of A prm τ) (ellOf A prm τ) (ellOf A prm τ - i) (permAt A prm τ i j') = j' := by
  have e : n0Of A prm τ - ellOf A prm τ + (ellOf A prm τ - i) = n0Of A prm τ - i := by omega
  have hb := permK_lt (n0Of A prm τ) (ellOf A prm τ) (ellOf A prm τ - i) j' (by rw [e]; exact hj)
  obtain ⟨h1, h2⟩ := permInvK_spec (n0Of A prm τ) (ellOf A prm τ) (ellOf A prm τ - i) _ hb
  exact permK_inj _ _ _ _ _ h1 (by rw [e]; exact hj) h2

theorem Fv_permAt (τ : PTn) (hl : ellOf A prm τ ≤ n0Of A prm τ) (i : Nat) (hi : i ≤ ellOf A prm τ)
    (j' : Nat) (hj : j' < 2 ^ (n0Of A prm τ - i)) :
    Fv A prm τ i (permAt A prm τ i j') = friF A prm τ i j' () := by
  simp only [Fv]; rw [permInv_permAt τ hl i hi j' hj]

theorem permAt_permInv (τ : PTn) (hl : ellOf A prm τ ≤ n0Of A prm τ) (i : Nat) (hi : i ≤ ellOf A prm τ)
    (q : Nat) (hq : q < 2 ^ (n0Of A prm τ - i)) :
    permAt A prm τ i (permInvK (n0Of A prm τ) (ellOf A prm τ) (ellOf A prm τ - i) q) = q ∧
    permInvK (n0Of A prm τ) (ellOf A prm τ) (ellOf A prm τ - i) q < 2 ^ (n0Of A prm τ - i) := by
  have e : n0Of A prm τ - ellOf A prm τ + (ellOf A prm τ - i) = n0Of A prm τ - i := by omega
  obtain ⟨h1, h2⟩ := permInvK_spec (n0Of A prm τ) (ellOf A prm τ) (ellOf A prm τ - i) q (by rw [e]; exact hq)
  exact ⟨h2, by rw [← e]; exact h1⟩

/-- The run's fold at natural index `j'` is the verifier's fold at `2 q`. -/
theorem fold_eq_foldPos (τ : PTn) (hn0 : n0Of A prm τ ≤ 27) (hl : ellOf A prm τ ≤ n0Of A prm τ)
    (i : Nat) (hi : i < ellOf A prm τ) (j' : Nat) (hj : j' < 2 ^ (n0Of A prm τ - (i + 1))) (β : Fp8) :
    line (Fri.evenW (mkSetup A prm τ hn0) i (friF A prm τ i)) (Fri.oddW (mkSetup A prm τ hn0) i (friF A prm τ i))
      β j' () =
    foldPos (n0Of A prm τ) i (2 * permAt A prm τ (i + 1) j') β
      (Fv A prm τ i (2 * permAt A prm τ (i + 1) j')) (Fv A prm τ i (2 * permAt A prm τ (i + 1) j' + 1)) := by
  obtain ⟨k, hk⟩ : ∃ k, ellOf A prm τ - i = k + 1 := ⟨ellOf A prm τ - i - 1, by omega⟩
  have hk' : ellOf A prm τ - (i + 1) = k := by omega
  have e : n0Of A prm τ - (i + 1) = n0Of A prm τ - ellOf A prm τ + k := by omega
  have hj2 : j' < 2 ^ (n0Of A prm τ - ellOf A prm τ + k) := by rw [← e]; exact hj
  have hlo : permAt A prm τ i j' = 2 * permAt A prm τ (i + 1) j' := by
    simp only [permAt]; rw [hk, hk', permK_lo _ _ _ _ hj2]
  have hhi : permAt A prm τ i (j' + 2 ^ (n0Of A prm τ - (i + 1))) = 2 * permAt A prm τ (i + 1) j' + 1 := by
    simp only [permAt]; rw [hk, hk', e, permK_hi _ _ _ _ hj2]
  have hbig : n0Of A prm τ - i = n0Of A prm τ - (i + 1) + 1 := by omega
  have hj0 : j' < 2 ^ (n0Of A prm τ - i) := by
    rw [hbig, Nat.pow_succ]; omega
  have hj1 : j' + 2 ^ (n0Of A prm τ - (i + 1)) < 2 ^ (n0Of A prm τ - i) := by
    rw [hbig, Nat.pow_succ]; omega
  rw [← hhi, ← hlo, Fv_permAt τ hl i (by omega) j' hj0, Fv_permAt τ hl i (by omega) _ hj1]
  rw [hlo]
  simp only [line, Fri.evenW, Fri.oddW, foldPos]
  have hxs : (mkSetup A prm τ hn0).xs i j' =
      Fp8.ofBase (domPoint (K := Fp8) (n0Of A prm τ) (n0Of A prm τ - i) (2 * permAt A prm τ (i + 1) j')) := by
    show pt _ _ (permAt A prm τ i j') = _
    rw [hlo]; rfl
  have hnn : (mkSetup A prm τ hn0).nn (i + 1) = 2 ^ (n0Of A prm τ - (i + 1)) := rfl
  rw [hxs, hnn]
  generalize hy : (domPoint (K := Fp8) (n0Of A prm τ) (n0Of A prm τ - i) (2 * permAt A prm τ (i + 1) j') : Fp) = y
  have hy0 : y ≠ 0 := by
    intro h0
    apply pt_ne_zero (n0 := n0Of A prm τ) (m := n0Of A prm τ - i) (by omega) (2 * permAt A prm τ (i + 1) j')
    rw [pt_eq]; rw [← hy] at h0; show Fp8.ofBase _ = 0; rw [show (31 : Fp) ^ 2 ^ (n0Of A prm τ - (n0Of A prm τ - i)) *
      Fp.twoAdicGen (n0Of A prm τ - i) ^ bitrev (n0Of A prm τ - i) (2 * permAt A prm τ (i + 1) j') = 0 from h0]; rfl
  rw [ofBase_inv (fp_mul_ne_zero fp_two_ne_zero hy0), Fp8.ofBase_mul]
  have : Fp8.ofBase 2 = (2 : Fp8) := rfl
  rw [this]
  grind

end
end ZkFormal.Udr.Np
