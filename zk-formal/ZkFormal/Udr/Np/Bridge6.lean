import ZkFormal.Udr.Np.Bridge5

/-!
# ZkFormal.Udr.Np.Bridge6 — the path values of the verifier's check

Fix a transcript at the query phase (deployed parameters) and a natural
layer-0 index `j` with verifier position `x = permAt 0 j`; `jp i = j % 2^(n0-i)`
is the path index at layer `i`.

* `Arr e`: the verifier's fold arriving at layer `e` (from layer `e - 1`),
  equal to the run's `foldW (e-1)` on the path (`arr_eq`);
* `rollInV` of `Arr e` is the run's `rollW (e-1)` on the path (`roll_eq`,
  assuming `DeepSemStmt`);
* the folded committed leaf is `Arr (c + a)` (`leaf_eq`).
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

local notation "P0" => Params.default

section
variable (A : Air) (τ : PTn)

/-- The verifier's fold arriving at layer `e` on the path through `x`. -/
def Arr (x e : Nat) : Fp8 :=
  foldPos (n0Of A P0 τ) (e - 1) (2 * (x >>> e)) (betaOf A P0 τ (e - 1))
    (Fv A P0 τ (e - 1) (2 * (x >>> e))) (Fv A P0 τ (e - 1) (2 * (x >>> e) + 1))

theorem ell_eq (Q : QData A P0 τ) : ellOf A P0 τ = n0Of A P0 τ - 5 := by
  simp only [ellOf, finalLayer, n0Of]; rfl

theorem arr_eq (hn0 : n0Of A P0 τ ≤ 27) (Q : QData A P0 τ) (j : Nat) (hj : j < 2 ^ n0Of A P0 τ)
    (e : Nat) (he1 : 1 ≤ e) (heℓ : e ≤ ellOf A P0 τ) :
    Fri.foldW (mkSetup A P0 τ hn0) (mkRun A P0 τ) (e - 1) (j % 2 ^ (n0Of A P0 τ - e)) () =
      Arr A τ (permAt A P0 τ 0 j) e := by
  have hl : ellOf A P0 τ ≤ n0Of A P0 τ := by rw [ell_eq A τ Q]; omega
  have hb : j % 2 ^ (n0Of A P0 τ - e) < 2 ^ (n0Of A P0 τ - (e - 1 + 1)) := by
    rw [show e - 1 + 1 = e by omega]; exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have := fold_eq_foldPos τ hn0 hl (e - 1) (by omega) _ hb (betaOf A P0 τ (e - 1))
  rw [show e - 1 + 1 = e by omega, permAt_path A P0 τ hl e j heℓ hj] at this
  exact this

theorem rollInV_eq (Q : QData A P0 τ) (op : List (List (List Fp))) (x i : Nat) (hi1 : 1 ≤ i)
    (hiℓ : i ≤ finalLayer A P0 Q.hdr) (v : Fp8) :
    rollInV (Stark.prep (F := Fp) A P0 τ.erase) op x i v =
      v + gammaOf A P0 τ i * (if rollInAt A P0 Q.hdr i then
        deepAt (F := Fp) (Stark.prep (F := Fp) A P0 τ.erase) op ((Stark.prep (F := Fp) A P0 τ.erase).n0 - i) x
        else 0) := by
  have := rollIn_eq Q i hi1 hiℓ v
    (deepAt (F := Fp) (Stark.prep (F := Fp) A P0 τ.erase) op ((Stark.prep (F := Fp) A P0 τ.erase).n0 - i) x)
  simp only [rollInV]
  cases h : (Stark.prep (F := Fp) A P0 τ.erase).gammas.lookup i <;> simp only [h] at this ⊢ <;> exact this

/-- The verifier's roll-in of `Arr e` is the run's `rollW (e-1)` on the path. -/
theorem roll_eq (hD : DeepSemStmt) (hok : NpOk A P0) (hs : Shaped (Vnp A P0) τ)
    (hq : (Vnp A P0).AtQuery τ) (hglob : (Vnp A P0).global ((Vnp A P0).prep τ.erase) = true)
    (hn0 : n0Of A P0 τ ≤ 27) (Q : QData A P0 τ) (j : Nat) (hj : j < 2 ^ n0Of A P0 τ)
    (e : Nat) (he1 : 1 ≤ e) (heℓ : e ≤ ellOf A P0 τ) :
    rollInV (Stark.prep (F := Fp) A P0 τ.erase) ((Vnp A P0).trueOpenings τ (permAt A P0 τ 0 j))
        (permAt A P0 τ 0 j) e (Arr A τ (permAt A P0 τ 0 j) e) =
      Fri.rollW (mkSetup A P0 τ hn0) (mkRun A P0 τ) (e - 1) (j % 2 ^ (n0Of A P0 τ - e)) () := by
  have hl : ellOf A P0 τ ≤ n0Of A P0 τ := by rw [ell_eq A τ Q]; omega
  have hx : permAt A P0 τ 0 j < 2 ^ n0Of A P0 τ := by
    have := permK_lt (n0Of A P0 τ) (ellOf A P0 τ) (ellOf A P0 τ) j
      (by rw [show n0Of A P0 τ - ellOf A P0 τ + ellOf A P0 τ = n0Of A P0 τ by omega]; exact hj)
    simp only [permAt, Nat.sub_zero]
    rwa [show n0Of A P0 τ - ellOf A P0 τ + ellOf A P0 τ = n0Of A P0 τ by omega] at this
  have hell := Q.ell
  rw [rollInV_eq A τ Q _ _ e he1 (by rw [← hell]; exact heℓ), prepF_n0 Q,
    hD A P0 hok τ hs hq hglob _ hx (n0Of A P0 τ - e) (by omega),
    show n0Of A P0 τ - (n0Of A P0 τ - e) = e by omega]
  simp only [Fri.rollW, line]
  rw [arr_eq A τ hn0 Q j hj e he1 heℓ]
  show _ = _ + gammaOf A P0 τ (e - 1 + 1) * rollG A P0 τ (e - 1) _ ()
  simp only [rollG, show e - 1 + 1 = e by omega, Q.hhdr]
  rw [permAt_path A P0 τ hl e j heℓ hj]

theorem shl_add (b t a : Nat) (ht : t < 2 ^ a) :
    ((b <<< a) + t) >>> a = b ∧ ((b <<< a) + t) % 2 ^ a = t := by
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hp : 0 < 2 ^ a := Nat.pow_pos (by omega)
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt ht, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

theorem shr_lt (x n c : Nat) (hx : x < 2 ^ n) (hc : c ≤ n) : x >>> c < 2 ^ (n - c) := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add, show c + (n - c) = n by omega]; exact hx)

/-- The FRI word at the layer of commit `k`, on verifier positions. -/
theorem Fv_committed (Q : QData A P0 τ) (k : Nat) (hk : k < (commitsOf A P0 τ).length) (P : Nat)
    (hP : P < 2 ^ (n0Of A P0 τ - ((commitsOf A P0 τ)[k]).1)) :
    Fv A P0 τ ((commitsOf A P0 τ)[k]).1 P = committedAt τ k ((commitsOf A P0 τ)[k]).2 P := by
  have hl : ellOf A P0 τ ≤ n0Of A P0 τ := by rw [ell_eq A τ Q]; omega
  have hcl : ((commitsOf A P0 τ)[k]).1 ≤ ellOf A P0 τ := by
    have := (commits_mem A P0 Q.hdr _ (by rw [← Q.commits]; exact List.getElem_mem hk)).1
    rw [Q.ell]; omega
  simp only [Fv]
  rw [friF_committed A P0 τ k hk, (permAt_permInv τ hl _ hcl P hP).1]

/-- At a layer strictly inside a commit block the FRI word is the plain fold. -/
theorem Fv_inner (hn0 : n0Of A P0 τ ≤ 27) (Q : QData A P0 τ) (i : Nat) (hiℓ : i < ellOf A P0 τ)
    (hnc : ∀ k (hk : k < (commitsOf A P0 τ).length), ((commitsOf A P0 τ)[k]).1 ≠ i + 1)
    (hnr : rollInAt A P0 Q.hdr (i + 1) = false) (q : Nat) (hq : q < 2 ^ (n0Of A P0 τ - (i + 1))) :
    Fv A P0 τ (i + 1) q = foldPos (n0Of A P0 τ) i (2 * q) (betaOf A P0 τ i)
      (Fv A P0 τ i (2 * q)) (Fv A P0 τ i (2 * q + 1)) := by
  have hl : ellOf A P0 τ ≤ n0Of A P0 τ := by rw [ell_eq A τ Q]; omega
  obtain ⟨h1, h2⟩ := permAt_permInv τ hl (i + 1) (by omega) q hq
  simp only [Fv]
  rw [friF_virtual A P0 τ i hnc]
  generalize hj : permInvK (n0Of A P0 τ) (ellOf A P0 τ) (ellOf A P0 τ - (i + 1)) q = j'' at h1 h2
  have hz : rollG A P0 τ i j'' () = 0 := by
    simp only [rollG, Q.hhdr, hnr, Bool.false_eq_true, ↓reduceIte]
  have := fold_eq_foldPos τ hn0 hl i hiℓ j'' h2 (betaOf A P0 τ i)
  rw [h1] at this
  simp only [Fv] at this
  rw [← this]
  simp only [line, hz]
  show _ + _ * 0 = _
  rw [Semiring.mul_zero, Semiring.add_zero]
  rfl

/-- Structure of commit `k`: a block `(c0, c0 + a)` with `a ≥ 1`, inside `[0, ℓ]`,
without commitments or roll-ins strictly inside. -/
theorem block_facts (Q : QData A P0 τ) (k : Nat) (hk : k < (commitsOf A P0 τ).length) :
    1 ≤ ((commitsOf A P0 τ)[k]).2 ∧
    ((commitsOf A P0 τ)[k]).1 + ((commitsOf A P0 τ)[k]).2 ≤ ellOf A P0 τ ∧
    (∀ i, ((commitsOf A P0 τ)[k]).1 < i → i < ((commitsOf A P0 τ)[k]).1 + ((commitsOf A P0 τ)[k]).2 →
      rollInAt A P0 Q.hdr i = false ∧
      ∀ k' (hk' : k' < (commitsOf A P0 τ).length), ((commitsOf A P0 τ)[k']).1 ≠ i) := by
  have hcm := Q.commits
  have hk2 : k < (friCommits A P0 Q.hdr).length := by rw [← hcm]; exact hk
  obtain ⟨-, h2, h3, h4⟩ := chain_get A P0 Q.hdr _ _ 0 (chain_commits A P0 Q.hdr) k hk2
  have hs := List.pairwise_iff_getElem.mp (commits_sorted A P0 Q.hdr)
  simp only [hcm, Q.ell]
  refine ⟨h2, ?_, fun i hi1 hi2 => ⟨h3 i hi1 hi2, fun k' hk' heq => ?_⟩⟩
  · split at h4
    · rename_i hh
      have := (commits_mem A P0 Q.hdr _ (List.getElem_mem hh)).1
      omega
    · omega
  · have hk'2 : k' < (friCommits A P0 Q.hdr).length := hk'
    rcases Nat.lt_trichotomy k' k with hlt | heq' | hgt
    · have := hs k' k hk'2 hk2 hlt; omega
    · subst heq'; omega
    · split at h4
      · rename_i hh
        by_cases hkk : k' = k + 1
        · subst hkk; omega
        · have := hs (k + 1) k' hh hk'2 (by omega); omega
      · omega

/-- **The folded committed leaf** is the fold arriving at the end of the block. -/
theorem leaf_eq (hn0 : n0Of A P0 τ ≤ 27) (Q : QData A P0 τ) (x : Nat) (hx : x < 2 ^ n0Of A P0 τ)
    (k : Nat) (hk : k < (commitsOf A P0 τ).length) (o : List (List Fp))
    (ho : ksOfRow (F := Fp) (K := Fp8) (o.getD 0 []) =
      ksOfRow ((matOf (oracleOf τ (3 + k)) 0).row ((x >>> ((commitsOf A P0 τ)[k]).1) >>> ((commitsOf A P0 τ)[k]).2)))
    (hlen : (ksOfRow (F := Fp) (K := Fp8) (o.getD 0 [])).length = 2 ^ ((commitsOf A P0 τ)[k]).2) :
    foldLeaf (F := Fp) (Stark.prep (F := Fp) A P0 τ.erase) ((commitsOf A P0 τ)[k]).1 ((commitsOf A P0 τ)[k]).2
        ((x >>> ((commitsOf A P0 τ)[k]).1) >>> ((commitsOf A P0 τ)[k]).2) (ksOfRow (o.getD 0 [])) =
      Arr A τ x (((commitsOf A P0 τ)[k]).1 + ((commitsOf A P0 τ)[k]).2) := by
  obtain ⟨ha1, hcaℓ, hin⟩ := block_facts A τ Q k hk
  generalize hc0 : ((commitsOf A P0 τ)[k]).1 = c0 at *
  generalize ha : ((commitsOf A P0 τ)[k]).2 = a at *
  have hℓ := ell_eq A τ Q
  have hn0c : c0 + a ≤ n0Of A P0 τ := by omega
  have hpa : (x >>> c0) >>> a < 2 ^ (n0Of A P0 τ - (c0 + a)) := by
    rw [← Nat.shiftRight_add]; exact shr_lt _ _ _ hx hn0c
  let U : Nat → Nat → Fp8 := fun s q => if s < a then Fv A P0 τ (c0 + s) q else
    foldPos (n0Of A P0 τ) (c0 + a - 1) (2 * q) (betaOf A P0 τ (c0 + a - 1))
      (Fv A P0 τ (c0 + a - 1) (2 * q)) (Fv A P0 τ (c0 + a - 1) (2 * q + 1))
  have key := foldLeaf_eq (Stark.prep (F := Fp) A P0 τ.erase) c0 a ((x >>> c0) >>> a) _ U hlen
    (fun t ht => ?_) (fun s q hs hq => ?_)
  · rw [key]
    simp only [U, Nat.lt_irrefl, ↓reduceIte, Arr, Nat.shiftRight_add,
      show c0 + a - 1 = c0 + a - 1 from rfl]
  · -- the leaf values
    obtain ⟨e1, e2⟩ := shl_add ((x >>> c0) >>> a) t a ht
    have hP : ((x >>> c0) >>> a) <<< a + t < 2 ^ (n0Of A P0 τ - c0) := by
      rw [Nat.shiftLeft_eq]
      have : 2 ^ (n0Of A P0 τ - c0) = 2 ^ (n0Of A P0 τ - (c0 + a)) * 2 ^ a := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [this]
      have := Nat.mul_le_mul_right (2 ^ a) (show (x >>> c0) >>> a + 1 ≤ 2 ^ (n0Of A P0 τ - (c0 + a)) by omega)
      rw [Nat.succ_mul] at this; omega
    simp only [U, show 0 < a by omega, ↓reduceIte, Nat.add_zero]
    rw [← hc0, Fv_committed A τ Q k hk _ (by rw [hc0]; exact hP), ho]
    simp only [committedAt, ha]
    rw [hc0, e1, e2]
  · -- the folds
    have hβ : (Stark.prep (F := Fp) A P0 τ.erase).betas.getD (c0 + s) 0 = betaOf A P0 τ (c0 + s) :=
      prepF_betas Q (c0 + s) (by rw [← Q.ell]; omega)
    rw [hβ, prepF_n0 Q]
    by_cases hs1 : s + 1 < a
    · simp only [U, hs1, hs, ↓reduceIte]
      obtain ⟨hr, hc⟩ := hin (c0 + s + 1) (by omega) (by omega)
      have hq' : q < 2 ^ (n0Of A P0 τ - (c0 + s + 1)) := by
        have h2 : 2 ^ (n0Of A P0 τ - (c0 + s + 1)) = 2 ^ (n0Of A P0 τ - (c0 + a)) * 2 ^ (a - (s + 1)) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [h2]
        have := Nat.mul_le_mul_right (2 ^ (a - (s + 1)))
          (show (x >>> c0) >>> a + 1 ≤ 2 ^ (n0Of A P0 τ - (c0 + a)) by omega)
        omega
      rw [show c0 + (s + 1) = c0 + s + 1 by omega]
      exact Fv_inner A τ hn0 Q (c0 + s) (by omega) (fun k' hk' => by
        have := hc k' hk'; omega) hr q hq'
    · have hsa : s + 1 = a := by omega
      simp only [U, hs, ↓reduceIte, show ¬ (s + 1 < a) from hs1]
      rw [show c0 + a - 1 = c0 + s by omega]

end
end ZkFormal.Udr.Np
