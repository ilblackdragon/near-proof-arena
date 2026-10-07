import ZkFormal.NearV3.Sched.Spec.Steps
import ZkFormal.Chacha.RngSpec

/-!
# ZkFormal.NearV3.Sched.Spec.Draws — RNG words drawn by the replay (M4, heights of `genV3` / `chachaV3`)

Lane `v3-sched`. The shuffle of a round with `L` entries makes `L − 1` `gen_index` calls, each
drawing at most 64 words (the fuel: `genAt_some_iff`, at most 63 rejections). Every other step
leaves the RNG untouched (`tryGrant_rng`). Hence (`simR_draws`): if the replay starts at stream
position `k` (`rngAt key k`; `lpState` starts at `Rng.ofSeed seed = rngAt (leWords seed) 0`), it
ends at a position `k' ≤ k + 64·(S − Rd)`, `S − Rd = Σ_rounds (L − 1)` the number of calls.

This bound is all the spec gives: a call drawing 64 words is legal. With the step budget
(`steps_pv86`) the worst case over a claim is 154,499 calls, i.e. 9,887,936 words
(`Complete/Height.worstK`), which exceeds `2^22` rows in `genV3` and `chachaV3`.
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler ZkFormal.Chacha

theorem genAt_pos_le : ∀ (fuel n : Nat) (key : List Nat) (k j k' : Nat),
    genAt fuel n key k = some (j, k') → k < k' ∧ k' ≤ k + fuel
  | 0, _, _, _, _, _, h => by simp [genAt] at h
  | f + 1, n, key, k, j, k', h => by
    simp only [genAt] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · have := genAt_pos_le f n key (k + 1) j k' h; omega

/-- A shuffle loop of `i` calls from stream position `k` ends at a position `≤ k + 64·i`. -/
theorem shuffleLoop_draws {α : Type} (key : List Nat) :
    ∀ (i : Nat) (l : List α) (k : Nat) (l' : List α) (r' : Rng),
      shuffleLoop i l (rngAt key k) = some (l', r') → ∃ k', r' = rngAt key k' ∧ k' ≤ k + 64 * i
  | 0, l, k, l', r', h => by
    simp only [shuffleLoop, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨k, h.2.symm, by omega⟩
  | i + 1, l, k, l', r', h => by
    simp only [shuffleLoop, genIndex_rngAt] at h
    cases hg : genAt 64 (i + 2) key k with
    | none => simp [hg] at h
    | some p =>
      obtain ⟨j, k1⟩ := p
      simp only [hg, Option.map_some] at h
      obtain ⟨-, hk1⟩ := genAt_pos_le 64 (i + 2) key k j k1 hg
      obtain ⟨k', e, hk'⟩ := shuffleLoop_draws key i _ k1 l' r' h
      exact ⟨k', e, by rw [Nat.mul_succ]; omega⟩

theorem shuffle_draws {α : Type} (key : List Nat) (l : List α) (k : Nat) (l' : List α) (r' : Rng)
    (h : shuffle l (rngAt key k) = some (l', r')) : ∃ k', r' = rngAt key k' ∧ k' ≤ k + 64 * (l.length - 1) :=
  shuffleLoop_draws key _ l k l' r' h

theorem stepE_rng (n : Nat) (allowed : Array Bool) (reqs : List Req) (K z t v : Nat) (st : St) :
    (stepE n allowed reqs K z t v st).1.rng = st.rng := by
  unfold stepE
  split
  · rfl
  · simp only
    split <;> exact tryGrant_rng n allowed st _ _

theorem runL_rng (n : Nat) (allowed : Array Bool) (reqs : List Req) (K z : Nat) :
    ∀ (vs : List Nat) (t : Nat) (st : St), (runL n allowed reqs K z vs t st).1.rng = st.rng
  | [], _, _ => rfl
  | v :: vs, t, st => by
    simp only [runL]
    rw [runL_rng n allowed reqs K z vs (t + 1), stepE_rng]

/-- `gen_index` calls of the rounds: `Σ (L − 1) = S − Rd` for nonempty rounds. -/
def callsOf (rs : List RoundD) : Nat := (rs.map fun R => R.ents.length - 1).sum

theorem callsOf_eq : ∀ (rs : List RoundD), (∀ R ∈ rs, R.ents ≠ []) →
    callsOf rs + rs.length = (entriesOf rs).length
  | [], _ => by simp [callsOf, entriesOf]
  | R :: rs, h => by
    have ih := callsOf_eq rs (fun R' hR' => h R' (List.mem_cons_of_mem _ hR'))
    simp only [callsOf, entriesOf, List.map_cons, List.sum_cons, List.flatMap_cons,
      List.length_append, List.length_map, List.length_cons] at ih ⊢
    have hR := h R List.mem_cons_self
    cases e : R.ents with
    | nil => exact absurd e hR
    | cons _ _ => simp only [List.length_cons]; omega

/-- **Words drawn by the replay**: from stream position `k`, at most `64` per `gen_index` call. -/
theorem simR_draws (n : Nat) (allowed : Array Bool) (reqs : List Req) (key : List Nat) :
    ∀ (rs : List RoundD) (t k : Nat) (st stF : St) (ps : List PM), st.rng = rngAt key k →
      simR n allowed reqs rs t st = some (stF, ps) → ∃ k', stF.rng = rngAt key k' ∧ k' ≤ k + 64 * callsOf rs
  | [], _, k, st, stF, ps, hr, hs => by
    simp only [simR, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    exact ⟨k, hr, by omega⟩
  | R :: rs, t, k, st, stF, ps, hr, hs => by
    simp only [simR] at hs
    split at hs
    · exact absurd hs (by simp)
    · rename_i sh rng hsh
      split at hs
      · exact absurd hs (by simp)
      · rename_i st2 ps2 hrec
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, -⟩ := hs
        rw [hr] at hsh
        obtain ⟨k1, e1, hk1⟩ := shuffle_draws key _ k sh rng hsh
        have hrng : (runL n allowed reqs R.key R.z sh t { st with rng := rng }).1.rng = rngAt key k1 := by
          rw [runL_rng]; exact e1
        obtain ⟨k', e', hk'⟩ := simR_draws n allowed reqs key rs _ k1 _ _ ps2 hrng hrec
        refine ⟨k', e', ?_⟩
        simp only [List.length_map] at hk1
        simp only [callsOf, List.map_cons, List.sum_cons] at hk' ⊢
        rw [Nat.mul_add]
        omega

/-- From `lpState` (`Rng.ofSeed seed`): the final stream position is `≤ 64·(S − Rd)`. -/
theorem lp_draws (ids : List Nat) (p : Params) (allowed : Array Bool) (a0 : Nat → Nat) (seed : NearSpec.Bytes)
    (reqs : List Req) {rs : List RoundD} {t0 : Nat} {stF : St} {ps : List PM}
    (hsim : simR ids.length allowed reqs rs t0 (lpState ids p allowed a0 seed) = some (stF, ps))
    (hne : ∀ R ∈ rs, R.ents ≠ []) :
    ∃ K, stF.rng = rngAt (leWords seed) K ∧ K + 64 * rs.length ≤ 64 * (entriesOf rs).length := by
  obtain ⟨K, e, hK⟩ := simR_draws ids.length allowed reqs (leWords seed) rs t0 0 _ stF ps
    (ofSeed_eq seed) hsim
  refine ⟨K, e, ?_⟩
  have := callsOf_eq rs hne
  rw [← this, Nat.mul_add]
  omega

end ZkFormal.NearV3.Sched
