import ZkFormal.NearV3.Sched.Spec.Canon
import ZkFormal.NearV3.Sched.Spec.CanonDup
import ZkFormal.NearV3.Sched.Spec.LinkPass
import ZkFormal.NearV3.Sched.Spec.Loop
import ZkFormal.NearV3.Sched.Spec.Dist

/-!
# ZkFormal.NearV3.Sched.Spec.Compose — the scheduler core as the composition of the AIR's phases (M1)

Lane `v3-sched`. `coreOf` (= `runCore`, by `runCore_eq`) on a canonical previous state equals:

1. read the previous state canonically (`decode_encode`, `allow0_src`): `allow0 = srcArr ids a0` (first-index `indexOf`, any layout);
2. the link pass in closed form (`linkPass_eq`): state `lpState`;
3. the process phase as the AIR's replayed rounds (`process_rounds`): state `stF`;
4. distribute as the AIR's grid (`distribute_eq_grid`, `applyGrants_allowance`).

Hypothesis added beyond the phase lemmas: `hn64 : ids.length ≤ 64` (the borsh `u32` link count
`n * n < 2^32` of the previous state; nearcore layouts have at most 64 shards anyway).
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler NearSpec

/-- The canonical link list of a layout with allowances `a`. -/
def canonLinks (ids : List Nat) (a : Nat → Nat) : List NearSpec.Bandwidth.LinkAllowance :=
  (List.range (ids.length * ids.length)).map fun l =>
    ⟨ids.getD (l / ids.length) 0, ids.getD (l % ids.length) 0, a l⟩

/-- Canonical previous state: absent (`a0 = 0`, initial hash), or the canonical links with
allowances `a0 < 2^64` and a 32-byte hash `h0`. -/
def PrevCanon (ids : List Nat) (prev : Option Bytes) (a0 : Nat → Nat) (h0 : Bytes) : Prop :=
  (prev = none ∧ (∀ l, a0 l = 0) ∧ h0 = NearSpec.Bandwidth.State.initial.sanityHash) ∨
  (prev = some (NearSpec.Bandwidth.State.encode ⟨canonLinks ids a0, h0⟩) ∧ h0.length = 32 ∧
    ∀ l, a0 l < 2 ^ 64)

/-- The previous allowances as an array. -/
def a0Arr (n : Nat) (a0 : Nat → Nat) : Array Nat := (List.range (n * n)).toArray.map a0

/-- The state after the link pass (closed form) with the seeded generator; the previous
allowances are read through the layout's source map (`Spec/CanonDup.srcArr`, first-index
`indexOf` semantics, any layout). -/
def lpState (ids : List Nat) (p : Params) (allowed : Array Bool) (a0 : Nat → Nat) (seed : Bytes) : St :=
  let lp := linkPass ids.length p allowed (srcArr ids a0)
  ⟨lp.sb, lp.rb, lp.a2, lp.g2, Rng.ofSeed seed⟩

/-! ## Array sizes through the process phase -/

/-- Sizes of the budget / grant arrays. -/
def SzOk (n : Nat) (st : St) : Prop :=
  st.senderBudget.size = n ∧ st.receiverBudget.size = n ∧ st.granted.size = n * n

theorem tryGrant_szOk {n : Nat} (allowed : Array Bool) {st : St} (l bw : Nat) (h : SzOk n st) :
    SzOk n (tryGrant n allowed st l bw).2 := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold tryGrant grantMore
  split
  · exact ⟨h1, h2, h3⟩
  · simp only
    split
    · exact ⟨h1, h2, h3⟩
    · refine ⟨?_, ?_, ?_⟩ <;> simp [Array.set!_eq_setIfInBounds, h1, h2, h3]

theorem stepE_szOk {n : Nat} (allowed : Array Bool) (reqs : List Req) (K z t v : Nat) {st : St}
    (h : SzOk n st) : SzOk n (stepE n allowed reqs K z t v st).1 := by
  unfold stepE
  split
  · exact h
  · simp only
    split
    · exact tryGrant_szOk allowed _ _ h
    · exact tryGrant_szOk allowed _ _ h

theorem runL_szOk {n : Nat} (allowed : Array Bool) (reqs : List Req) (K z : Nat) :
    ∀ (vs : List Nat) (t : Nat) {st : St}, SzOk n st → SzOk n (runL n allowed reqs K z vs t st).1
  | [], _, _, h => h
  | v :: vs, t, _, h => by
    simp only [runL]
    exact runL_szOk allowed reqs K z vs (t + 1) (stepE_szOk allowed reqs K z t v h)

theorem simR_szOk {n : Nat} (allowed : Array Bool) (reqs : List Req) :
    ∀ (rs : List RoundD) (t : Nat) {st stF : St} {ps : List PM}, SzOk n st →
      simR n allowed reqs rs t st = some (stF, ps) → SzOk n stF
  | [], _, _, _, _, h, hs => by
    simp only [simR, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    exact h
  | R :: rs, t, st, stF, ps, h, hs => by
    simp only [simR] at hs
    split at hs
    · exact absurd hs (by simp)
    · rename_i sh rng _
      split at hs
      · exact absurd hs (by simp)
      · rename_i st2 ps2 hrec
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, -⟩ := hs
        have h' : SzOk n { st with rng := rng } := h
        exact simR_szOk allowed reqs rs _ (runL_szOk allowed reqs R.key R.z sh t h') hrec

/-! ## The composition -/

theorem core_compose (ids : List Nat) (hn : 1 ≤ ids.length) (hn64 : ids.length ≤ 64)
    (hids : ∀ x ∈ ids, x < 2 ^ 64)
    (p : Params) (hp : Params.calculate Config.pv86 ids.length = some p)
    (allowed : Array Bool) (hA : allowed.size = ids.length * ids.length)
    (reqs : List Req) (seed ash : Bytes)
    (prev : Option Bytes) (a0 : Nat → Nat) (h0 : Bytes) (hprev : PrevCanon ids prev a0 h0)
    (hR : ∀ q ∈ reqs, q.incs ≠ [] ∧ q.incs.length < 64)
    (rs : List RoundD) (stF : St) (ps : List PM) (t0 : Nat) (ht0 : reqs.length ≤ t0)
    (hsim : simR ids.length allowed reqs rs t0 (lpState ids p allowed a0 seed) =
      some (stF, ps))
    (hperm : (entriesOf rs).Perm (initPushes reqs (lpState ids p allowed a0 seed) ++ ps))
    (hord : rs.Pairwise fun R R' => before (R.key, R.z) (R'.key, R'.z))
    (hval : ∀ R ∈ rs, R.valid) (hne : ∀ R ∈ rs, R.ents ≠ []) (hts : TsOk t0 rs) :
    let n := ids.length
    coreOf ids p allowed reqs seed ash prev = some
      ⟨NearSpec.Bandwidth.State.encode
          ⟨canonLinks ids (fun l => stF.allowance[l]!), sha256 (h0 ++ ash)⟩,
        (List.range (n * n)).map (fun l => ((ids.getD (l / n) 0, ids.getD (l % n) 0),
          (applyGrants n stF (gridGrants n allowed stF.senderBudget stF.receiverBudget
            (sordOf n allowed stF.senderBudget)
            (rordOf n allowed stF.receiverBudget))).granted[l]!)),
        p⟩ := by
  intro n
  simp only [n]
  -- the phases
  have hpr : processRequests ids.length allowed
      { senderBudget := (linkPass ids.length p allowed (srcArr ids a0)).sb,
        receiverBudget := (linkPass ids.length p allowed (srcArr ids a0)).rb,
        allowance := (linkPass ids.length p allowed (srcArr ids a0)).a2,
        granted := (linkPass ids.length p allowed (srcArr ids a0)).g2,
        rng := Rng.ofSeed seed } reqs = some stF :=
    process_rounds ids.length allowed reqs hR rs _ stF ps t0 ht0 hsim hperm hord hval hne hts
  have hsz0 : SzOk ids.length (lpState ids p allowed a0 seed) := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [lpState, linkPass]
  obtain ⟨hsb, hrb, hg⟩ := simR_szOk allowed reqs rs t0 hsz0 hsim
  have hdist := distribute_eq_grid ids.length allowed stF hsb hrb hA
  have hal : (distribute ids.length allowed stF).allowance = stF.allowance := by
    rw [hdist]; exact applyGrants_allowance ids.length stF _ hg
  have hlp := linkPass_eq hn hp allowed (srcArr ids a0) hA (by simp [srcArr])
    (Rng.ofSeed seed)
  simp only at hlp
  rcases hprev with ⟨rfl, ha, rfl⟩ | ⟨rfl, hh, ha⟩
  · unfold coreOf
    simp only [Option.bind_some, bind]
    generalize hF : List.foldl _ (Array.replicate _ 0) NearSpec.Bandwidth.State.initial.links = F
    have hFa : F = srcArr ids a0 := by
      rw [← hF]
      apply Array.ext
      · simp [srcArr, NearSpec.Bandwidth.State.initial]
      · intro i h1 h2
        simp only [srcArr, NearSpec.Bandwidth.State.initial, List.foldl_nil, Array.getElem_replicate,
          Array.getElem_map, List.getElem_toArray]
        split <;> simp [ha]
    subst hFa
    rw [hlp, hpr]
    simp only [Option.bind_some]
    rw [hal, hdist]
    rfl
  · unfold coreOf
    simp only []
    rw [decode_encode _ ?_ hh ?_]
    · simp only [Option.bind_some, bind]
      generalize hF : List.foldl _ (Array.replicate _ 0) (canonLinks ids a0) = F
      have hFa : F = srcArr ids a0 := by
        rw [← hF]; exact allow0_src ids a0
      subst hFa
      rw [hlp, hpr]
      simp only [Option.bind_some]
      rw [hal, hdist]
      rfl
    · intro la hla
      simp only [canonLinks, List.mem_map, List.mem_range] at hla
      obtain ⟨l, hl, rfl⟩ := hla
      have hpos : 0 < ids.length := hn
      have hs : l / ids.length < ids.length := (Nat.div_lt_iff_lt_mul hpos).2 hl
      have hr : l % ids.length < ids.length := Nat.mod_lt _ hpos
      have e1 : ids.getD (l / ids.length) 0 = ids[l / ids.length] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]; rfl
      have e2 : ids.getD (l % ids.length) 0 = ids[l % ids.length] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]; rfl
      refine ⟨?_, ?_, ha l⟩
      · show ids.getD (l / ids.length) 0 < 2 ^ 64
        rw [e1]; exact hids _ (List.getElem_mem hs)
      · show ids.getD (l % ids.length) 0 < 2 ^ 64
        rw [e2]; exact hids _ (List.getElem_mem hr)
    · simp only [canonLinks, List.length_map, List.length_range]
      have := Nat.mul_le_mul hn64 hn64
      omega

end ZkFormal.NearV3.Sched
