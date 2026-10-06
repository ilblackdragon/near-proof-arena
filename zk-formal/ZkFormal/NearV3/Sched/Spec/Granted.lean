import ZkFormal.NearV3.Sched.Spec.Compose

/-!
# Granted totals are bounded by the shard bandwidth (no `u64::MAX` saturation)

`grantMore` adds with `checked_add`, saturating at `u64Max`; the AIR adds mod `P`. Both agree
because every granted total stays `≤ maxShardBandwidth` (`= 4,500,000` under `Config.pv86`):

* `GInv n M st`: `granted[l] + senderBudget[l / n] ≤ M` for every link `l`;
* it holds after the base grants (`lpState_ginv`), and `tryGrant` / `stepE` / `runL` / `simR`
  preserve it, with `grantMore` never saturating (`tryGrant_granted`);
* every grid grant of link `l` is at most `senderBudget[l / n]` (`gridGrants_le`), so
  `applyGrants` never saturates either and every final total is `≤ M` (`final_granted`).

All of this is derived from the model; nothing about the AIR is assumed here.
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler NearSpec

theorem getElem!_set!_eq {α : Type} [Inhabited α] (a : Array α) (i j : Nat) (v : α) :
    (a.set! i v)[j]! = if i = j ∧ i < a.size then v else a[j]! := by
  by_cases h : i = j
  · subst h; rw [getElem!_set!_self]; by_cases hs : i < a.size <;> simp [hs]
  · rw [getElem!_set!_ne _ _ h]; simp [h]

theorem getElem!_replicate_le (n v j : Nat) : (Array.replicate n v)[j]! ≤ v := by
  by_cases h : j < n
  · simp [getElem!_def, Array.getElem?_replicate, h]
  · simp [getElem!_def, Array.getElem?_replicate, h]

/-- The grant invariant. -/
def GInv (n M : Nat) (st : St) : Prop :=
  ∀ l, st.granted[l]! + st.senderBudget[l / n]! ≤ M

/-- `try_grant_bandwidth` under the invariant: `grantMore` adds without saturating, and the
invariant is preserved. -/
theorem tryGrant_granted {n M : Nat} (hM : M ≤ u64Max) (allowed : Array Bool) {st : St}
    (h : GInv n M st) (l bw : Nat) :
    GInv n M (tryGrant n allowed st l bw).2 ∧
      ((tryGrant n allowed st l bw).1 = true →
        (tryGrant n allowed st l bw).2.granted = st.granted.set! l (st.granted[l]! + bw)) := by
  unfold tryGrant grantMore
  by_cases ha : allowed[l]! = true
  · simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases hb : st.senderBudget[l / n]! < bw ∨ st.receiverBudget[l % n]! < bw
    · rw [if_pos hb]; exact ⟨h, by simp⟩
    · rw [if_neg hb]
      have hl := h l
      have hg : st.granted[l]! + bw ≤ u64Max := by omega
      simp only [hg, ↓reduceIte, true_implies, and_true]
      intro l'
      have hl' := h l'
      have hbS : bw ≤ st.senderBudget[l / n]! := by omega
      rw [getElem!_set!_eq, getElem!_set!_eq]
      by_cases e : l = l'
      · subst e
        by_cases hs : l / n < st.senderBudget.size
        · by_cases hg : l < st.granted.size
          · simp only [hs, hg, and_self, ↓reduceIte]; omega
          · simp only [hs, hg, and_self, and_false, ↓reduceIte]; omega
        · have h0 : st.senderBudget[l / n]! = 0 := getElem!_oob _ (by omega)
          by_cases hg : l < st.granted.size
          · simp only [hs, hg, and_self, and_false, ↓reduceIte]; omega
          · simp only [hs, hg, and_false, ↓reduceIte]; omega
      · rw [if_neg (fun c => e c.1)]
        by_cases hc : l / n = l' / n ∧ l / n < st.senderBudget.size
        · rw [if_pos hc, hc.1]; omega
        · rw [if_neg hc]; exact hl'
  · simp only [ha, Bool.not_false, ↓reduceIte, Bool.false_eq_true, false_implies, and_true]
    exact h

theorem stepE_ginv {n M : Nat} (hM : M ≤ u64Max) (allowed : Array Bool) (reqs : List Req)
    (K z t v : Nat) {st : St} (h : GInv n M st) : GInv n M (stepE n allowed reqs K z t v st).1 := by
  unfold stepE
  split
  · exact h
  · simp only
    split
    · exact (tryGrant_granted hM allowed h _ _).1
    · exact (tryGrant_granted hM allowed h _ _).1

theorem runL_ginv {n M : Nat} (hM : M ≤ u64Max) (allowed : Array Bool) (reqs : List Req)
    (K z : Nat) :
    ∀ (vs : List Nat) (t : Nat) {st : St}, GInv n M st → GInv n M (runL n allowed reqs K z vs t st).1
  | [], _, _, h => h
  | v :: vs, t, _, h => by
    simp only [runL]
    exact runL_ginv hM allowed reqs K z vs (t + 1) (stepE_ginv hM allowed reqs K z t v h)

/-- The invariant holds at every state of the round replay (in particular at `stF`). -/
theorem simR_ginv {n M : Nat} (hM : M ≤ u64Max) (allowed : Array Bool) (reqs : List Req) :
    ∀ (rs : List RoundD) (t : Nat) {st stF : St} {ps : List PM}, GInv n M st →
      simR n allowed reqs rs t st = some (stF, ps) → GInv n M stF
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
        have h' : GInv n M { st with rng := rng } := h
        exact simR_ginv hM allowed reqs rs _ (runL_ginv hM allowed reqs R.key R.z sh t h') hrec

/-- The base-grant fold preserves the invariant. -/
theorem baseFold_ginv {n M : Nat} (hM : M ≤ u64Max) (allowed : Array Bool) (bw : Nat) :
    ∀ (ls : List Nat) {st : St}, GInv n M st →
      GInv n M (ls.foldl (fun st l => (tryGrant n allowed st l bw).2) st)
  | [], _, h => h
  | l :: ls, _, h => by
    simp only [List.foldl_cons]
    exact baseFold_ginv hM allowed bw ls (tryGrant_granted hM allowed h l bw).1

/-- PV 86 fixes the shard bandwidth. -/
theorem pv86_maxShard {n : Nat} {p : Params} (hp : Params.calculate Config.pv86 n = some p) :
    p.maxShardBandwidth = 4500000 := by
  simp [Params.calculate, Config.pv86] at hp
  rw [← hp]

/-- **The invariant holds after the base grants** (`lpState`). -/
theorem lpState_ginv (ids : List Nat) (hn : 1 ≤ ids.length) (p : Params)
    (hp : Params.calculate Config.pv86 ids.length = some p)
    (allowed : Array Bool) (hA : allowed.size = ids.length * ids.length)
    (a0 : Nat → Nat) (seed : Bytes) :
    GInv ids.length p.maxShardBandwidth (lpState ids p allowed a0 seed) := by
  have hM : p.maxShardBandwidth ≤ u64Max := by rw [pv86_maxShard hp]; decide
  have hlp := linkPass_eq hn hp allowed (srcArr ids a0) hA (by simp [srcArr]) (Rng.ofSeed seed)
  have h0 : GInv ids.length p.maxShardBandwidth
      { senderBudget := Array.replicate ids.length p.maxShardBandwidth
        receiverBudget := Array.replicate ids.length p.maxShardBandwidth
        allowance := (srcArr ids a0).map (fun a => Nat.min (Nat.min (a + p.maxShardBandwidth / ids.length) u64Max)
          p.maxAllowance)
        granted := Array.replicate (ids.length * ids.length) 0
        rng := Rng.ofSeed seed } := by
    intro l
    have h1 := getElem!_replicate_le (ids.length * ids.length) 0 l
    have h2 := getElem!_replicate_le ids.length p.maxShardBandwidth (l / ids.length)
    simp only at h1 h2 ⊢
    omega
  have h1 := baseFold_ginv hM allowed p.base (List.range (ids.length * ids.length)) h0
  simp only at hlp
  rw [hlp] at h1
  exact h1

/-! ## The grid grants -/

/-- Every grant written by a grid row is at most the row's starting sender budget. -/
theorem gridRow_le (n : Nat) (allowed : Array Bool) (s B : Nat) (sb : Array Nat)
    (hB : B ≤ sb[s]!) :
    ∀ (rs : List Nat) (se : Endpoint) (ri : Array Endpoint) (g : Array (Option Nat)),
      (∀ r ∈ rs, r < n) → se.2 ≤ B →
      (∀ l, (g[l]!).getD 0 ≤ sb[l / n]!) →
      ∀ l, (((gridRow n allowed s rs se ri g).2.2)[l]!).getD 0 ≤ sb[l / n]!
  | [], _, _, g, _, _, hg => hg
  | r :: rs, se, ri, g, hr, hse, hg => by
    simp only [gridRow]
    split
    · exact gridRow_le n allowed s B sb hB rs se ri g (fun x hx => hr x (List.mem_cons_of_mem _ hx))
        hse hg
    · refine gridRow_le n allowed s B sb hB rs _ _ _ (fun x hx => hr x (List.mem_cons_of_mem _ hx))
        (by simp only; omega) ?_
      intro l
      rw [getElem!_set!_eq]
      split
      · rename_i hc
        have hrn : r < n := hr r List.mem_cons_self
        have hdiv : (s * n + r) / n = s := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hrn]; simp
        rw [← hc.1, hdiv]
        simp only [Option.getD_some]
        have : Nat.min (se.2 / se.1) ((ri[r]!).2 / (ri[r]!).1) ≤ se.2 :=
          Nat.le_trans (Nat.min_le_left _ _) (Nat.div_le_self _ _)
        omega
      · exact hg l

/-- **Every grid grant of link `l` is at most `sb[l / n]`.** -/
theorem gridGrants_le (n : Nat) (allowed : Array Bool) (sb rb : Array Nat) (sord rord : List Nat)
    (hrlt : ∀ x ∈ rord, x < n) (l : Nat) :
    ((gridGrants n allowed sb rb sord rord)[l]!).getD 0 ≤ sb[l / n]! := by
  unfold gridGrants
  simp only
  suffices H : ∀ (ss : List Nat) (acc : Array Endpoint × Array (Option Nat)),
      (∀ l, (acc.2[l]!).getD 0 ≤ sb[l / n]!) →
      ∀ l, (((ss.foldl (fun (acc : Array Endpoint × Array (Option Nat)) s =>
        let (_, ri', g') := gridRow n allowed s rord
          (((List.range n).map fun s => (cntS n allowed s, sb[s]!)).toArray)[s]! acc.1 acc.2
        (ri', g')) acc).2)[l]!).getD 0 ≤ sb[l / n]! by
    apply H
    intro l
    have : ((Array.replicate (n * n) (none : Option Nat))[l]!) = none := by
      by_cases h : l < n * n
      · simp [getElem!_def, Array.getElem?_replicate, h]
      · exact getElem!_oob _ (by simp; omega)
    simp [this]
  intro ss
  induction ss with
  | nil => intro acc h; exact h
  | cons s ss ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    have hse : ((((List.range n).map fun s => (cntS n allowed s, sb[s]!)).toArray)[s]!).2 ≤ sb[s]! := by
      by_cases hs : s < n
      · rw [getElem!_toArray_map_range _ _ hs]; exact Nat.le_refl _
      · rw [getElem!_oob _ (by simp; omega)]; simp [default]
    exact gridRow_le n allowed s _ sb hse rord _ acc.1 acc.2 hrlt (Nat.le_refl _) h

theorem addGrant_eq (o : Option Nat) (old : Nat) (h : old + o.getD 0 ≤ u64Max) :
    addGrant o old = old + o.getD 0 := by
  cases o with
  | none => simp [addGrant]
  | some b => simp only [Option.getD_some] at h; simp [addGrant, h]

/-- **Final grants: `applyGrants` never saturates, and every total is `≤ M`.** -/
theorem final_granted {n M : Nat} (hM : M ≤ u64Max) (allowed : Array Bool) (stF : St)
    (hI : GInv n M stF) (hg : stF.granted.size = n * n) (sord rord : List Nat)
    (hrlt : ∀ x ∈ rord, x < n) (l : Nat) (hl : l < n * n) :
    let g := gridGrants n allowed stF.senderBudget stF.receiverBudget sord rord
    (applyGrants n stF g).granted[l]! = stF.granted[l]! + (g[l]!).getD 0 ∧
      (applyGrants n stF g).granted[l]! ≤ M := by
  intro g
  have hA : (applyGrants n stF g).granted[l]! = addGrant g[l]! stF.granted[l]! := by
    have := (applyGrants_fold stF g (n * n) (by omega)).2.2.2.2.2 l
    simp only [hl, ite_true] at this
    exact this
  have h1 : (g[l]!).getD 0 ≤ stF.senderBudget[l / n]! :=
    gridGrants_le n allowed stF.senderBudget stF.receiverBudget sord rord hrlt l
  have h2 := hI l
  rw [hA]
  rw [addGrant_eq _ _ (by omega)]
  omega

/-- **In `core_compose`'s setting:** every state of the round replay ending in `stF` keeps
`granted[l] + senderBudget[l / n] ≤ 4,500,000`, and each output grant is the *unsaturated*
sum `stF.granted[l] + grid[l]`, itself `≤ 4,500,000` (far below `u64::MAX` and `P`). -/
theorem core_granted (ids : List Nat) (hn : 1 ≤ ids.length) (p : Params)
    (hp : Params.calculate Config.pv86 ids.length = some p)
    (allowed : Array Bool) (hA : allowed.size = ids.length * ids.length)
    (reqs : List Req) (seed : Bytes) (a0 : Nat → Nat)
    (rs : List RoundD) (stF : St) (ps : List PM) (t0 : Nat)
    (hsim : simR ids.length allowed reqs rs t0 (lpState ids p allowed a0 seed) = some (stF, ps)) :
    let n := ids.length
    GInv n 4500000 stF ∧
    ∀ l, l < n * n →
      let g := gridGrants n allowed stF.senderBudget stF.receiverBudget
        (sordOf n allowed stF.senderBudget) (rordOf n allowed stF.receiverBudget)
      (applyGrants n stF g).granted[l]! = stF.granted[l]! + (g[l]!).getD 0 ∧
        (applyGrants n stF g).granted[l]! ≤ 4500000 := by
  intro n
  have hM := pv86_maxShard hp
  have hMu : (4500000 : Nat) ≤ u64Max := by decide
  have h0 := lpState_ginv ids hn p hp allowed hA a0 seed
  rw [hM] at h0
  have hF : GInv n 4500000 stF := simR_ginv hMu allowed reqs rs t0 h0 hsim
  have hsz0 : SzOk ids.length (lpState ids p allowed a0 seed) := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [lpState, linkPass]
  obtain ⟨-, -, hg⟩ := simR_szOk allowed reqs rs t0 hsz0 hsim
  refine ⟨hF, fun l hl => ?_⟩
  exact final_granted hMu allowed stF hF hg _ _
    (fun x hx => (mem_sortByKey_range _ n x).1 hx) l hl

end ZkFormal.NearV3.Sched
