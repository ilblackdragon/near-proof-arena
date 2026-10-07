import ZkFormal.NearV3.Sched.Spec.Granted
import ZkFormal.NearV3.Sched.Spec.Conv

/-!
# ZkFormal.NearV3.Sched.Spec.Steps — the step budget of `process_bandwidth_requests` (M4)

Lane `v3-sched`. The number of processing steps (bucket entries, = `sprV3` entry rows) of the
replay `simR` is bounded by the converted requests plus a per-sender budget:

* `incsOf_ge`: every increase of a converted request is `≥ m = ⌊D/40⌋`, `D = maxSingleGrant − base`
  (the first increase is measured from `base`, later ones between two set-bit values; the
  values are `base + ⌊D·(c+1)/40⌋` and `⌊x + D⌋/40 ≥ ⌊x/40⌋ + ⌊D/40⌋`). The bound is exact: a
  bitmap with bit 0 set has first increase `⌊D/40⌋`. No parameter hypothesis is needed.
* `simR_phi`: with the potential `Φ = Σ_{s<n} ⌊senderBudget[s] / m⌋`, every re-push of the replay
  comes from a successful grant, which lowers some `senderBudget[s]` (`s = l / n < n`) by
  `inc ≥ m`, hence `Φ` by `≥ 1`; a failed grant (or a last increase) pushes nothing and lowers
  nothing. So `Φ(stF) + |pushes| ≤ Φ(st)`.
* `steps_budget`: with the `PUSH` balance (`entries ~ initial pushes ++ re-pushes`), the number
  of entries is `≤ |reqs| + n·⌊M/m⌋` when every sender budget is `≤ M`; `rounds_le_entries`:
  rounds are nonempty, so `Rd ≤ S`.
* `pv86_kappa`: under `Config.pv86`, `m ≥ 102,357` (`base ≤ 100,000`) and `M = 4,500,000`, so
  `⌊M/m⌋ ≤ 43` (`= 43` at `base = 100,000`, i.e. `n ≤ 4`).
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler

/-! ## The minimum increase -/

theorem requestValues_getD (p : Params) {c : Nat} (hc : c < 40) :
    (requestValues p).getD c 0 = p.base + (p.maxSingleGrant - p.base) * (c + 1) / 40 := by
  simp [requestValues, List.getD_eq_getElem?_getD, hc]

theorem incsFrom_ge (p : Params) :
    ∀ (cs : List Nat) (k : Nat), cs.Pairwise (· < ·) → (∀ c ∈ cs, k ≤ c ∧ c < 40) →
      ∀ x ∈ incsFrom (requestValues p) (p.base + (p.maxSingleGrant - p.base) * k / 40) cs,
        (p.maxSingleGrant - p.base) / 40 ≤ x
  | [], _, _, _, x, hx => by simp [incsFrom] at hx
  | c :: cs, k, hp, hb, x, hx => by
    rw [List.pairwise_cons] at hp
    obtain ⟨hkc, hc40⟩ := hb c List.mem_cons_self
    simp only [incsFrom, List.mem_cons] at hx
    rw [requestValues_getD p hc40] at hx
    rcases hx with hx | hx
    · subst hx
      generalize p.maxSingleGrant - p.base = D
      have : D * k + D ≤ D * (c + 1) := by
        rw [Nat.mul_succ]; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hkc) _
      omega
    · exact incsFrom_ge p cs (c + 1) hp.2
        (fun c' h => ⟨hp.1 c' h, (hb c' (List.mem_cons_of_mem _ h)).2⟩) x hx

/-- **Every increase is `≥ ⌊(maxSingleGrant − base)/40⌋`.** -/
theorem incsOf_ge (p : Params) (bm : List UInt8) :
    ∀ x ∈ incsOf p bm, (p.maxSingleGrant - p.base) / 40 ≤ x := by
  have h := incsFrom_ge p (setBits bm) 0 (List.pairwise_lt_range.filter _)
    (fun c hc => ⟨Nat.zero_le _, List.mem_range.1 (List.mem_filter.1 hc).1⟩)
  have e : p.base + (p.maxSingleGrant - p.base) * 0 / 40 = p.base := by simp
  rw [e] at h
  exact h

theorem convRaw_ge (p : Params) (n : Nat) (raw : List RawReq) :
    ∀ q ∈ convRaw p n raw, ∀ x ∈ q.incs, (p.maxSingleGrant - p.base) / 40 ≤ x := by
  intro q hq x hx
  simp only [convRaw, List.mem_filterMap] at hq
  obtain ⟨r, -, hr⟩ := hq
  cases h : incsOf p r.bm with
  | nil => simp [h] at hr
  | cons a t =>
    simp only [h, Option.some.injEq] at hr
    subst hr
    exact incsOf_ge p r.bm x (h ▸ hx)

theorem reqAt_ge {m : Nat} {reqs : List Req} (hinc : ∀ q ∈ reqs, ∀ x ∈ q.incs, m ≤ x) (v : Nat) :
    ∀ x ∈ (reqAt reqs v).incs, m ≤ x := by
  intro x hx
  unfold reqAt at hx
  have hx' := List.mem_of_mem_drop hx
  rw [List.getD_eq_getElem?_getD] at hx'
  cases h : reqs[v / 64]? with
  | none => simp [h] at hx'
  | some q =>
    simp only [h, Option.getD_some] at hx'
    exact hinc q (List.mem_of_getElem? h) x hx'

/-! ## The potential -/

/-- `Φ = Σ_{s<n} ⌊senderBudget[s] / m⌋`. -/
def phiB (m n : Nat) (st : St) : Nat := ((List.range n).map fun s => st.senderBudget[s]! / m).sum

theorem sum_range_le (f g : Nat → Nat) :
    ∀ n, (∀ i, i < n → g i ≤ f i) → ((List.range n).map g).sum ≤ ((List.range n).map f).sum
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    have := sum_range_le f g n (fun i hi => h i (by omega))
    have := h n (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem sum_range_lt (f g : Nat → Nat) {s : Nat} (hlt : g s < f s) :
    ∀ n, s < n → (∀ i, i < n → g i ≤ f i) →
      ((List.range n).map g).sum + 1 ≤ ((List.range n).map f).sum
  | 0, hs, _ => absurd hs (by omega)
  | n + 1, hs, h => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    by_cases e : s = n
    · subst e
      have := sum_range_le f g s (fun i hi => h i (by omega))
      omega
    · have := sum_range_lt f g hlt n (by omega) (fun i hi => h i (by omega))
      have := h n (by omega)
      omega

theorem sum_range_const (g : Nat → Nat) (c : Nat) :
    ∀ n, (∀ i, i < n → g i ≤ c) → ((List.range n).map g).sum ≤ n * c
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have := sum_range_const g c n (fun i hi => h i (by omega))
    have := h n (by omega)
    rw [Nat.succ_mul]; omega

theorem div_sub_lt {a b m : Nat} (hm : 0 < m) (hb : m ≤ b) (ha : b ≤ a) : (a - b) / m + 1 ≤ a / m := by
  rw [← Nat.add_div_right _ hm]
  exact Nat.div_le_div_right (by omega)

/-- A grant lowers `Φ` by one if it succeeds and never raises it. -/
theorem tryGrant_phi {m n : Nat} (hm : 0 < m) (allowed : Array Bool) (hA : allowed.size = n * n)
    (st : St) (hS : st.senderBudget.size = n) (l bw : Nat) (hbw : m ≤ bw) :
    phiB m n (tryGrant n allowed st l bw).2 + (if (tryGrant n allowed st l bw).1 then 1 else 0) ≤
      phiB m n st := by
  unfold tryGrant grantMore
  by_cases ha : allowed[l]! = true
  · simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases hb : st.senderBudget[l / n]! < bw ∨ st.receiverBudget[l % n]! < bw
    · rw [if_pos hb]; simp
    · rw [if_neg hb]
      simp only [↓reduceIte]
      have hl : l < n * n := by
        rw [← hA]
        rcases Nat.lt_or_ge l allowed.size with hc | hc
        · exact hc
        · rw [getElem!_def, getElem?_neg allowed l (by omega)] at ha
          cases ha
      have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp at hl
        · exact h
      have hs : l / n < n := (Nat.div_lt_iff_lt_mul hn).2 hl
      unfold phiB
      refine sum_range_lt _ _ ?_ n hs ?_
      · simp only [getElem!_set!_eq, hS, hs, and_self, ↓reduceIte]
        exact div_sub_lt hm hbw (by omega)
      · intro i _
        simp only [getElem!_set!_eq]
        split
        · next h => rw [← h.1]; exact Nat.div_le_div_right (Nat.sub_le _ _)
        · exact Nat.le_refl _
  · have ha' : allowed[l]! = false := by simpa using ha
    simp only [ha', Bool.not_false, ↓reduceIte, Bool.false_eq_true]
    simp

section

variable {m n : Nat} (hm : 0 < m) (allowed : Array Bool) (hA : allowed.size = n * n)
  (reqs : List Req) (hinc : ∀ q ∈ reqs, ∀ x ∈ q.incs, m ≤ x)

include hm hA hinc

theorem stepE_phi (K z t v : Nat) (st : St) (hS : SzOk n st) :
    phiB m n (stepE n allowed reqs K z t v st).1 + (stepE n allowed reqs K z t v st).2.length ≤
      phiB m n st := by
  unfold stepE
  split
  · simp
  · next inc rest h =>
    have hi : m ≤ inc := reqAt_ge hinc v inc (by rw [h]; exact List.mem_cons_self)
    have T := tryGrant_phi hm allowed hA st hS.1 (reqAt reqs v).link inc hi
    simp only
    split
    · next hok => simp only [hok.1, ↓reduceIte] at T; simp only [List.length_singleton]; exact T
    · simp only [List.length_nil, Nat.add_zero]; split at T <;> omega

theorem runL_phi (K z : Nat) :
    ∀ (vs : List Nat) (t : Nat) (st : St), SzOk n st →
      phiB m n (runL n allowed reqs K z vs t st).1 + (runL n allowed reqs K z vs t st).2.length ≤
        phiB m n st
  | [], _, _, _ => by simp [runL]
  | v :: vs, t, st, hS => by
    simp only [runL, List.length_append]
    have h1 := stepE_phi hm allowed hA reqs hinc K z t v st hS
    have h2 := runL_phi K z vs (t + 1) _ (stepE_szOk allowed reqs K z t v hS)
    omega

/-- **The replay pays one unit of `Φ` per re-push.** -/
theorem simR_phi :
    ∀ (rs : List RoundD) (t : Nat) (st stF : St) (ps : List PM), SzOk n st →
      simR n allowed reqs rs t st = some (stF, ps) → phiB m n stF + ps.length ≤ phiB m n st
  | [], _, _, _, _, _, hs => by
    simp only [simR, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    simp
  | R :: rs, t, st, stF, ps, hS, hs => by
    simp only [simR] at hs
    split at hs
    · exact absurd hs (by simp)
    · rename_i sh rng _
      split at hs
      · exact absurd hs (by simp)
      · rename_i st2 ps2 hrec
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        have hS' : SzOk n { st with rng := rng } := hS
        have h1 := runL_phi hm allowed hA reqs hinc R.key R.z sh t _ hS'
        have h2 := simR_phi rs _ _ _ _ (runL_szOk allowed reqs R.key R.z sh t hS') hrec
        have e : phiB m n { st with rng := rng } = phiB m n st := rfl
        rw [List.length_append]
        omega

omit hm hA hinc in
theorem phiB_le {M : Nat} (st : St) (h : ∀ s, s < n → st.senderBudget[s]! ≤ M) :
    phiB m n st ≤ n * (M / m) :=
  sum_range_const _ _ n fun i hi => Nat.div_le_div_right (h i hi)

omit hm hA hinc in
theorem initPushes_length (st : St) : (initPushes reqs st).length = reqs.length := by
  simp [initPushes]

/-- **The step budget.** With the `PUSH` balance, the entries (steps) of the replayed rounds
number at most `|reqs| + n·⌊M/m⌋`, `M` a bound on every initial sender budget. -/
theorem steps_budget {M : Nat} {st stF : St} (hS : SzOk n st) (hM : ∀ s, s < n → st.senderBudget[s]! ≤ M)
    {rs : List RoundD} {t0 : Nat} {ps : List PM}
    (hsim : simR n allowed reqs rs t0 st = some (stF, ps))
    (hperm : (entriesOf rs).Perm (initPushes reqs st ++ ps)) :
    (entriesOf rs).length ≤ reqs.length + n * (M / m) := by
  have h1 := simR_phi hm allowed hA reqs hinc rs t0 st stF ps hS hsim
  have h2 := phiB_le (m := m) st hM
  rw [hperm.length_eq, List.length_append, initPushes_length]
  omega

end

/-- Rounds are nonempty, so there are at most as many rounds as entries. -/
theorem rounds_le_entries : ∀ (rs : List RoundD), (∀ R ∈ rs, R.ents ≠ []) → rs.length ≤ (entriesOf rs).length
  | [], _ => by simp
  | R :: rs, h => by
    have ih := rounds_le_entries rs (fun R' hR' => h R' (List.mem_cons_of_mem _ hR'))
    simp only [entriesOf, List.flatMap_cons, List.length_append, List.length_map, List.length_cons] at ih ⊢
    have hR := h R List.mem_cons_self
    cases e : R.ents with
    | nil => exact absurd e hR
    | cons _ _ => simp only [List.length_cons]; omega

/-! ## The link-pass state and PV 86 -/

theorem lpState_sb_le (ids : List Nat) (p : Params) (allowed : Array Bool) (a0 : Nat → Nat) (seed : NearSpec.Bytes)
    (s : Nat) : (lpState ids p allowed a0 seed).senderBudget[s]! ≤ p.maxShardBandwidth := by
  simp only [lpState, linkPass, getElem!_def, Array.getElem?_map]
  split
  · next h =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨c, -, rfl⟩ := h
    exact Nat.sub_le _ _
  · exact Nat.zero_le _

theorem lpState_szOk (ids : List Nat) (p : Params) (allowed : Array Bool) (a0 : Nat → Nat) (seed : NearSpec.Bytes) :
    SzOk ids.length (lpState ids p allowed a0 seed) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [lpState, linkPass]

/-- Under `Config.pv86`: `m = ⌊(maxSingleGrant − base)/40⌋ ≥ 102,357` and `⌊M/m⌋ ≤ 43`. -/
theorem pv86_kappa {n : Nat} {p : Params} (hp : Params.calculate Config.pv86 n = some p) :
    102357 ≤ (p.maxSingleGrant - p.base) / 40 ∧
      p.maxShardBandwidth / ((p.maxSingleGrant - p.base) / 40) ≤ 43 := by
  rw [pv86_calc hp]
  simp only
  have hb : Nat.min (305696 / Nat.max 1 (n - 1)) 100000 ≤ 100000 := Nat.min_le_right _ _
  generalize Nat.min (305696 / Nat.max 1 (n - 1)) 100000 = b at hb
  have hm : 102357 ≤ (4194304 - b) / 40 := by omega
  refine ⟨hm, ?_⟩
  calc 4500000 / ((4194304 - b) / 40) ≤ 4500000 / 102357 := Nat.div_le_div_left hm (by decide)
    _ = 43 := by decide

/-- The PV 86 step budget of one instance: entries `≤ |reqs| + 43·n`, rounds `≤` entries. -/
theorem steps_pv86 (ids : List Nat) (p : Params) (hp : Params.calculate Config.pv86 ids.length = some p)
    (allowed : Array Bool) (hA : allowed.size = ids.length * ids.length) (raw : List RawReq)
    (a0 : Nat → Nat) (seed : NearSpec.Bytes) {rs : List RoundD} {t0 : Nat} {stF : St} {ps : List PM}
    (hsim : simR ids.length allowed (convRaw p ids.length raw) rs t0 (lpState ids p allowed a0 seed) =
      some (stF, ps))
    (hperm : (entriesOf rs).Perm (initPushes (convRaw p ids.length raw) (lpState ids p allowed a0 seed) ++ ps))
    (hne : ∀ R ∈ rs, R.ents ≠ []) :
    rs.length ≤ (entriesOf rs).length ∧
      (entriesOf rs).length ≤ (convRaw p ids.length raw).length + 43 * ids.length := by
  obtain ⟨hm, hk⟩ := pv86_kappa hp
  refine ⟨rounds_le_entries rs hne, ?_⟩
  have := steps_budget (by omega) allowed hA _ (convRaw_ge p ids.length raw)
    (lpState_szOk ids p allowed a0 seed) (fun s _ => lpState_sb_le ids p allowed a0 seed s) hsim hperm
  have : ids.length * (p.maxShardBandwidth / ((p.maxSingleGrant - p.base) / 40)) ≤ ids.length * 43 :=
    Nat.mul_le_mul_left _ hk
  rw [Nat.mul_comm 43]
  omega

end ZkFormal.NearV3.Sched
