import ZkFormal.NearV3.Sched.Spec.Rounds

/-!
# ZkFormal.NearV3.Sched.Spec.Loop — `processRequests` = the replayed rounds

**`process_rounds`**: if the rounds `rs` recorded by the AIR satisfy
* `simR` replays them to `(stF, ps)` (the shuffles succeed);
* the bucket entries of all rounds are a permutation of all pushes (initial and re-pushes) —
  this is the `PUSH` bus balance;
* `(key, z)` strictly *before* along the list (`before`: keys strictly decrease, then key-0
  rounds with strictly increasing ordinals), every round valid (`z = 0` iff `key > 0`) and
  nonempty;
* each round's entries have strictly increasing time stamps, all below the round's start time
  (`TsOk`; the AIR range-checks this),
then `processRequests n allowed st reqs = some stF`.

Proof: induction over the rounds with the *local* invariant "pending pushes ++ future pushes ~
entries of the remaining rounds"; the round's bucket is the pending group of its key
(`Buckets.groups_pop`), processed by `runL` (`Rounds.processBucket_runL`); fuel by the potential
`Φ = Σ remaining increases`.
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler

/-- Remaining increases of a push. -/
def phi (reqs : List Req) (p : PM) : Nat := (reqAt reqs p.v).incs.length

def phiV (reqs : List Req) (v : Nat) : Nat := (reqAt reqs v).incs.length

/-- Round order. -/
def before (a b : Nat × Nat) : Prop := b.1 < a.1 ∨ (b.1 = 0 ∧ a.1 = 0 ∧ a.2 < b.2)

def RoundD.valid (R : RoundD) : Prop := (0 < R.key ∧ R.z = 0) ∨ (R.key = 0 ∧ 1 ≤ R.z)

/-- Entries of each round: strictly increasing time stamps, all below the round's start. -/
def TsOk : Nat → List RoundD → Prop
  | _, [] => True
  | t, R :: rs => R.ents.Pairwise (fun a b => a.1 < b.1) ∧ (∀ e ∈ R.ents, e.1 < t) ∧
      TsOk (t + R.ents.length) rs

def entsPM (R : RoundD) : List PM := R.ents.map fun e => ⟨R.key, R.z, e.1, e.2⟩

theorem entriesOf_cons (R : RoundD) (rs : List RoundD) :
    entriesOf (R :: rs) = entsPM R ++ entriesOf rs := by
  simp [entriesOf, entsPM]

/-! ## Sorted lists -/

abbrev TsAsc (l : List PM) : Prop := l.Pairwise fun a b => a.ts < b.ts

theorem eq_of_perm_tsAsc : ∀ {l₁ l₂ : List PM}, TsAsc l₁ → TsAsc l₂ → l₁.Perm l₂ → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => absurd h.length_eq (by simp)
  | _ :: _, [], _, _, h => absurd h.length_eq (by simp)
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    have hab : a = b := by
      have ha : a ∈ b :: l₂ := h.subset (List.mem_cons_self ..)
      have hb : b ∈ a :: l₁ := h.symm.subset (List.mem_cons_self ..)
      rcases List.mem_cons.1 ha with e | ha
      · exact e
      rcases List.mem_cons.1 hb with e | hb
      · exact e.symm
      have x1 := List.rel_of_pairwise_cons h₁ hb
      have x2 := List.rel_of_pairwise_cons h₂ ha
      omega
    subst hab
    rw [eq_of_perm_tsAsc h₁.of_cons h₂.of_cons (List.perm_cons a |>.1 h)]

/-! ## `runL` facts -/

section
variable (n : Nat) (allowed : Array Bool) (reqs : List Req)

theorem stepE_facts (hR : ∀ q ∈ reqs, q.incs.length < 64) (K z t v : Nat) (st : St) :
    let r := stepE n allowed reqs K z t v st
    r.1.rng = st.rng ∧ (∀ p ∈ r.2, p.ts = t ∧ p.z = zNext K z p.key ∧ 1 ≤ phi reqs p) ∧
      r.2.length ≤ 1 ∧ (phiV reqs v = 0 → r.2 = []) ∧
      (r.2.map (phi reqs)).sum + 1 ≤ phiV reqs v + (if phiV reqs v = 0 then 1 else 0) := by
  intro r
  unfold r stepE phiV
  split
  · next h => simp [h]
  · next inc rest h =>
    simp only [h, List.length_cons]
    by_cases hok : (tryGrant n allowed st (reqAt reqs v).link inc).1 = true ∧ rest ≠ []
    · rw [if_pos hok]
      have hs := reqAt_succ reqs v hR h hok.2
      have hrl : 1 ≤ rest.length := by
        cases rest with
        | nil => exact absurd rfl hok.2
        | cons _ _ => simp
      refine ⟨tryGrant_rng .., ?_, by simp, by simp, ?_⟩
      · intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        refine ⟨rfl, rfl, ?_⟩
        simp only [phi, hs]; exact hrl
      · simp [phi, hs]
    · rw [if_neg hok]
      refine ⟨tryGrant_rng .., by simp, by simp, by simp, by simp⟩

theorem runL_facts (hR : ∀ q ∈ reqs, q.incs.length < 64) (K z : Nat) :
    ∀ (vs : List Nat) (t : Nat) (st : St),
      let r := runL n allowed reqs K z vs t st
      r.1.rng = st.rng ∧
      (∀ p ∈ r.2, t ≤ p.ts ∧ p.ts < t + vs.length ∧ p.z = zNext K z p.key ∧ 1 ≤ phi reqs p) ∧
      TsAsc r.2 ∧
      ((∀ v ∈ vs, 1 ≤ phiV reqs v) → (r.2.map (phi reqs)).sum + vs.length ≤ (vs.map (phiV reqs)).sum)
  | [], t, st => by simp [runL]
  | v :: vs, t, st => by
    intro r
    obtain ⟨e1, e2, e3, e4, e5⟩ := stepE_facts n allowed reqs hR K z t v st
    obtain ⟨f1, f2, f3, f4⟩ := runL_facts hR K z vs (t + 1) (stepE n allowed reqs K z t v st).1
    refine ⟨by simp only [r, runL]; rw [f1, e1], ?_, ?_, ?_⟩
    · intro p hp
      simp only [r, runL, List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨a, b, c⟩ := e2 p hp; simp only [List.length_cons]; omega
      · obtain ⟨a, b, c, d⟩ := f2 p hp; simp only [List.length_cons]; omega
    · simp only [r, runL]
      refine List.pairwise_append.2 ⟨?_, f3, fun a ha b hb => ?_⟩
      · cases h : (stepE n allowed reqs K z t v st).2 with
        | nil => simp
        | cons x xs =>
          have hl := e3; rw [h] at hl
          cases xs with
          | nil => simp
          | cons _ _ => simp at hl
      · have := (e2 a ha).1; have := (f2 b hb).1; omega
    · intro hv
      have h1 := hv v (List.mem_cons_self ..)
      have h2 := f4 (fun w hw => hv w (List.mem_cons_of_mem _ hw))
      have h3 := e5
      rw [if_neg (by omega)] at h3
      simp only [r, runL, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        List.length_cons]
      omega

theorem simR_ts (hR : ∀ q ∈ reqs, q.incs.length < 64) :
    ∀ (rs : List RoundD) (t : Nat) (st stF : St) (ps : List PM),
    simR n allowed reqs rs t st = some (stF, ps) → ∀ p ∈ ps, t ≤ p.ts
  | [], _, _, _, _, h => by simp [simR] at h; obtain ⟨-, rfl⟩ := h; simp
  | R :: rs, t, st, stF, ps, h => by
    unfold simR at h
    split at h
    · cases h
    · next sh rng hsh =>
      dsimp only at h
      split at h
      · cases h
      · next st2 ps2 h2 =>
        cases h
        have hlen := length_shuffle hsh
        simp only [List.length_map] at hlen
        intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact ((runL_facts n allowed reqs hR R.key R.z sh t _).2.1 p hp).1
        · have := simR_ts hR rs _ _ _ _ h2 p hp; omega

end

/-! ## Permutations -/

theorem perm_sum_map {α : Type} (f : α → Nat) {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    (l₁.map f).sum = (l₂.map f).sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp; omega
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem swapAt_perm {α : Type} [DecidableEq α] (l : List α) (i j : Nat) : (swapAt l i j).Perm l := by
  unfold swapAt
  cases hi : l[i]? with
  | none => exact List.Perm.refl _
  | some a =>
    cases hj : l[j]? with
    | none => exact List.Perm.refl _
    | some b =>
      simp only
      obtain ⟨hil, hia⟩ := List.getElem?_eq_some_iff.1 hi
      obtain ⟨hjl, hjb⟩ := List.getElem?_eq_some_iff.1 hj
      rw [List.perm_iff_count]
      intro x
      have hjl' : j < (l.set i b).length := by simpa using hjl
      rw [List.count_set hjl', List.count_set hil]
      have hsj : (l.set i b)[j] = b := by
        rw [List.getElem_set]; split
        · rfl
        · exact hjb
      rw [hsj, hia]
      have ha : (a == x) = true → 1 ≤ List.count x l := by
        intro h
        have : x = a := (beq_iff_eq.1 h).symm
        subst this
        exact List.count_pos_iff.2 (hia ▸ List.getElem_mem hil)
      by_cases h1 : (a == x) = true <;> by_cases h2 : (b == x) = true <;> simp [h1, h2] <;>
        have := ha <;> simp_all <;> omega

theorem shuffleLoop_perm {α : Type} [DecidableEq α] :
    ∀ (i : Nat) (l : List α) (r : Rng) (l' : List α) (r' : Rng),
      shuffleLoop i l r = some (l', r') → l'.Perm l
  | 0, l, r, l', r', h => by simp [shuffleLoop] at h; rw [← h.1]
  | i + 1, l, r, l', r', h => by
    unfold shuffleLoop at h
    cases hg : genIndex 64 (i + 2) r with
    | none => rw [hg] at h; cases h
    | some p =>
      rw [hg] at h
      exact (shuffleLoop_perm i _ _ l' r' h).trans (swapAt_perm _ _ _)

theorem shuffle_perm {α : Type} [DecidableEq α] {l l' : List α} {r r' : Rng}
    (h : shuffle l r = some (l', r')) : l'.Perm l := shuffleLoop_perm _ _ _ _ _ h

/-! ## The loop -/

section
variable (n : Nat) (allowed : Array Bool) (reqs : List Req)

/-- Pushes before `t`, all others are future ones. -/
structure Inv (suf : List RoundD) (t : Nat) (pend fut : List PM) : Prop where
  perm : (entriesOf suf).Perm (pend ++ fut)
  asc : TsAsc pend
  past : ∀ p ∈ pend, p.ts < t
  future : ∀ p ∈ fut, t ≤ p.ts
  phi : ∀ p ∈ pend, 1 ≤ phi reqs p
  zinit : ∀ p ∈ pend, p.key = 0 → ∀ R ∈ suf, R.key = 0 → p.z ≤ R.z
  ord : suf.Pairwise fun R R' => before (R.key, R.z) (R'.key, R'.z)
  valid : ∀ R ∈ suf, R.valid
  ne : ∀ R ∈ suf, R.ents ≠ []
  ts : TsOk t suf

theorem mem_entriesOf {suf : List RoundD} {p : PM} (h : p ∈ entriesOf suf) :
    ∃ R ∈ suf, p.key = R.key ∧ p.z = R.z ∧ (p.ts, p.v) ∈ R.ents := by
  simp only [entriesOf, List.mem_flatMap, List.mem_map] at h
  obtain ⟨R, hR, e, he, rfl⟩ := h
  exact ⟨R, hR, rfl, rfl, he⟩

theorem loop (hR : ∀ q ∈ reqs, q.incs.length < 64) :
    ∀ (suf : List RoundD) (t : Nat) (st stF : St) (pend fut : List PM) (fuel : Nat),
      simR n allowed reqs suf t st = some (stF, fut) → Inv reqs suf t pend fut →
      (pend.map (phi reqs)).sum ≤ fuel →
      processLoop n allowed fuel st (bucketsOf reqs pend) = some stF
  | [], t, st, stF, pend, fut, fuel, hs, I, _ => by
    simp only [simR, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    have : pend = [] := by
      have := I.perm.length_eq; simp [entriesOf] at this; exact List.eq_nil_of_length_eq_zero (by omega)
    subst this
    cases fuel <;> rfl
  | R :: suf, t, st, stF, pend, fut, fuel, hs, I, hf => by
    -- unfold the replay of the first round
    unfold simR at hs
    split at hs
    · cases hs
    next sh rng hsh =>
    dsimp only at hs
    split at hs
    · cases hs
    next stF' fut2 hs2 =>
    cases hs
    generalize ha : runL n allowed reqs R.key R.z sh t { st with rng := rng } = a at hs2 I
    have hlen : sh.length = R.ents.length := by
      have := length_shuffle hsh; simpa using this
    obtain ⟨ar, af, aasc, aphi⟩ := ha ▸ runL_facts n allowed reqs hR R.key R.z sh t { st with rng := rng }
    have hfut2 := simR_ts n allowed reqs hR suf _ _ _ _ hs2
    have hpermE := I.perm
    rw [entriesOf_cons] at hpermE
    have hEts : ∀ e ∈ R.ents, e.1 < t := I.ts.2.1
    have hEasc : R.ents.Pairwise (fun a b => a.1 < b.1) := I.ts.1
    -- rounds after `R` have another `(key, z)`
    have hordR : ∀ R' ∈ suf, before (R.key, R.z) (R'.key, R'.z) :=
      fun R' h => List.rel_of_pairwise_cons I.ord h
    have htagne : ∀ R' ∈ suf, ¬ (R'.key = R.key ∧ R'.z = R.z) := by
      intro R' hR' ⟨h1, h2⟩
      have := hordR R' hR'; unfold before at this; simp only at this; omega
    -- every pending push belongs to some remaining round
    have hround : ∀ p ∈ pend, ∃ R'' ∈ R :: suf, p.key = R''.key ∧ p.z = R''.z := by
      intro p hp
      have : p ∈ entriesOf (R :: suf) := I.perm.symm.subset (List.mem_append_left _ hp)
      obtain ⟨R'', h1, h2, h3, -⟩ := mem_entriesOf this
      exact ⟨R'', h1, h2, h3⟩
    -- the pending pushes with the round's key are exactly its tag
    have hz : ∀ p ∈ pend, p.key = R.key → p.z = R.z := by
      intro p hp hk
      obtain ⟨R'', h1, h2, h3⟩ := hround p hp
      rcases List.mem_cons.1 h1 with rfl | h1
      · exact h3
      · have hb := hordR R'' h1
        unfold before at hb; simp only at hb
        rcases hb with hb | ⟨hb1, hb2, hb3⟩
        · omega
        · have := I.zinit p hp (by omega) R (List.mem_cons_self ..) hb2
          omega
    -- the bucket is the pending group of `R.key`
    let E := entsPM R
    have hEeq : E = pend.filter fun p => p.key = R.key := by
      have hp1 := hpermE.filter (fun p => p.key == R.key && p.z == R.z)
      have e1 : (E ++ entriesOf suf).filter (fun p => p.key == R.key && p.z == R.z) = E := by
        rw [List.filter_append]
        have : E.filter (fun p => p.key == R.key && p.z == R.z) = E := by
          rw [List.filter_eq_self]; intro x hx
          simp only [E, entsPM, List.mem_map] at hx
          obtain ⟨e, -, rfl⟩ := hx; simp
        rw [this, List.filter_eq_nil_iff.2, List.append_nil]
        intro x hx hx'
        obtain ⟨R', h1, h2, h3, -⟩ := mem_entriesOf hx
        simp only [Bool.and_eq_true, beq_iff_eq] at hx'
        exact htagne R' h1 ⟨h2 ▸ hx'.1, h3 ▸ hx'.2⟩
      have e2 : (pend ++ (a.2 ++ fut2)).filter (fun p => p.key == R.key && p.z == R.z) =
          pend.filter (fun p => p.key = R.key) := by
        rw [List.filter_append]
        have : (a.2 ++ fut2).filter (fun p => p.key == R.key && p.z == R.z) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx hx'
          have hxE : x ∈ E := by
            have : x ∈ (E ++ entriesOf suf).filter (fun p => p.key == R.key && p.z == R.z) := by
              rw [hp1.mem_iff]; exact List.mem_filter.2 ⟨List.mem_append_right _ hx, hx'⟩
            rwa [e1] at this
          simp only [E, entsPM, List.mem_map] at hxE
          obtain ⟨e, he, rfl⟩ := hxE
          have h1 := hEts e he
          have h2 : t ≤ e.1 := by
            rcases List.mem_append.1 hx with hx | hx
            · exact (af _ hx).1
            · have := hfut2 _ hx; simp only at this; omega
          omega
        rw [this, List.append_nil]
        apply List.filter_congr
        intro p hp
        by_cases hk : p.key = R.key
        · simp [hk, hz p hp hk]
        · simp [hk]
      rw [e1, e2] at hp1
      refine eq_of_perm_tsAsc ?_ ((I.asc).sublist List.filter_sublist) hp1
      simp only [E, entsPM, TsAsc, List.pairwise_map]
      exact hEasc
    have hEne : E ≠ [] := by simpa [E, entsPM] using I.ne R (List.mem_cons_self ..)
    have hmax : ∀ p ∈ pend, p.key ≤ R.key := by
      intro p hp
      obtain ⟨R'', h1, h2, -⟩ := hround p hp
      rcases List.mem_cons.1 h1 with rfl | h1
      · omega
      · have hb := hordR R'' h1; unfold before at hb; simp only at hb; omega
    have hpres : ∃ p ∈ pend, p.key = R.key := by
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil E hEne
      rw [hEeq] at hx
      exact ⟨x, (List.mem_filter.1 hx).1, by simpa using (List.mem_filter.1 hx).2⟩
    obtain ⟨hlast, hdrop⟩ := groups_pop reqs pend R.key hpres hmax
    -- potentials
    have hphiE : ∀ v ∈ R.ents.map Prod.snd, 1 ≤ phiV reqs v := by
      intro v hv
      simp only [List.mem_map] at hv
      obtain ⟨e, he, rfl⟩ := hv
      have : (⟨R.key, R.z, e.1, e.2⟩ : PM) ∈ pend := by
        have : (⟨R.key, R.z, e.1, e.2⟩ : PM) ∈ E := by
          simp only [E, entsPM, List.mem_map]; exact ⟨e, he, rfl⟩
        rw [hEeq] at this; exact (List.mem_filter.1 this).1
      exact I.phi _ this
    have hshP := shuffle_perm hsh
    have hphiSh : ∀ v ∈ sh, 1 ≤ phiV reqs v := fun v hv => hphiE v (hshP.subset hv)
    have hsumSh : (sh.map (phiV reqs)).sum = ((pend.filter fun p => p.key = R.key).map (phi reqs)).sum := by
      rw [perm_sum_map _ hshP, ← hEeq]
      simp [E, entsPM, phi, phiV, Function.comp_def]
    have hsplit := perm_sum_map (phi reqs) (List.filter_append_perm (fun p => decide (p.key = R.key)) pend)
    simp only [List.map_append, List.sum_append] at hsplit
    have hfilt : (pend.filter fun p => !decide (p.key = R.key)) = pend.filter fun p => p.key ≠ R.key := by
      apply List.filter_congr; intro p _; simp
    rw [hfilt] at hsplit
    have hshne : 1 ≤ sh.length := by
      rw [hlen]; cases h : R.ents with
      | nil => exact absurd h (I.ne R (List.mem_cons_self ..))
      | cons _ _ => simp
    have hphiA := aphi hphiSh
    -- the spec's step
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hbk : bucketsOf reqs pend ≠ [] := by
      rw [bucketsOf_eq_groups]; unfold groupsOf
      obtain ⟨p, hp, hk⟩ := hpres
      have : R.key ∈ keysOf pend := (mem_keysOf pend R.key).2 ⟨p, hp, hk⟩
      intro h; rw [List.map_eq_nil_iff] at h; rw [h] at this; cases this
    obtain ⟨b0, bs, hb⟩ := List.exists_cons_of_ne_nil hbk
    rw [hb]
    unfold processLoop
    rw [← hb, bucketsOf_eq_groups, hlast]
    simp only
    have hqs : grp reqs pend R.key = (R.ents.map Prod.snd).map (reqAt reqs) := by
      unfold grp; rw [← hEeq]; simp [E, entsPM, Function.comp_def]
    rw [hqs, shuffle_map, hsh]
    simp only [Option.map_some]
    rw [hdrop, ← bucketsOf_eq_groups, processBucket_runL n allowed reqs hR R.key R.z sh t, ha]
    refine loop hR suf (t + R.ents.length) a.1 stF _ fut2 f hs2 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
    · -- perm
      have h1 : pend.Perm (E ++ pend.filter fun p => p.key ≠ R.key) := by
        have := List.filter_append_perm (fun p => decide (p.key = R.key)) pend
        rw [hfilt, ← hEeq] at this; exact this.symm
      have h2 : (E ++ entriesOf suf).Perm (E ++ ((pend.filter fun p => p.key ≠ R.key) ++ a.2 ++ fut2)) := by
        refine hpermE.trans ((h1.append_right (a.2 ++ fut2)).trans (List.Perm.of_eq ?_))
        simp only [List.append_assoc]
      exact (List.perm_append_left_iff E).1 h2
    · -- ascending
      refine List.pairwise_append.2 ⟨(I.asc).sublist List.filter_sublist, aasc, ?_⟩
      intro x hx y hy
      have := I.past x (List.mem_filter.1 hx).1
      have := (af y hy).1
      omega
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · have := I.past p (List.mem_filter.1 hp).1; omega
      · have := (af p hp).2.1; omega
    · exact hfut2
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact I.phi p (List.mem_filter.1 hp).1
      · exact (af p hp).2.2.2
    · intro p hp hk R' hR' hk'
      rcases List.mem_append.1 hp with hp | hp
      · exact I.zinit p (List.mem_filter.1 hp).1 hk R' (List.mem_cons_of_mem _ hR') hk'
      · rw [(af p hp).2.2.1, hk]
        unfold zNext
        simp only [ite_true]
        have hv := I.valid R' (List.mem_cons_of_mem _ hR')
        unfold RoundD.valid at hv
        split
        · next hK0 =>
          have hb := hordR R' hR'; unfold before at hb; simp only at hb; omega
        · omega
    · exact I.ord.of_cons
    · exact fun R' h => I.valid R' (List.mem_cons_of_mem _ h)
    · exact fun R' h => I.ne R' (List.mem_cons_of_mem _ h)
    · exact I.ts.2.2
    · -- fuel
      simp only [List.map_append, List.sum_append]
      omega

end

section
variable (n : Nat) (allowed : Array Bool) (reqs : List Req)

theorem map_getD_range {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem reqAt_init (reqs : List Req) (i : Nat) : reqAt reqs (i * 64) = reqs.getD i ⟨0, []⟩ := by
  unfold reqAt
  simp only [Nat.mul_mod_left, List.drop_zero, Nat.mul_div_cancel _ (by decide : 0 < 64)]

/-- The spec's initial bucket map is the map of the initial pushes. -/
theorem init_buckets (reqs : List Req) (st : St) :
    reqs.foldl (fun bk q => bucketPush st.allowance[q.link]! q bk) [] =
      bucketsOf reqs (initPushes reqs st) := by
  unfold bucketsOf initPushes
  rw [List.foldl_map]
  conv => lhs; rw [← map_getD_range reqs ⟨0, []⟩]
  rw [List.foldl_map]
  congr 1
  funext bk i
  rw [reqAt_init]

/-- **`process_bandwidth_requests` from the AIR's rounds.** -/
theorem process_rounds (hR : ∀ q ∈ reqs, q.incs ≠ [] ∧ q.incs.length < 64)
    (rs : List RoundD) (st stF : St) (ps : List PM) (t0 : Nat) (ht0 : reqs.length ≤ t0)
    (hsim : simR n allowed reqs rs t0 st = some (stF, ps))
    (hperm : (entriesOf rs).Perm (initPushes reqs st ++ ps))
    (hord : rs.Pairwise fun R R' => before (R.key, R.z) (R'.key, R'.z))
    (hval : ∀ R ∈ rs, R.valid) (hne : ∀ R ∈ rs, R.ents ≠ []) (hts : TsOk t0 rs) :
    processRequests n allowed st reqs = some stF := by
  have hR' : ∀ q ∈ reqs, q.incs.length < 64 := fun q h => (hR q h).2
  unfold processRequests
  simp only
  rw [init_buckets]
  have hphi : ∀ i, i < reqs.length → phi reqs ⟨st.allowance[(reqs.getD i ⟨0, []⟩).link]!,
      zNext 1 0 st.allowance[(reqs.getD i ⟨0, []⟩).link]!, i, i * 64⟩ = (reqs.getD i ⟨0, []⟩).incs.length := by
    intro i _; simp only [phi, reqAt_init]
  refine loop n allowed reqs hR' rs t0 st stF _ ps _ hsim ⟨hperm, ?_, ?_,
    simR_ts n allowed reqs hR' rs _ _ _ _ hsim, ?_, ?_, hord, hval, hne, hts⟩ ?_
  · simp only [TsAsc, initPushes, List.pairwise_map]
    exact List.pairwise_lt_range
  · intro p hp
    simp only [initPushes, List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp; exact Nat.lt_of_lt_of_le hi ht0
  · intro p hp
    simp only [initPushes, List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    rw [hphi i hi]
    have hq : reqs.getD i ⟨0, []⟩ ∈ reqs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi
    have := (hR _ hq).1
    cases h : (reqs.getD i ⟨0, []⟩).incs with
    | nil => exact absurd h this
    | cons _ _ => simp
  · intro p hp hk R' hR'm hk'
    simp only [initPushes, List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    simp only at hk ⊢
    have hv := hval R' hR'm
    unfold RoundD.valid at hv
    rw [hk]; simp [zNext]; omega
  · have : ((initPushes reqs st).map (phi reqs)).sum = (reqs.map (·.incs.length)).sum := by
      unfold initPushes
      rw [List.map_map]
      conv => rhs; rw [← map_getD_range reqs ⟨0, []⟩]
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hphi i (List.mem_range.1 hi)
    rw [this]; omega

end

end ZkFormal.NearV3.Sched
