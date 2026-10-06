import ZkFormal.NearV3.Sched.Link.ProcShuf

/-!
# ZkFormal.NearV3.Sched.Link.ProcStep — the steps of a round (reduction of `hsim`'s pushes)

* `tryGrant_eq`: `try_grant_bandwidth` in closed form (`ok = allowed ∧ inc ≤ sb ∧ inc ≤ rb`, the
  new allowance `a − inc` or `a`);
* `stepSt`: the spec's state before entry `j` of round `i` (along the AIR's shuffled order);
  `runL_iter`, `specPush_eq`: a round's spec re-pushes are the per-entry `stepE` pushes;
* `EntryOk`: what the memory and scan links must give for one entry — the memory in-values are
  the spec state (`sbIn, rbIn, alIn`), the GRANT outcomes (`cS, cR, cL, alOut`) and the `INC`
  values (`inc`, `rem`, `link` of request entry `eout`);
* **`round_push`**: under `EntryOk` for every entry of round `i`, the spec's re-pushes are the
  recorded ones: `specPush … i = recPush … i`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open NearSpecV3 NearSpecV3.Scheduler

/-- **`try_grant_bandwidth` in closed form.** -/
theorem tryGrant_eq (n : Nat) (allowed : Array Bool) (st : St) (l bw : Nat)
    (hl : l < st.allowance.size) :
    (tryGrant n allowed st l bw).1 =
        (allowed[l]! && decide (bw ≤ st.senderBudget[l / n]!) && decide (bw ≤ st.receiverBudget[l % n]!)) ∧
      (tryGrant n allowed st l bw).2.allowance[l]! =
        (if allowed[l]! && decide (bw ≤ st.senderBudget[l / n]!) && decide (bw ≤ st.receiverBudget[l % n]!)
          then st.allowance[l]! - bw else st.allowance[l]!) := by
  unfold tryGrant grantMore
  by_cases ha : allowed[l]! = true
  · simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.true_and]
    by_cases hb : st.senderBudget[l / n]! < bw ∨ st.receiverBudget[l % n]! < bw
    · rw [if_pos hb]
      have : ¬ (bw ≤ st.senderBudget[l / n]! ∧ bw ≤ st.receiverBudget[l % n]!) := by omega
      simp only [Bool.and_eq_true, decide_eq_true_eq] at *
      simp [this]
      intro h; omega
    · rw [if_neg hb]
      have h1 : bw ≤ st.senderBudget[l / n]! := by omega
      have h2 : bw ≤ st.receiverBudget[l % n]! := by omega
      simp only [h1, h2, decide_true, Bool.and_self, ↓reduceIte, true_and]
      simp [Array.set!_eq_setIfInBounds, Array.getD, hl]
  · simp [ha]

section
variable (n : Nat) (allowed : Array Bool) (reqs : List Req)

/-- `runL` along a list given by a function, with the states `S j`. -/
theorem runL_iter (K z t : Nat) (g : Nat → Nat) (S : Nat → St)
    (hS : ∀ j, S (j + 1) = (stepE n allowed reqs K z (t + j) (g j) (S j)).1) :
    ∀ d k, runL n allowed reqs K z ((List.range' k d).map g) (t + k) (S k) =
      (S (k + d), (List.range' k d).flatMap fun j => (stepE n allowed reqs K z (t + j) (g j) (S j)).2)
  | 0, k => by simp [runL]
  | d + 1, k => by
    rw [List.range'_succ, List.map_cons, List.flatMap_cons]
    simp only [runL]
    rw [← hS k, show t + k + 1 = t + (k + 1) by omega, runL_iter K z t g S hS d (k + 1),
      show k + 1 + d = k + (d + 1) by omega]

variable (tr : Trace Fp) (tp f : Nat) (st : St)

/-- The spec's state before entry `j` of round `i`. -/
def stepSt (i : Nat) : Nat → St
  | 0 => { specSt n allowed reqs tr tp f st i with
      rng := rngAt (procKey tr tp f) (cv tr tp (Proc.hdrAt tr tp f i) Proc.kend) }
  | j + 1 => (stepE n allowed reqs (rOf tr tp f i).key (rOf tr tp f i).z
      (cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j)
      (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout) (stepSt i j)).1

theorem specPush_eq (i : Nat) :
    specPush n allowed reqs tr tp f st i =
      (List.range (cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr)).flatMap fun j =>
        (stepE n allowed reqs (rOf tr tp f i).key (rOf tr tp f i).z
          (cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j)
          (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout) (stepSt n allowed reqs tr tp f st i j)).2 := by
  have := runL_iter n allowed reqs (rOf tr tp f i).key (rOf tr tp f i).z
    (cv tr tp (Proc.hdrAt tr tp f i) Proc.T) (fun j => cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout)
    (stepSt n allowed reqs tr tp f st i) (fun j => rfl) (cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr) 0
  simp only [Nat.add_zero, Nat.zero_add] at this
  rw [← List.range_eq_range'] at this
  unfold specPush specRound
  rw [show eoutsOf tr tp f i = (List.range (cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr)).map
    (fun j => cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout) from rfl]
  rw [show ({ specSt n allowed reqs tr tp f st i with
      rng := rngAt (procKey tr tp f) (cv tr tp (Proc.hdrAt tr tp f i) Proc.kend) } : St) =
      stepSt n allowed reqs tr tp f st i 0 from rfl, this]

/-- What the memory and scan links give for entry `j` of round `i` (row `w = h_i + 1 + j`,
spec state `σ = stepSt … i j`). -/
structure EntryOk (i j : Nat) : Prop where
  /-- `INC`: the request entry `eout` has head increase `inc`, more increases iff `rem ≠ 0`,
  link `link` (scan link). -/
  incs : ∃ rest, (reqAt reqs (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout)).incs =
      cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc :: rest ∧
    (rest = [] ↔ cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.rem = 0)
  link : (reqAt reqs (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout)).link =
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link
  eout1 : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout + 1 < 2013265921
  size : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link < (stepSt n allowed reqs tr tp f st i j).allowance.size
  /-- Memory consistency: the in-values are the spec state. -/
  sIn : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.sbIn =
    (stepSt n allowed reqs tr tp f st i j).senderBudget[cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link / n]!
  rIn : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.rbIn =
    (stepSt n allowed reqs tr tp f st i j).receiverBudget[cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link % n]!
  aIn : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.alIn =
    (stepSt n allowed reqs tr tp f st i j).allowance[cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link]!
  /-- GRANT semantics (memory rows, comparator, `INIT` flags). -/
  cS : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.cS =
    if cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc ≤ cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.sbIn
    then 1 else 0
  cR : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.cR =
    if cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc ≤ cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.rbIn
    then 1 else 0
  cL : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.cL =
    if allowed[cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link]! then 1 else 0
  aOut : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.alOut =
    if cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.ok = 1 then
      cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.alIn - cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc
    else cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.alIn

end

theorem filter_map_eq_flatMap {α β : Type} (l : List α) (p : α → Bool) (g : α → β) :
    (l.filter p).map g = l.flatMap fun x => if p x then [g x] else [] := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : p x <;> simp [List.filter_cons, h, ih]

variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp f m : Nat}

/-- **The re-pushes of round `i`** are the spec's, given `EntryOk` for its entries. -/
theorem round_push (hL : Proc.PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) (I : Proc.Inst tr tp f m)
    (n : Nat) (allowed : Array Bool) (reqs : List Req) (st : St) {i : Nat} (hi : i < m)
    (hE : ∀ j, j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr → EntryOk n allowed reqs tr tp f st i j) :
    specPush n allowed reqs tr tp f st i = recPush tr tp f i := by
  rw [specPush_eq, recPush, filter_map_eq_flatMap]
  apply flatMap_congr'
  intro j hj
  have hj' := List.mem_range.1 hj
  obtain ⟨⟨hh0, hh, -⟩, -⟩ := I.hdr i hi
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hok, hlast, hS, hR, hLc⟩ :=
    Proc.ent_msgs hL hH hh0 hh hj'
  have hw' : Proc.hdrAt tr tp f i + 1 + j < tr.height tp := ((Proc.round_shape hL hH hh0 hh).2.2 j hj').1.1
  obtain ⟨-, -, -, hpm, -, -, -, hO⟩ := Proc.entry_row hL hw' ((Proc.round_shape hL hH hh0 hh).2.2 j hj').1.2.1
  have hlf := Proc.bool_of hL hw' (x := Proc.lastf) (by simp [Proc.boolCols])
  have E := hE j hj'
  obtain ⟨rest, hinc, hrest⟩ := E.incs
  have eLink := E.link; have eE1 := E.eout1; have eSz := E.size; have eSIn := E.sIn
  have eRIn := E.rIn; have eAIn := E.aIn; have eCS := E.cS; have eCR := E.cR; have eCL := E.cL
  have eAOut := E.aOut
  clear E
  generalize hw : Proc.hdrAt tr tp f i + 1 + j = w at *
  unfold stepE
  rw [hinc]
  simp only
  rw [eLink]
  have tg := tryGrant_eq n allowed (stepSt n allowed reqs tr tp f st i j) (cv tr tp w Proc.link)
    (cv tr tp w Proc.inc) eSz
  rw [← eSIn, ← eRIn, ← eAIn] at tg
  obtain ⟨t1, t2⟩ := tg
  -- `ok` is the grant decision
  have hokb : (cv tr tp w Proc.ok = 1) ↔
      (tryGrant n allowed (stepSt n allowed reqs tr tp f st i j) (cv tr tp w Proc.link) (cv tr tp w Proc.inc)).1 = true := by
    rw [t1, hok, eCS, eCR, eCL]
    by_cases a : allowed[cv tr tp w Proc.link]! = true <;>
    by_cases b : cv tr tp w Proc.inc ≤ cv tr tp w Proc.sbIn <;>
    by_cases c : cv tr tp w Proc.inc ≤ cv tr tp w Proc.rbIn <;> simp [a, b, c]
  have hal : (tryGrant n allowed (stepSt n allowed reqs tr tp f st i j) (cv tr tp w Proc.link)
      (cv tr tp w Proc.inc)).2.allowance[cv tr tp w Proc.link]! = cv tr tp w Proc.alOut := by
    rw [t2, eAOut]
    by_cases hb : cv tr tp w Proc.ok = 1
    · rw [if_pos hb, if_pos (by rw [← t1]; exact hokb.1 hb)]
    · rw [if_neg hb, if_neg (by rw [← t1]; exact fun h => hb (hokb.2 h))]
  -- `pm = 1` iff granted and more increases
  have hpmb : (cv tr tp w Proc.pm == 1) = true ↔
      ((tryGrant n allowed (stepSt n allowed reqs tr tp f st i j) (cv tr tp w Proc.link) (cv tr tp w Proc.inc)).1 = true ∧
        rest ≠ []) := by
    rw [beq_iff_eq, hpm, ← hokb]
    constructor
    · intro h
      have h1 : cv tr tp w Proc.ok = 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hO with e | e
        · rw [e] at h; simp at h
        · exact e
      refine ⟨h1, fun hr => ?_⟩
      have := hlast.2 (hrest.1 hr)
      rw [h1, this] at h; simp at h
    · rintro ⟨h1, h2⟩
      have h3 : cv tr tp w Proc.lastf = 0 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hlf with e | e
        · exact e
        · exact absurd (hrest.2 (hlast.1 e)) h2
      rw [h1, h3]
  -- the zero-round ordinal
  have hzn : zNext (rOf tr tp f i).key (rOf tr tp f i).z (cv tr tp w Proc.alOut) =
      (if cv tr tp w Proc.alOut = 0 then cv tr tp (Proc.hdrAt tr tp f i) Proc.z + 1 else 0) := by
    have hv := rounds_valid hL hH I (rOf tr tp f i) (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
    unfold RoundD.valid at hv
    simp only [rOf] at hv ⊢
    unfold zNext
    split
    · split
      · rfl
      · rw [hv.elim (fun h => h.2) (fun h => by omega)]
    · rfl
  by_cases hp : (cv tr tp w Proc.pm == 1) = true
  · rw [if_pos (hpmb.1 hp), if_pos hp, hal, hzn, Nat.mod_eq_of_lt eE1]
  · rw [if_neg (fun h => hp (hpmb.2 h)), if_neg hp]

end ZkFormal.NearV3.Sched
