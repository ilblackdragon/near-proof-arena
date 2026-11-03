import WasmBase.Main.SegRowRel
import WasmBase.Main.HostVacuity

/-!
# WasmBase.Main.SegSigma — the segment induction with the host side pinned (E2E M6, σ-thread)

`Main/HostVacuity.lean` shows that a per-row premise quantified over **every** related pre-state
(`RowSpecSeg`, `RowQ`) cannot hold at a continuing HOST row: `RelW` does not see the host-side state
`σ` (`relW_of_vis`), and the host call's result depends on it.  The fix: pin `σ` along the
segment by a **ghost thread**, as the gas segments are pinned by `sg`.

## A generic state invariant `J`, indexed by STATE time

* `RowSpecSegJ X J …` — `RowSpecSeg` restricted to pre-states with `J t s` (`t` the row's STATE
  time), and giving `J (t + 1) s'` for the continuing post-state;
* `RowFactsSegJ`/`RowFactsSegMapJ` — the row facts with that spec (the flat half unchanged);
* `RowQJ X J Q …` — `RowQ` restricted to pre-states with `J t s`;
* **`exec_rowsJ`** — the segment induction (`exec_of_rows_cutQ` + `exec_rows_rel` in one, copied so
  that the old files stay untouched) carrying `J`: from `J (t0 + 1) s0` it concludes the cut case
  with `J (t0 + n + 1) sN`, and the per-row relation with `J (t0 + k + 1) s` at every row.

Unrestricted premises restrict (`RowSpecSeg.toJ`, `RowFactsSeg.toJ` given that the row keeps `J`,
`RowJKeep`; `RowQ.toJ`).

## The σ-thread: `J t s := sideR s = σ t`

`sideR` is the host side with the gas register blanked (`StepSide.sideG`, `Main/StepSide.lean`)
**plus the register file** (NEAR host state that `RelW` does not see either).  With `σ : Nat → St`
indexed by STATE time:
* a non-host instruction row keeps `sideR` (`StepSide.step_sideG`, `StepRegs.step_registers`), so
  it keeps `J` when `σ (t + 1) = σ t` at its time (`SigKeep`, the analogue of `SegKeepM2` for `sg`);
* a HOST row's spec premise is `RowSpecSegJ` with `J = SigJ σ`: only pre-states whose host side is
  `σ t` (and it lands at host side `σ (t + 1)`).  The σ-variants that refuted the unrestricted
  premise are identified (`sigJ_unique`); see `Main/SegSoundSigma.lean` for honest runs.
-/

namespace WasmBase

open ZkFormal.Algebra
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## 1. Restricted row premises -/

/-- **A row's step, restricted to pre-states satisfying `J`** (at the row's STATE time `t`); a
continuing post-state satisfies `J (t + 1)`.  Otherwise as `RowSpecSeg`. -/
def RowSpecSegJ (X : Ctx) (J : Nat → St → Prop) (inS outS : List F) (cons prod : List Msg)
    (sgin sgout : Nat × Nat) : Prop :=
  ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop),
    RelW X E s f tps tpl t pc S live sgin.1 sgin.2 → J t s →
    inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid → (∀ x ∈ cons, live x) →
    t + 1 < ZkFormal.Algebra.P → S + X.maxFee < ZkFormal.Algebra.P → X.g0 < 2 ^ 64 →
    ∃ k' pc' fee hb sb' cid',
      fee ≤ X.maxFee ∧ hb ≤ 2 ∧
      outS = stMsg (X.offOf k' + pc') (t + 1) (S + fee) hb sb' cid' ∧
      (X.R * (S + fee - sgin.1) ≤ sgin.2 →
        (hb = 0 → ∃ s', step X.cfg X.p s = .cont s' ∧
          Rel X s' (t + 1) k' pc' (S + fee) sb' cid' (stepLive live cons prod) sgout.1 sgout.2 ∧
          J (t + 1) s') ∧
        (hb = 1 → ∃ sN, step X.cfg X.p s = .fin sN ∧ sN.frames = [] ∧
          X.R * (S + fee - sgout.1) + sN.gas.g = sgout.2 ∧
          ∃ G : Msg → Prop, (∀ x, G x → x.space ≠ 0 ∧ x.space ≠ 16) ∧
          ∀ x, stepLive live cons prod x ↔ x ∈ stackView sN.stack tps ∨ x ∈ localView 16 f.locals tpl ∨ G x) ∧
        (hb = 2 → ∃ sN e, step X.cfg X.p s = .abort sN e ∧
          X.R * (S + fee - sgout.1) + sN.gas.g = sgout.2))

/-- `RowFactsSeg` with the restricted spec. -/
structure RowFactsSegJ (X : Ctx) (J : Nat → St → Prop) (inS outS : List F) (cons prod : List Msg)
    (sgin sgout : Nat × Nat) : Prop where
  spec : RowSpecSegJ X J inS outS cons prod sgin sgout
  flat : RowFactsFlat X inS outS cons prod

/-- The segments read off the STATE-time thread (as `RowFactsSegMap`). -/
def RowFactsSegMapJ (X : Ctx) (J : Nat → St → Prop) (inS outS : List F) (cons prod : List Msg)
    (seg : Nat → Nat × Nat) : Prop :=
  RowFactsSegJ X J inS outS cons prod (seg (lvl inS).toNat) (seg ((lvl inS).toNat + 1))

/-- **`RowQ` restricted to pre-states satisfying `J`.** -/
def RowQJ (X : Ctx) (J : Nat → St → Prop) (Q : St → (Msg → Prop) → Prop) (inS : List F)
    (cons prod : List Msg) : Prop :=
  ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) (a b : Nat)
    (s' : St), RelW X E s f tps tpl t pc S live a b → J t s → inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
    (∀ x ∈ cons, live x) → step X.cfg X.p s = .cont s' → Q s live → Q s' (stepLive live cons prod)

/-- A row keeps `J`: from a related pre-state with `J t s`, a continuing step lands in `J (t + 1)`. -/
def RowJKeep (X : Ctx) (J : Nat → St → Prop) (inS : List F) : Prop :=
  ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) (a b : Nat)
    (s' : St), RelW X E s f tps tpl t pc S live a b → inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
    t + 1 < ZkFormal.Algebra.P → J t s → step X.cfg X.p s = .cont s' → J (t + 1) s'

theorem RowSpecSeg.toJ {X : Ctx} {J : Nat → St → Prop} {inS outS : List F} {cons prod : List Msg}
    {sgin sgout : Nat × Nat} (h : RowSpecSeg X inS outS cons prod sgin sgout) (hk : RowJKeep X J inS) :
    RowSpecSegJ X J inS outS cons prod sgin sgout := by
  intro E s f tps tpl t pc S live R hJ hin hl h1 h2 h3
  obtain ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, hsp⟩ := h E s f tps tpl t pc S live R hin hl h1 h2 h3
  refine ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, fun hg => ?_⟩
  obtain ⟨c0, c1, c2⟩ := hsp hg
  refine ⟨fun e => ?_, c1, c2⟩
  obtain ⟨s', hs', hR⟩ := c0 e
  exact ⟨s', hs', hR, hk E s f tps tpl t pc S live _ _ s' R hin h1 hJ hs'⟩

theorem RowFactsSeg.toJ {X : Ctx} {J : Nat → St → Prop} {inS outS : List F} {cons prod : List Msg}
    {sgin sgout : Nat × Nat} (h : RowFactsSeg X inS outS cons prod sgin sgout) (hk : RowJKeep X J inS) :
    RowFactsSegJ X J inS outS cons prod sgin sgout :=
  ⟨RowSpecSeg.toJ h.spec hk, h.toFlat⟩

theorem RowQ.toJ {X : Ctx} {J : Nat → St → Prop} {Q : St → (Msg → Prop) → Prop} {inS : List F}
    {cons prod : List Msg} (h : RowQ X Q inS cons prod) : RowQJ X J Q inS cons prod :=
  fun E s f tps tpl t pc S live a b s' R _ hin hl hs hQ => h E s f tps tpl t pc S live a b s' R hin hl hs hQ

theorem rowQJ_and {X : Ctx} {J : Nat → St → Prop} {Q1 Q2 : St → (Msg → Prop) → Prop} {inS : List F}
    {cons prod : List Msg} (h1 : RowQJ X J Q1 inS cons prod) (h2 : RowQJ X J Q2 inS cons prod) :
    RowQJ X J (fun s live => Q1 s live ∧ Q2 s live) inS cons prod :=
  fun E s f tps tpl t pc S live a b s' R hJ hin hl hs hQ =>
    ⟨h1 E s f tps tpl t pc S live a b s' R hJ hin hl hs hQ.1, h2 E s f tps tpl t pc S live a b s' R hJ hin hl hs hQ.2⟩

/-! ## 2. The segment induction carrying `J` -/

section
variable (X : Ctx) {ρ : Type} [DecidableEq ρ] (act : List ρ) (inS outS : ρ → List F)
  (cons prod : ρ → List Msg) (init fin : List Msg) (pcf N Sf : F)

/-- **`exec_rowsJ`: the segment induction with a time-indexed state invariant `J`.**  The hypotheses
of `exec_of_rows_cutQ` with the row premises restricted to `J` (`RowFactsSegMapJ`, `RowQJ`) and
`J (t0 + 1) s0`.  Conclusions: `N = t0 + n + 1`; at a cut, `exec_of_rows_cutQ`'s conclusion plus
`J (t0 + n + 1) sN`; for any status, `exec_rows_rel`'s per-row relation plus `J` at every row. -/
theorem exec_rowsJ (sg : Nat → Nat × Nat) (st : Nat) (hst2 : st ≤ 2) (J : Nat → St → Prop)
    (hrows : ∀ r ∈ act, RowFactsSegMapJ X J (inS r) (outS r) (cons r) (prod r) sg)
    (t0 S0 : Nat) (m0 : List F) (sbf cidf : F)
    (hst : (m0 :: act.map outS).Perm ([pcf, N, Sf, (st : F), sbf, cidf] :: act.map inS))
    (hch : (init ++ act.flatMap prod).Perm (fin ++ act.flatMap cons))
    (hinit : init.Nodup) (hinitTp : ∀ x ∈ init, x.tp ≤ t0)
    (ht : t0 + act.length + 1 + (2 ^ 30 + 2 ^ 16) < ZkFormal.Algebra.P)
    (hfee : S0 + (act.length + 1) * (X.maxFee + 1) < ZkFormal.Algebra.P)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64)
    {s0 : St} (h0 : Bnd X sg s0 t0 S0 m0 init)
    (Q : St → (Msg → Prop) → Prop) (hQ : ∀ r ∈ act, RowQJ X J Q (inS r) (cons r) (prod r))
    (hQ0 : Q s0 (· ∈ init)) (hJ0 : J (t0 + 1) s0) :
    N.toNat = t0 + act.length + 1 ∧
    (st = 0 → ∃ sN, NearSpecV3.Wasm.seg X.cfg X.p act.length s0 = .cont sN ∧
      (∀ m, run X.cfg X.p (act.length + m) s0 = run X.cfg X.p m sN) ∧
      Bnd X sg sN (t0 + act.length) Sf.toNat [pcf, N, Sf, ((0 : Nat) : F), sbf, cidf] fin ∧
      Q sN (· ∈ fin) ∧ J (t0 + act.length + 1) sN) ∧
    (init ++ act.flatMap prod).Nodup ∧
    (∀ r ∈ act, ∀ r' ∈ act, lvl (inS r) = lvl (inS r') → r = r') ∧
    ∀ r ∈ act, ∃ k, k < act.length ∧ ∃ s q pc S sb cid, ∃ live : Msg → Prop,
      inS r = stMsg (X.offOf q + pc) (t0 + k + 1) S 0 sb cid ∧
      NearSpecV3.Wasm.seg X.cfg X.p k s0 = .cont s ∧
      Rel X s (t0 + k + 1) q pc S sb cid live (sg (t0 + k + 1)).1 (sg (t0 + k + 1)).2 ∧
      Q s live ∧ J (t0 + k + 1) s ∧ (∀ x ∈ cons r, live x) := by
  have hP' := P_val
  obtain ⟨k0, pc0, sb0, cid0, rfl, R0⟩ := h0
  have hS0 : S0 < ZkFormal.Algebra.P := by
    have : 1 * 1 ≤ (act.length + 1) * (X.maxFee + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  -- (A) the chain
  let g : ρ → List F × List F := fun r => (inS r, outS r)
  have hE1 : (act.map g).map Prod.snd = act.map outS := by simp [g, List.map_map]
  have hE2 : (act.map g).map Prod.fst = act.map inS := by simp [g, List.map_map]
  have hstepE : ∀ e ∈ act.map g, lvl e.2 = lvl e.1 + 1 := by
    intro e he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    exact (hrows r hr).flat.tsOut
  obtain ⟨es, hes, hpath⟩ := chain (act.map g) (stMsg (X.offOf k0 + pc0) (t0 + 1) S0 0 sb0 cid0)
    [pcf, N, Sf, (st : F), sbf, cidf] lvl (by rw [hE1, hE2]; exact hst) hstepE (by simp; omega)
  obtain ⟨rs, hrs, rfl⟩ := perm_map_lift g es act hes
  have hlenrs : rs.length = act.length := hrs.length_eq
  have hmem : ∀ k (hk : k < rs.length), rs[k] ∈ act := fun k hk => hrs.subset (List.getElem_mem hk)
  obtain ⟨lk, lfin⟩ := path_levels lvl (rs.map g) _ _ hpath (fun e he => hstepE e (hes.subset he))
  obtain ⟨link, ends, enil⟩ := path_link (rs.map g) _ _ hpath
  simp only [List.length_map, List.getElem_map] at lk lfin link ends enil
  have l0 : lvl (stMsg (X.offOf k0 + pc0) (t0 + 1) S0 0 sb0 cid0) = ((t0 + 1 : Nat) : F) := rfl
  have lvlk : ∀ k (hk : k < rs.length), lvl (inS rs[k]) = ((t0 + k + 1 : Nat) : F) := by
    intro k hk; rw [lk k hk, l0, ← Lean.Grind.Semiring.natCast_add, show t0 + 1 + k = t0 + k + 1 by omega]
  have RFS : ∀ k (hk : k < rs.length),
      RowFactsSegJ X J (inS rs[k]) (outS rs[k]) (cons rs[k]) (prod rs[k])
        (sg (t0 + k + 1)) (sg (t0 + k + 1 + 1)) :=
    fun k hk => by
      have e : lvl (inS rs[k]) = ((t0 + k + 1 : Nat) : F) := lvlk k hk
      have h := hrows rs[k] (hmem k hk)
      unfold RowFactsSegMapJ at h
      rwa [e, Fp.toNat_cast_of_lt (by omega)] at h
  have RF : ∀ k (hk : k < rs.length), RowFactsFlat X (inS rs[k]) (outS rs[k]) (cons rs[k]) (prod rs[k]) :=
    fun k hk => (RFS k hk).flat
  have hN : N.toNat = t0 + act.length + 1 := by
    have : N = ((t0 + rs.length + 1 : Nat) : F) := by
      have e : lvl [pcf, N, Sf, (st : F), sbf, cidf] = N := rfl
      rw [← e, lfin, l0, ← Lean.Grind.Semiring.natCast_add, show t0 + 1 + rs.length = t0 + rs.length + 1 by omega]
    rw [this, Fp.toNat_cast_of_lt (by omega), hlenrs]
  -- position messages: `pos k` is the STATE message entering step `k` (the final one at `k = n`)
  let pos : Nat → List F := fun k => if h : k < rs.length then inS rs[k] else [pcf, N, Sf, (st : F), sbf, cidf]
  have pos_in : ∀ k (hk : k < rs.length), pos k = inS rs[k] := fun k hk => by simp [pos, hk]
  have pos_out : ∀ k (hk : k < rs.length), pos (k + 1) = outS rs[k] := by
    intro k hk
    by_cases h1 : k + 1 < rs.length
    · simp only [pos, h1, dite_true]; exact link k h1
    · have : k = rs.length - 1 := by omega
      subst this
      simp only [pos, h1, dite_false]; exact (ends (by omega)).2.symm
  have posN : pos rs.length = [pcf, N, Sf, (st : F), sbf, cidf] := by simp [pos]
  have pos0 : pos 0 = stMsg (X.offOf k0 + pc0) (t0 + 1) S0 0 sb0 cid0 := by
    by_cases h : 0 < rs.length
    · rw [pos_in 0 h]; exact (ends h).1
    · have h' : rs.length = 0 := by omega
      have := posN; rw [h'] at this; rw [this]; exact (enil h').symm
  -- gas units along the path: no wrap-around
  have step1 : ∀ k (hk : k < rs.length), (gasF (pos k)).toNat ≤ S0 + k * X.maxFee →
      ∃ fee, fee ≤ X.maxFee ∧ (gasF (pos (k + 1))).toNat = (gasF (pos k)).toNat + fee := by
    intro k hk hb
    obtain ⟨fee, hfl, hfe⟩ := (RF k hk).gasOut
    refine ⟨fee, hfl, ?_⟩
    rw [pos_out k hk, hfe, ← pos_in k hk]
    conv => lhs; rw [← Fp.cast_toNat (gasF (pos k))]
    rw [← Lean.Grind.Semiring.natCast_add, Fp.toNat_cast_of_lt]
    have : (k + 1) * (X.maxFee + 1) ≤ (act.length + 1) * (X.maxFee + 1) := Nat.mul_le_mul_right _ (by omega)
    have : k * X.maxFee + X.maxFee ≤ (k + 1) * (X.maxFee + 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    omega
  have gasB : ∀ k, k ≤ rs.length → (gasF (pos k)).toNat ≤ S0 + k * X.maxFee := by
    intro k
    induction k with
    | zero =>
      intro _; rw [pos0]
      show (((S0 : Nat) : F)).toNat ≤ _
      rw [Fp.toNat_cast_of_lt hS0]; omega
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      obtain ⟨fee, hfl, he⟩ := step1 k (by omega) ih'
      rw [he, Nat.succ_mul]
      omega
  have gas0 : (gasF (pos 0)).toNat = S0 := by
    rw [pos0]; show (((S0 : Nat) : F)).toNat = _; exact Fp.toNat_cast_of_lt hS0
  have gasN : (gasF (pos rs.length)).toNat = Sf.toNat := by rw [posN]; rfl
  -- (B) the channel, with producer times shifted by `t0`
  let prodL := rs.map prod
  let consL := rs.map cons
  have hpTp : ∀ k (hk : k < rs.length), ∀ x ∈ prod rs[k], x.tp = t0 + k + 1 := by
    intro k hk x hx
    obtain ⟨h1, h2⟩ := (RF k hk).prodT x hx
    rw [lvlk k hk] at h2
    exact natEq h2 h1 (by omega)
  have hpermC : (init ++ prodL.flatten).Perm (fin ++ consL.flatten) := by
    have e1 : prodL.flatten = rs.flatMap prod := by simp [prodL, List.flatMap]
    have e2 : consL.flatten = rs.flatMap cons := by simp [consL, List.flatMap]
    rw [e1, e2]
    exact ((hrs.flatMap_right prod).append_left init).trans (hch.trans
      ((hrs.flatMap_right cons).symm.append_left fin))
  have tpBound : ∀ x ∈ fin ++ consL.flatten, x.tp ≤ t0 + rs.length := by
    intro x hx
    rcases List.mem_append.mp (hpermC.symm.subset hx) with h | h
    · have := hinitTp x h; omega
    · obtain ⟨j, hj, hxj⟩ := mem_flatten_iff.mp h
      simp only [prodL, List.length_map, List.getElem_map] at hj hxj
      rw [hpTp j hj x hxj]; omega
  have C : ChanOK init fin prodL consL (fun x => x.tp - t0) := by
    refine ⟨by simp [prodL, consL], hpermC, ?_, fun x hx => by have := hinitTp x hx; show x.tp - t0 = 0; omega, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hinit, nodup_flatten_of _ (fun j hj => by simpa [prodL] using (RF j (by simpa [prodL] using hj)).prodNd) ?_, ?_⟩
      · intro i j hi hj hij x hx hx'
        simp only [prodL, List.length_map, List.getElem_map] at hi hj hx hx'
        have := hpTp i hi x hx; have := hpTp j hj x hx'; omega
      · intro x hx y hy hxy
        subst hxy
        obtain ⟨j, hj, hxj⟩ := mem_flatten_iff.mp hy
        simp only [prodL, List.length_map, List.getElem_map] at hj hxj
        have := hpTp j hj x hxj; have := hinitTp x hx; omega
    · intro k hk x hx
      simp only [prodL, List.length_map, List.getElem_map] at hk hx
      have := hpTp k hk x hx; show x.tp - t0 = k + 1; omega
    · intro k hk x hx
      simp only [consL, List.length_map, List.getElem_map] at hk hx
      obtain ⟨m, hm, he⟩ := (RF k hk).consT x hx
      rw [lvlk k hk] at he
      have hb := tpBound x (List.mem_append_right _ (mem_flatten_iff.mpr ⟨k, by simpa [consL] using hk, by simpa [consL] using hx⟩))
      have := natEq he (by omega) (by omega)
      show x.tp - t0 < k + 1; omega
  -- (C) induction along the path; the state after `k` rows is related as long as it is not halted
  have IH : ∀ k (hk : k ≤ rs.length), (k < rs.length ∨ st = 0) →
      ∃ s q pc sb cid, NearSpecV3.Wasm.seg X.cfg X.p k s0 = .cont s ∧
      pos k = stMsg (X.offOf q + pc) (t0 + k + 1) (gasF (pos k)).toNat 0 sb cid ∧
      Rel X s (t0 + k + 1) q pc (gasF (pos k)).toNat sb cid (live init prodL consL k)
        (sg (t0 + k + 1)).1 (sg (t0 + k + 1)).2 ∧ Q s (live init prodL consL k) ∧ J (t0 + k + 1) s := by
    intro k
    induction k with
    | zero =>
      intro _ _
      have e0 : (· ∈ init) = live init prodL consL 0 := by funext x; simp [live, prodBefore, consBefore]
      refine ⟨s0, k0, pc0, sb0, cid0, rfl, ?_, ?_, ?_, hJ0⟩
      · rw [gas0, pos0]
      · rw [gas0]
        exact R0.congr_live e0
      · rw [← e0]; exact hQ0
    | succ k ih =>
      intro hk hcase
      obtain ⟨s, q, pc, sb, cid, hrun, hin, ⟨E, f, tps, tpl, rfl, rfl, rfl, R⟩, hQk, hJk⟩ := ih (by omega) (Or.inl (by omega))
      have gb := gasB k (by omega)
      have hm : (k + 1) * (X.maxFee + 1) ≤ (act.length + 1) * (X.maxFee + 1) := Nat.mul_le_mul_right _ (by omega)
      have hS : (gasF (pos k)).toNat + X.maxFee < ZkFormal.Algebra.P := by
        have : k * X.maxFee + X.maxFee ≤ (k + 1) * (X.maxFee + 1) := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
        omega
      have hlive : ∀ x ∈ cons rs[k], live init prodL consL k x := fun x hx =>
        C.consumed_live (k := k) (by simp [consL]; omega) (by simpa [consL] using hx)
      obtain ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, hspec⟩ :=
        (RFS k (by omega)).spec E s f tps tpl (t0 + k + 1) pc _
          (live init prodL consL k) R hJk (by rw [← pos_in k (by omega)]; exact hin) hlive (by omega) hS hg64
      have hout' : pos (k + 1) = stMsg (X.offOf k' + pc') (t0 + k + 1 + 1) ((gasF (pos k)).toNat + fee) hb sb' cid' := by
        rw [pos_out k (by omega), hout]
      have hg1 : (gasF (pos (k + 1))).toNat = (gasF (pos k)).toNat + fee := by
        rw [hout']; simp only [gasF, stMsg, List.getD_cons_succ, List.getD_cons_zero]
        exact Fp.toNat_cast_of_lt (by simp only [gasF] at hS; omega)
      have hgas' : X.R * ((gasF (pos k)).toNat + fee - (sg (t0 + k + 1)).1) ≤ (sg (t0 + k + 1)).2 := by
        have hm := hstepgas (t0 + k + 1) ((gasF (pos k)).toNat) s.gas.g R.gas
        have hle : (gasF (pos k)).toNat + fee - (sg (t0 + k + 1)).1 ≤
            (gasF (pos k)).toNat + X.maxFee - (sg (t0 + k + 1)).1 := by
          have := hfl; omega
        exact Nat.le_trans (Nat.mul_le_mul_left _ hle) hm
      have hb0 : hb = 0 := by
        have h3 : (pos (k + 1)).getD 3 0 = 0 := by
          by_cases hc : k + 1 < rs.length
          · rw [pos_in (k + 1) hc]; exact (RF (k + 1) hc).halt0
          · have : k + 1 = rs.length := by omega
            have hc' : st = 0 := hcase.resolve_left hc
            rw [this, posN, hc']; rfl
        rw [hout'] at h3
        simp only [stMsg, List.getD_cons_succ, List.getD_cons_zero] at h3
        exact natEq (h3.trans rfl) (by omega) (by decide)
      obtain ⟨s', hs', ⟨E', f', tps', tpl', hsb', hcid', hk', R'⟩, hJ'⟩ := (hspec hgas').1 hb0
      have eS : stepLive (live init prodL consL k) (cons rs[k]) (prod rs[k]) = live init prodL consL (k + 1) := by
        funext x
        have := (C.live_succ (k := k) (by simp [consL]; omega) x).symm
        simp only [consL, prodL, List.getElem_map] at this
        exact propext this
      refine ⟨s', k', pc', sb', cid', seg_succ_cont hrun hs', ?_, ?_, ?_, ?_⟩
      · rw [hg1, hout', hb0, show t0 + (k + 1) + 1 = t0 + k + 1 + 1 by omega]
      · rw [hg1, show t0 + (k + 1) + 1 = t0 + k + 1 + 1 by omega, ← hsb', ← hcid', ← hk']
        exact Rel_of_RelW_congr R' eS
      · rw [← eS]
        exact hQ rs[k] (hmem k (by omega)) E s f tps tpl (t0 + k + 1) pc _ (live init prodL consL k) _ _ s' R hJk
          (by rw [← pos_in k (by omega)]; exact hin) hlive hs' hQk
      · rw [show t0 + (k + 1) + 1 = t0 + k + 1 + 1 by omega]; exact hJ'
  have e1 : prodL.flatten = rs.flatMap prod := by simp [prodL, List.flatMap]
  refine ⟨hN, fun h0 => ?_, ((hrs.flatMap_right prod).append_left init).nodup_iff.mp (e1 ▸ C.nodup), ?_, ?_⟩
  -- (D0) a cut: the state after the last row is related to the final boundary
  · obtain ⟨s, q, pc, sb, cid, hrun, hin, R, hQs, hJs⟩ := IH rs.length (Nat.le_refl _) (Or.inr h0)
    rw [hlenrs] at hrun hJs
    have eF : live init prodL consL rs.length = (· ∈ fin) := by
      funext x
      have := C.live_final x
      simp only [consL, List.length_map] at this
      exact propext this
    refine ⟨s, hrun, run_of_seg_cont hrun, ⟨q, pc, sb, cid, ?_, ?_⟩, by rw [← eF]; exact hQs, hJs⟩
    · subst h0; rw [← posN, hin, gasN, hlenrs]
    · rw [← gasN, ← hlenrs]
      refine R.congr_live ?_
      funext x
      have := C.live_final x
      simp only [consL, List.length_map] at this
      exact propext this
  · intro r hr r' hr' hl
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (hrs.symm.subset hr)
    obtain ⟨k', hk', rfl⟩ := List.getElem_of_mem (hrs.symm.subset hr')
    rw [lvlk k hk, lvlk k' hk'] at hl
    have := congrArg Fp.toNat hl
    rw [Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega)] at this
    have : k = k' := by omega
    subst this; rfl
  intro r hr
  obtain ⟨k, hk, hrk⟩ := List.getElem_of_mem (hrs.symm.subset hr)
  obtain ⟨s, q, pc, sb, cid, hrun, hin, R, hQs, hJs⟩ := IH k (by omega) (Or.inl hk)
  refine ⟨k, by omega, s, q, pc, (gasF (pos k)).toNat, sb, cid, live init prodL consL k, ?_, hrun, R, hQs, hJs, ?_⟩
  · rw [← hrk, ← pos_in k hk]; exact hin
  · intro x hx
    rw [← hrk] at hx
    exact C.consumed_live (k := k) (by simp [consL]; omega) (by simpa [consL] using hx)
end

/-! ## 3. The σ-thread -/

/-- **The host side of the σ-thread**: `StepSide.sideG` (every non-Wasm field, gas register blanked)
**plus the register file**.  Registers are NEAR host state (`VMLogic`'s registers; only host
functions write them, `StepRegs.step_registers`), and `RelW` does not see them: without them in
the thread a `read_register`-style call would refute the HOST-row premise exactly as `σ` does in
`Main/HostVacuity.lean`. -/
def sideR (s : St) : St := { StepSide.sideG s with registers := s.registers }

/-- **The σ-thread invariant**: the state at STATE time `t` has host side (registers included, gas
register blanked) `σ t`. -/
def SigJ (σ : Nat → St) : Nat → St → Prop := fun t s => sideR s = σ t

/-- `sideR` determines `sideG`. -/
theorem sideG_of_sideR {s s' : St} (h : sideR s = sideR s') : StepSide.sideG s = StepSide.sideG s' := by
  have := congrArg (fun x : St => { x with registers := #[] }) h
  exact this

/-- **The pinned σ-variants are gone.**  Two states on the thread at the same time with the same
Wasm-visible part and gas register are equal: the pair that refuted `RowSpecSeg`
(`not_rowSpecSeg_of_sigma`) cannot occur among the pre-states `RowSpecSegJ … (SigJ σ)` ranges over. -/
theorem sigJ_unique {σ : Nat → St} {t : Nat} {s s' : St} (h : SigJ σ t s) (h' : SigJ σ t s')
    (hv : HostFoot.vis s = HostFoot.vis s') (hg : s.gas.g = s'.gas.g) : s = s' :=
  StepSide.st_eq_of_sideG hv (sideG_of_sideR (h.trans h'.symm)) hg

/-- The row's instruction is not a host call, at every related state (what `seg_instr_regKeep`
establishes from the FETCH op; `StepRegs.NonHostI`). -/
def CodeNonHost (X : Ctx) (inS : List F) : Prop :=
  ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) (a b : Nat),
    RelW X E s f tps tpl t pc S live a b → inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
    ∀ i, (X.pfOf E.k).code[pc]? = some i → StepRegs.NonHostI X.p i

/-- A non-host row's continuing step keeps the host side and the register file
(`StepSide.step_sideG`, `StepRegs.step_registers`). -/
theorem sideR_keep_of_code {X : Ctx} {inS : List F} (h : CodeNonHost X inS)
    {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop} {a b : Nat}
    {s' : St} (R : RelW X E s f tps tpl t pc S live a b) (hin : inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid)
    (hs : step X.cfg X.p s = .cont s') : sideR s' = sideR s := by
  have hi : ∀ f' fs pf i, s.frames = f' :: fs → X.p.funcs[f'.fn]? = some pf → pf.code[f'.pc]? = some i →
      StepRegs.NonHostI X.p i := by
    intro f' fs pf i hfr hpf hci
    rw [R.frames] at hfr
    obtain ⟨rfl, -⟩ := List.cons.inj hfr
    refine h E s f tps tpl t pc S live a b R hin i ?_
    have e : X.pfOf E.k = pf := by
      unfold Ctx.pfOf; rw [← R.fn, hpf]; rfl
    rw [e, ← R.pcEq]; exact hci
  unfold sideR
  rw [StepSide.step_sideG hs hi, StepRegs.step_registers hs hi]

/-- **A non-host row keeps the σ-thread** when `σ` does not move at its time. -/
theorem rowJKeep_sig {X : Ctx} {inS : List F} {σ : Nat → St} (h : CodeNonHost X inS)
    (hk : σ ((lvl inS).toNat + 1) = σ (lvl inS).toNat) : RowJKeep X (SigJ σ) inS := by
  intro E s f tps tpl t pc S live a b s' R hin ht hJ hs
  have hl : (lvl inS).toNat = t := by
    rw [hin]; show (((t : Nat) : F)).toNat = t; exact Fp.toNat_cast_of_lt (by omega)
  rw [hl] at hk
  show sideR s' = σ (t + 1)
  rw [sideR_keep_of_code h R hin hs, hk]; exact hJ

#print axioms exec_rowsJ
#print axioms sigJ_unique
#print axioms rowJKeep_sig

end WasmBase
