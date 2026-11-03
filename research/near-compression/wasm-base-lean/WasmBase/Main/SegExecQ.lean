import WasmBase.Main.SegSigma
import WasmBase.Main.SegGrowStep
import WasmBase.Main.SegGrow
import WasmBase.Main.SegMemFrame

/-!
# WasmBase.Main.SegExecQ — the segment induction with the invariant handed to the row spec (E2E M6, GROW)

`exec_rowsJ` (`Main/SegSigma.lean`) carries a state/live-set invariant `Q` along the segment
(`RowQJ`: every row keeps it), but a row's spec premise (`RowSpecSegJ`) only sees `RelW` and `J`.
A `memory.grow` / `memory.size` row's step depends on the page count, which `RelW` does not tie to
the space-8 size message the row consumes: the **size clause** `SzC` (`Main/SegGrowStep.lean`) is a
`Q`-invariant, and the row spec needs it.  Here:

* `RowSpecSegJQ X J Q mf` — `RowSpecSegJ` whose pre-states also satisfy `Q s live`, with a fee bound
  `mf` in place of `X.maxFee` (MEMG charges `fee + lin · n`, the linear fee of `memory.grow`);
* `RowFactsFlatM mf`, `RowFactsSegJQ`, `RowFactsSegMapJQ` — the row facts with that spec and bound;
* `RowFactsSegJ.toJQ` — every existing row (`RowFactsSegMapJ`, fee `≤ X.maxFee ≤ mf`) is one;
* **`exec_rowsJQ`** — `exec_rowsJ` (one copied induction) with these rows: from `Q s0` and
  `J (t0 + 1) s0` it concludes the cut case with `Q sN (· ∈ fin)` and `J (t0 + n + 1) sN`;
* the size clause at the boundaries (§3): `szC_init` (SEGG's production is the in-block's only
  space-8 message), `szC_fin`, and for `wasmBaseSegAirG` `segg_size_dec` / **`segg_size_track`**:
  with `nblk_in = 64·pin`, `nblk_out = 64·pout` (public), `SzC` holds at `s0` when `s0` has `pin`
  pages, and `SzC` at the cut gives `nblk_out = 64 · sN.pages.size`.

With `Q := … ∧ SzC`, a MEMG row's spec premise is discharged by `step_memSize` / `step_memGrow_ok` /
`step_memGrow_fail` (`Main/SegGrowStep.lean`) once the row's trace decoding and its code record are
available (open: the `checkModuleM3` context, see `Main/SegGrowStep.lean`'s header).
-/

namespace WasmBase

open ZkFormal.Algebra
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## 1. Row premises with `Q` and a fee bound -/

/-- `RowSpecSegJ` with the pre-state also satisfying `Q s live`, and fee bound `mf`. -/
def RowSpecSegJQ (X : Ctx) (J : Nat → St → Prop) (Q : St → (Msg → Prop) → Prop) (mf : Nat)
    (inS outS : List F) (cons prod : List Msg) (sgin sgout : Nat × Nat) : Prop :=
  ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop),
    RelW X E s f tps tpl t pc S live sgin.1 sgin.2 → J t s → Q s live →
    inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid → (∀ x ∈ cons, live x) →
    t + 1 < ZkFormal.Algebra.P → S + mf < ZkFormal.Algebra.P → X.g0 < 2 ^ 64 →
    ∃ k' pc' fee hb sb' cid',
      fee ≤ mf ∧ hb ≤ 2 ∧
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

/-- `RowFactsFlat` with the fee bound `mf`. -/
structure RowFactsFlatM (mf : Nat) (inS outS : List F) (cons prod : List Msg) : Prop where
  halt0 : inS.getD 3 0 = 0
  tsOut : lvl outS = lvl inS + 1
  gasOut : ∃ fee, fee ≤ mf ∧ gasF outS = gasF inS + (fee : F)
  consT : ∀ x ∈ cons, ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((x.tp + 1 + n : Nat) : F) = lvl inS
  prodT : ∀ x ∈ prod, x.tp < ZkFormal.Algebra.P ∧ ((x.tp : Nat) : F) = lvl inS
  prodNd : prod.Nodup

/-- The row facts with the `Q`-aware spec. -/
structure RowFactsSegJQ (X : Ctx) (J : Nat → St → Prop) (Q : St → (Msg → Prop) → Prop) (mf : Nat)
    (inS outS : List F) (cons prod : List Msg) (sgin sgout : Nat × Nat) : Prop where
  spec : RowSpecSegJQ X J Q mf inS outS cons prod sgin sgout
  flat : RowFactsFlatM mf inS outS cons prod

/-- The segments read off the STATE-time thread. -/
def RowFactsSegMapJQ (X : Ctx) (J : Nat → St → Prop) (Q : St → (Msg → Prop) → Prop) (mf : Nat)
    (inS outS : List F) (cons prod : List Msg) (seg : Nat → Nat × Nat) : Prop :=
  RowFactsSegJQ X J Q mf inS outS cons prod (seg (lvl inS).toNat) (seg ((lvl inS).toNat + 1))

theorem RowFactsFlat.toM {X : Ctx} {mf : Nat} (hmf : X.maxFee ≤ mf) {inS outS : List F} {cons prod : List Msg}
    (h : RowFactsFlat X inS outS cons prod) : RowFactsFlatM mf inS outS cons prod := by
  obtain ⟨fee, hf, he⟩ := h.gasOut
  exact ⟨h.halt0, h.tsOut, ⟨fee, by omega, he⟩, h.consT, h.prodT, h.prodNd⟩

/-- **Every existing row is a `Q`-aware row** (the spec ignores `Q`; `X.maxFee ≤ mf`). -/
theorem RowFactsSegJ.toJQ {X : Ctx} {J : Nat → St → Prop} {Q : St → (Msg → Prop) → Prop} {mf : Nat}
    (hmf : X.maxFee ≤ mf) {inS outS : List F} {cons prod : List Msg} {sgin sgout : Nat × Nat}
    (h : RowFactsSegJ X J inS outS cons prod sgin sgout) : RowFactsSegJQ X J Q mf inS outS cons prod sgin sgout := by
  refine ⟨fun E s f tps tpl t pc S live R hJ _ hin hl h1 h2 h3 => ?_, h.flat.toM hmf⟩
  obtain ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, hsp⟩ := h.spec E s f tps tpl t pc S live R hJ hin hl h1 (by omega) h3
  exact ⟨k', pc', fee, hb, sb', cid', by omega, hbl, hout, hsp⟩

theorem RowFactsSegMapJ.toJQ {X : Ctx} {J : Nat → St → Prop} {Q : St → (Msg → Prop) → Prop} {mf : Nat}
    (hmf : X.maxFee ≤ mf) {inS outS : List F} {cons prod : List Msg} {sg : Nat → Nat × Nat}
    (h : RowFactsSegMapJ X J inS outS cons prod sg) : RowFactsSegMapJQ X J Q mf inS outS cons prod sg :=
  RowFactsSegJ.toJQ hmf h

/-- **`RowQJ` with the gas of one step available** (`R · (S + mf − a) ≤ b`, what `hstepgas` gives at
every row): a row whose step lemma needs its charge to succeed (MEMG) can then compute its step. -/
def RowQJM (X : Ctx) (J : Nat → St → Prop) (Q : St → (Msg → Prop) → Prop) (mf : Nat) (inS : List F)
    (cons prod : List Msg) : Prop :=
  ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) (a b : Nat)
    (s' : St), RelW X E s f tps tpl t pc S live a b → X.R * (S + mf - a) ≤ b → J t s →
    inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
    (∀ x ∈ cons, live x) → step X.cfg X.p s = .cont s' → Q s live → Q s' (stepLive live cons prod)

theorem RowQJ.toM {X : Ctx} {J : Nat → St → Prop} {Q : St → (Msg → Prop) → Prop} {mf : Nat} {inS : List F}
    {cons prod : List Msg} (h : RowQJ X J Q inS cons prod) : RowQJM X J Q mf inS cons prod :=
  fun E s f tps tpl t pc S live a b s' R _ hJ hin hl hs hQ => h E s f tps tpl t pc S live a b s' R hJ hin hl hs hQ

theorem rowQJM_and {X : Ctx} {J : Nat → St → Prop} {Q1 Q2 : St → (Msg → Prop) → Prop} {mf : Nat} {inS : List F}
    {cons prod : List Msg} (h1 : RowQJM X J Q1 mf inS cons prod) (h2 : RowQJM X J Q2 mf inS cons prod) :
    RowQJM X J (fun s live => Q1 s live ∧ Q2 s live) mf inS cons prod :=
  fun E s f tps tpl t pc S live a b s' R hg hJ hin hl hs hQ =>
    ⟨h1 E s f tps tpl t pc S live a b s' R hg hJ hin hl hs hQ.1, h2 E s f tps tpl t pc S live a b s' R hg hJ hin hl hs hQ.2⟩

/-! ## 2. The segment induction with `Q` in the row spec -/

section
variable (X : Ctx) {ρ : Type} [DecidableEq ρ] (act : List ρ) (inS outS : ρ → List F)
  (cons prod : ρ → List Msg) (init fin : List Msg) (pcf N Sf : F)

/-- **`exec_rowsJQ`: `exec_rowsJ` with the state invariant `Q` handed to the row spec** and a fee
bound `mf` in place of `X.maxFee` (a `memory.grow` row charges `fee + lin · n`).  Hypotheses and
conclusions as `exec_rowsJ` (`Main/SegSigma.lean`), with `RowFactsSegMapJQ X J Q mf` rows. -/
theorem exec_rowsJQ (sg : Nat → Nat × Nat) (st : Nat) (hst2 : st ≤ 2) (J : Nat → St → Prop)
    (Q : St → (Msg → Prop) → Prop) (mf : Nat)
    (hrows : ∀ r ∈ act, RowFactsSegMapJQ X J Q mf (inS r) (outS r) (cons r) (prod r) sg)
    (t0 S0 : Nat) (m0 : List F) (sbf cidf : F)
    (hst : (m0 :: act.map outS).Perm ([pcf, N, Sf, (st : F), sbf, cidf] :: act.map inS))
    (hch : (init ++ act.flatMap prod).Perm (fin ++ act.flatMap cons))
    (hinit : init.Nodup) (hinitTp : ∀ x ∈ init, x.tp ≤ t0)
    (ht : t0 + act.length + 1 + (2 ^ 30 + 2 ^ 16) < ZkFormal.Algebra.P)
    (hfee : S0 + (act.length + 1) * (mf + 1) < ZkFormal.Algebra.P)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + mf - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64)
    {s0 : St} (h0 : Bnd X sg s0 t0 S0 m0 init)
    (hQ : ∀ r ∈ act, RowQJM X J Q mf (inS r) (cons r) (prod r))
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
    have : 1 * 1 ≤ (act.length + 1) * (mf + 1) := Nat.mul_le_mul (by omega) (by omega)
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
      RowFactsSegJQ X J Q mf (inS rs[k]) (outS rs[k]) (cons rs[k]) (prod rs[k])
        (sg (t0 + k + 1)) (sg (t0 + k + 1 + 1)) :=
    fun k hk => by
      have e : lvl (inS rs[k]) = ((t0 + k + 1 : Nat) : F) := lvlk k hk
      have h := hrows rs[k] (hmem k hk)
      unfold RowFactsSegMapJQ at h
      rwa [e, Fp.toNat_cast_of_lt (by omega)] at h
  have RF : ∀ k (hk : k < rs.length), RowFactsFlatM mf (inS rs[k]) (outS rs[k]) (cons rs[k]) (prod rs[k]) :=
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
  have step1 : ∀ k (hk : k < rs.length), (gasF (pos k)).toNat ≤ S0 + k * mf →
      ∃ fee, fee ≤ mf ∧ (gasF (pos (k + 1))).toNat = (gasF (pos k)).toNat + fee := by
    intro k hk hb
    obtain ⟨fee, hfl, hfe⟩ := (RF k hk).gasOut
    refine ⟨fee, hfl, ?_⟩
    rw [pos_out k hk, hfe, ← pos_in k hk]
    conv => lhs; rw [← Fp.cast_toNat (gasF (pos k))]
    rw [← Lean.Grind.Semiring.natCast_add, Fp.toNat_cast_of_lt]
    have : (k + 1) * (mf + 1) ≤ (act.length + 1) * (mf + 1) := Nat.mul_le_mul_right _ (by omega)
    have : k * mf + mf ≤ (k + 1) * (mf + 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    omega
  have gasB : ∀ k, k ≤ rs.length → (gasF (pos k)).toNat ≤ S0 + k * mf := by
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
      have hm : (k + 1) * (mf + 1) ≤ (act.length + 1) * (mf + 1) := Nat.mul_le_mul_right _ (by omega)
      have hS : (gasF (pos k)).toNat + mf < ZkFormal.Algebra.P := by
        have : k * mf + mf ≤ (k + 1) * (mf + 1) := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
        omega
      have hlive : ∀ x ∈ cons rs[k], live init prodL consL k x := fun x hx =>
        C.consumed_live (k := k) (by simp [consL]; omega) (by simpa [consL] using hx)
      obtain ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, hspec⟩ :=
        (RFS k (by omega)).spec E s f tps tpl (t0 + k + 1) pc _
          (live init prodL consL k) R hJk hQk (by rw [← pos_in k (by omega)]; exact hin) hlive (by omega) hS hg64
      have hout' : pos (k + 1) = stMsg (X.offOf k' + pc') (t0 + k + 1 + 1) ((gasF (pos k)).toNat + fee) hb sb' cid' := by
        rw [pos_out k (by omega), hout]
      have hg1 : (gasF (pos (k + 1))).toNat = (gasF (pos k)).toNat + fee := by
        rw [hout']; simp only [gasF, stMsg, List.getD_cons_succ, List.getD_cons_zero]
        exact Fp.toNat_cast_of_lt (by simp only [gasF] at hS; omega)
      have hgas' : X.R * ((gasF (pos k)).toNat + fee - (sg (t0 + k + 1)).1) ≤ (sg (t0 + k + 1)).2 := by
        have hm := hstepgas (t0 + k + 1) ((gasF (pos k)).toNat) s.gas.g R.gas
        have hle : (gasF (pos k)).toNat + fee - (sg (t0 + k + 1)).1 ≤
            (gasF (pos k)).toNat + mf - (sg (t0 + k + 1)).1 := by
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
        exact hQ rs[k] (hmem k (by omega)) E s f tps tpl (t0 + k + 1) pc _ (live init prodL consL k) _ _ s' R
          (hstepgas (t0 + k + 1) ((gasF (pos k)).toNat) s.gas.g R.gas) hJk
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

/-! ## 3. The size clause at the segment boundaries (SEGG's first row) -/

/-- **The size clause holds at the in-boundary** when the in-block's only space-8 message is the size
message of `s0` (SEGG's production `[8, 0, 0, pin, 0, 0, 0, t_in]` with `pin = s0.pages.size`). -/
theorem szC_init {s0 : St} {init : List Msg} {tin : Nat}
    (h8 : ∀ x ∈ init, x.space = 8 → x = szMsg s0.pages.size tin) (hm : szMsg s0.pages.size tin ∈ init) :
    SzC s0 (· ∈ init) :=
  ⟨tin, fun x hx => ⟨fun h => h8 x h hx, fun h => h ▸ hm⟩⟩

/-- **The out-boundary's size message carries the final page count** (SEGG's consumption is in the
out-block `fin`, and `SzC sN (· ∈ fin)` is `exec_rowsJQ`'s conclusion). -/
theorem szC_fin {sN : St} {fin : List Msg} (h : SzC sN (· ∈ fin)) {pout tz : Nat} (hm : szMsg pout tz ∈ fin) :
    pout = sN.pages.size :=
  SzC.pages h hm

/-- `64 · x = y` in the field with `y = 64 · p` (`64 · p < P`) pins `x = p`. -/
theorem pages_of_64 {x y : F} {p : Nat} (h : ((64 : Nat) : F) * x = y) (hy : y.toNat = 64 * p) (hp : 64 * p < P) :
    x.toNat = p := by
  have e : y = ((64 * p : Nat) : F) := by rw [← hy, Fp.cast_toNat]
  rw [e, Lean.Grind.Semiring.natCast_mul] at h
  have h64 : ((64 : Nat) : F) ≠ 0 := by
    intro h0
    have := congrArg Fp.toNat h0
    rw [Fp.toNat_cast_of_lt (by rw [P_val]; decide)] at this
    exact absurd this (by decide)
  have ex : x = ((p : Nat) : F) := by grind
  rw [ex, Fp.toNat_cast_of_lt (by omega)]

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirG nloc ngl) pub tr)
include H

/-- **SEGG's size messages, decoded**: with the public block counts `nblk_in = 64 · pin`,
`nblk_out = 64 · pout`, SEGG produces `szMsg pin t_in` and consumes `szMsg pout tz`. -/
theorem segg_size_dec {pin pout : Nat} (hin : (pNin pub).toNat = 64 * pin) (hout : (pNout pub).toNat = 64 * pout)
    (hpin : 64 * pin < P) (hpout : 64 * pout < P) :
    decMsg (segSzIn tr pub) = szMsg pin (pub.getD Chips.Seg.pubTIn 0).toNat ∧
      decMsg (segSzOut tr pub) = szMsg pout (sgc tr 0 2).toNat := by
  obtain ⟨h1, h2, -⟩ := segg_row0 H
  have e1 := pages_of_64 h1 hin hpin
  have e2 := pages_of_64 h2 hout hpout
  have h8 : (((Chips.memSizeSpace : Nat) : F)).toNat = 8 := Fp.toNat_cast_of_lt (by rw [P_val]; decide)
  have h0 : (0 : F).toNat = 0 := rfl
  constructor
  · simp only [decMsg, segSzIn, szMsg, List.getD_cons_zero, List.getD_cons_succ, h8, h0, e1]
  · simp only [decMsg, segSzOut, szMsg, List.getD_cons_zero, List.getD_cons_succ, h8, h0, e2]

/-- **The size message tracks the page count across the segment**: if the segment's in-block
carries SEGG's production as its only space-8 message and `s0` has `pin` pages, the size clause
holds at the start; if the size clause holds at the cut (`exec_rowsJQ`) and the out-block contains
SEGG's consumption, the final state has `pout` pages, i.e. `64 · sN.pages.size = nblk_out`. -/
theorem segg_size_track {pin pout : Nat} (hin : (pNin pub).toNat = 64 * pin) (hout : (pNout pub).toNat = 64 * pout)
    (hpin : 64 * pin < P) (hpout : 64 * pout < P) {init fin : List Msg} {s0 sN : St}
    (h8 : ∀ x ∈ init, x.space = 8 → x = decMsg (segSzIn tr pub)) (hmi : decMsg (segSzIn tr pub) ∈ init)
    (hs0 : s0.pages.size = pin) (hmf : decMsg (segSzOut tr pub) ∈ fin)
    (hN : SzC s0 (· ∈ init) → SzC sN (· ∈ fin)) :
    SzC s0 (· ∈ init) ∧ (pNout pub).toNat = 64 * sN.pages.size := by
  obtain ⟨e1, e2⟩ := segg_size_dec H hin hout hpin hpout
  rw [e1, ← hs0] at h8 hmi
  have h0 : SzC s0 (· ∈ init) := szC_init h8 hmi
  rw [e2] at hmf
  refine ⟨h0, ?_⟩
  rw [hout, szC_fin (hN h0) hmf]
end

/-! ## 4. Rows that keep the size clause -/

/-- **A row that keeps the page count and whose messages avoid space 8 keeps the size clause**
(every instruction row of `actListM2` keeps the page count, `seg_instr_pagesKeep`; HOST rows by
`HostPagesRely`).  Note the boundary relation's space clause `SpC` (`SpaceOK`, `Main/SegView.lean`)
has no space 8: with the size message live, the grow chain's boundary relation needs `SpaceOK ∨
space = 8`. -/
theorem rowQJ_szC {X : Ctx} {J : Nat → St → Prop} {inS : List F} {cons prod : List Msg}
    (hk : PagesKeep X inS) (hc : ∀ x ∈ cons, x.space ≠ 8) (hp : ∀ x ∈ prod, x.space ≠ 8) :
    RowQJ X J SzC inS cons prod :=
  fun E s f tps tpl t pc S live a b s' R _ hin _ hs hQ =>
    SzC.keep hQ hc hp (hk E s f tps tpl t pc S live a b s' R hin hs)

/-! ## 5. A MEMG row's spec premise from its decoding -/

/-- The premises a row's decoding states about every related pre-state (the shape of
`RowSpecSegJQ`'s hypotheses). -/
def AtRow (X : Ctx) (inS : List F) (P : Env → St → Frame → (Nat → Nat) → Nat → Nat → Nat → Prop) : Prop :=
  ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) (a b : Nat),
    RelW X E s f tps tpl t pc S live a b → inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid → P E s f tps t pc S

/-- **The spec premise of a MEMG `memory.size` row, from the size clause.**  The row's decoding
gives: the instruction at its pc is `memory.size` with fee units `fee ≤ mf` and a straight successor
(code facts, `hcode`); it consumes the size message `szMsg pg tz` and produces the pushed `i32` and
`szMsg pg t` (`hprod`; the slot is the stack height); its out-STATE is `pc + 1`, `S + fee`
(`hout`).  The size clause in `Q` pins `pg = s.pages.size`, and `step_memSize` gives the step. -/
theorem memSize_rowSpecJQ (X : Ctx) {J : Nat → St → Prop} {Q : St → (Msg → Prop) → Prop} {mf : Nat}
    (hQ : ∀ s live, Q s live → SzC s live) {inS outS : List F} {prod : List Msg} {sg : Nat × Nat}
    (hJk : RowJKeep X J inS) {pg tz fee : Nat} (hfm : fee ≤ mf)
    (hcode : AtRow X inS fun E s f _ _ pc _ => (X.pfOf E.k).code[pc]? = some .memSize ∧
      feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee ∧ pc + 1 < (X.pfOf E.k).code.size ∧
      (∃ ls, (X.ckOf E.k).labels[pc + 1]? = some ls ∧ f.labels = shiftLabels E.sb ls) ∧
      (X.ckOf E.k).heights[pc + 1]? = some (s.stack.size + 1 - E.sb))
    (hout : AtRow X inS fun E _ _ _ t pc S => outS = stMsg (X.offOf E.k + (pc + 1)) (t + 1) (S + fee) 0 E.sb E.cid)
    (hprod : AtRow X inS fun _ s _ _ t _ _ => prod = [enc 0 s.stack.size (i32V pg) t, szMsg pg t]) :
    RowSpecSegJQ X J Q mf inS outS [szMsg pg tz] prod sg sg := by
  intro E s f tps tpl t pc S live R hJ hQs hin hl h1 h2 h3
  obtain ⟨hins, hfee, hnext, hL1, hH1⟩ := hcode E s f tps tpl t pc S live _ _ R hin
  have hz : live (szMsg pg tz) := hl _ (by simp)
  have hpg : pg = s.pages.size := SzC.pages (hQ s live hQs) hz
  subst hpg
  refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfm, by omega, by rw [hout E s f tps tpl t pc S live _ _ R hin], ?_⟩
  intro hg
  refine ⟨fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  obtain ⟨s', hs, -, hR, -⟩ := step_memSize X R hins hfee hg h3 hnext hL1 hH1 (hQ s live hQs) hz
  rw [hprod E s f tps tpl t pc S live _ _ R hin]
  exact ⟨s', hs, hR, hJk E s f tps tpl t pc S live _ _ s' R hin h1 hJ hs⟩

/-- **The spec premise of a successful MEMG `memory.grow` row**: as `memSize_rowSpecJQ`, with the
consumed top operand an `i32` page count `w` (`hstk`), the grow succeeding (`pages + w ≤
maxMemoryPages`, from the row's `ok = 1` and the size clause), the linear fee `fee + lin · w ≤ mf`,
and the grown zero bytes `A` (MEMBG's blocks of this grow) in the new pages. -/
theorem memGrowOk_rowSpecJQ (X : Ctx) {J : Nat → St → Prop} {Q : St → (Msg → Prop) → Prop} {mf : Nat}
    (hQ : ∀ s live, Q s live → SzC s live) {inS outS : List F} {cons prod : List Msg} {sg : Nat × Nat}
    (hJk : RowJKeep X J inS) {pg tz fee lin : Nat} {w : UInt32} (hfm : fee + lin * w.toNat ≤ mf)
    (hok : pg + w.toNat ≤ X.cfg.maxMemoryPages) (A : List Nat) (hAnd : A.Nodup)
    (hA : ∀ a ∈ A, pg * pageSize ≤ a ∧ a < (pg + w.toNat) * pageSize)
    (hcode : AtRow X inS fun E s f _ _ pc _ => (X.pfOf E.k).code[pc]? = some .memGrow ∧
      growFee X.cfg (X.pfOf E.k).gas[pc]? = some (fee, lin) ∧ pc + 1 < (X.pfOf E.k).code.size ∧
      (∃ ls, (X.ckOf E.k).labels[pc + 1]? = some ls ∧ f.labels = shiftLabels E.sb ls) ∧
      (X.ckOf E.k).heights[pc + 1]? = some (s.stack.size - E.sb) ∧
      E.sb + 1 ≤ s.stack.size ∧ s.stack[s.stack.size - 1]? = some (.i32 w))
    (hout : AtRow X inS fun E _ _ _ t pc S =>
      outS = stMsg (X.offOf E.k + (pc + 1)) (t + 1) (S + (fee + lin * w.toNat)) 0 E.sb E.cid)
    (hcons : AtRow X inS fun _ s _ tps _ _ _ =>
      cons = [enc 0 (s.stack.size - 1) (.i32 w) (tps (s.stack.size - 1)), szMsg pg tz])
    (hprod : AtRow X inS fun _ s _ _ t _ _ =>
      prod = enc 0 (s.stack.size - 1) (i32V pg) t :: szMsg (pg + w.toNat) t :: zeroBytes A t) :
    RowSpecSegJQ X J Q mf inS outS cons prod sg sg := by
  intro E s f tps tpl t pc S live R hJ hQs hin hl h1 h2 h3
  obtain ⟨hins, hfee, hnext, hL1, hH1, hstk, hw⟩ := hcode E s f tps tpl t pc S live _ _ R hin
  rw [hcons E s f tps tpl t pc S live _ _ R hin] at hl ⊢
  have hz : live (szMsg pg tz) := hl _ (by simp)
  have hpg : pg = s.pages.size := SzC.pages (hQ s live hQs) hz
  subst hpg
  refine ⟨E.k, pc + 1, fee + lin * w.toNat, 0, E.sb, E.cid, hfm, by omega,
    by rw [hout E s f tps tpl t pc S live _ _ R hin], ?_⟩
  intro hg
  refine ⟨fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  obtain ⟨s', hs, -, hR, -⟩ := step_memGrow_ok X R hins hfee hstk hw hg hok hnext hL1 hH1 (hQ s live hQs) hz
    A hAnd hA
  rw [hprod E s f tps tpl t pc S live _ _ R hin]
  exact ⟨s', hs, hR, hJk E s f tps tpl t pc S live _ _ s' R hin h1 hJ hs⟩

/-- **A MEMG `memory.size` row keeps the size clause** (`RowQJM`; the step is `step_memSize`'s, by
determinism of `step`). -/
theorem memSize_rowQJM (X : Ctx) {J : Nat → St → Prop} {mf : Nat} {inS : List F} {prod : List Msg}
    {pg tz fee : Nat} (hfm : fee ≤ mf)
    (hcode : AtRow X inS fun E s f _ _ pc _ => (X.pfOf E.k).code[pc]? = some .memSize ∧
      feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee ∧ pc + 1 < (X.pfOf E.k).code.size ∧
      (∃ ls, (X.ckOf E.k).labels[pc + 1]? = some ls ∧ f.labels = shiftLabels E.sb ls) ∧
      (X.ckOf E.k).heights[pc + 1]? = some (s.stack.size + 1 - E.sb))
    (hprod : AtRow X inS fun _ s _ _ t _ _ => prod = [enc 0 s.stack.size (i32V pg) t, szMsg pg t])
    (hg64 : X.g0 < 2 ^ 64) :
    RowQJM X J SzC mf inS [szMsg pg tz] prod := by
  intro E s f tps tpl t pc S live a b s' R hg _ hin hl hs hQ
  obtain ⟨hins, hfee, hnext, hL1, hH1⟩ := hcode E s f tps tpl t pc S live _ _ R hin
  have hz : live (szMsg pg tz) := hl _ (by simp)
  have hpg : pg = s.pages.size := SzC.pages hQ hz
  subst hpg
  have hg' : X.R * (S + fee - a) ≤ b :=
    Nat.le_trans (Nat.mul_le_mul_left _ (by omega)) hg
  obtain ⟨s'', hs'', -, -, hQ'⟩ := step_memSize X R hins hfee hg' hg64 hnext hL1 hH1 hQ hz
  rw [hs] at hs''
  cases hs''
  rw [hprod E s f tps tpl t pc S live _ _ R hin]
  exact hQ'

/-- **A successful MEMG `memory.grow` row keeps the size clause** (`step_memGrow_ok`). -/
theorem memGrowOk_rowQJM (X : Ctx) {J : Nat → St → Prop} {mf : Nat} {inS : List F} {cons prod : List Msg}
    {pg tz fee lin : Nat} {w : UInt32} (hfm : fee + lin * w.toNat ≤ mf)
    (hok : pg + w.toNat ≤ X.cfg.maxMemoryPages) (A : List Nat) (hAnd : A.Nodup)
    (hA : ∀ a ∈ A, pg * pageSize ≤ a ∧ a < (pg + w.toNat) * pageSize)
    (hcode : AtRow X inS fun E s f _ _ pc _ => (X.pfOf E.k).code[pc]? = some .memGrow ∧
      growFee X.cfg (X.pfOf E.k).gas[pc]? = some (fee, lin) ∧ pc + 1 < (X.pfOf E.k).code.size ∧
      (∃ ls, (X.ckOf E.k).labels[pc + 1]? = some ls ∧ f.labels = shiftLabels E.sb ls) ∧
      (X.ckOf E.k).heights[pc + 1]? = some (s.stack.size - E.sb) ∧
      E.sb + 1 ≤ s.stack.size ∧ s.stack[s.stack.size - 1]? = some (.i32 w))
    (hcons : AtRow X inS fun _ s _ tps _ _ _ =>
      cons = [enc 0 (s.stack.size - 1) (.i32 w) (tps (s.stack.size - 1)), szMsg pg tz])
    (hprod : AtRow X inS fun _ s _ _ t _ _ =>
      prod = enc 0 (s.stack.size - 1) (i32V pg) t :: szMsg (pg + w.toNat) t :: zeroBytes A t) :
    RowQJM X J SzC mf inS cons prod := by
  intro E s f tps tpl t pc S live a b s' R hg _ hin hl hs hQ
  obtain ⟨hins, hfee, hnext, hL1, hH1, hstk, hw⟩ := hcode E s f tps tpl t pc S live _ _ R hin
  rw [hcons E s f tps tpl t pc S live _ _ R hin] at hl ⊢
  have hz : live (szMsg pg tz) := hl _ (by simp)
  have hpg : pg = s.pages.size := SzC.pages hQ hz
  subst hpg
  have hg' : X.R * (S + (fee + lin * w.toNat) - a) ≤ b :=
    Nat.le_trans (Nat.mul_le_mul_left _ (by omega)) hg
  obtain ⟨s'', hs'', -, -, hQ'⟩ := step_memGrow_ok X R hins hfee hstk hw hg' hok hnext hL1 hH1 hQ hz A hAnd hA
  rw [hs] at hs''
  cases hs''
  rw [hprod E s f tps tpl t pc S live _ _ R hin]
  exact hQ'

#print axioms exec_rowsJQ
#print axioms RowFactsSegMapJ.toJQ
#print axioms memSize_rowQJM
#print axioms memGrowOk_rowQJM
#print axioms memSize_rowSpecJQ
#print axioms memGrowOk_rowSpecJQ
#print axioms rowQJ_szC
#print axioms pages_of_64
#print axioms segg_size_dec
#print axioms segg_size_track

end WasmBase
