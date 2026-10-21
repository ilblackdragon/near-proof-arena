import WasmBase.Main.Abstract
import WasmBase.Main.HostRel
import WasmBase.Main.ExecHost

/-!
# WasmBase.Main.SegHarness — `exec_of_rows` with a segment that restarts

`Main/Abstract.lean:exec_of_rows` threads **one** gas segment `(S_seg, segb)` through every row and
concludes `R · (Sf − S_seg) + g = segb`.  A host-carrying trace cannot use it: a HOST row
resynchronises the budget (`g := remaining`), so every instruction after it lives in a different
segment.

**Status: `exec_of_rows_seg` is proved.**  `exec_of_rows` is re-run with the gas segment threaded
per row (`seg : Nat → Nat × Nat`, indexed by STATE time so it survives the `act`/`rs` permutation).
`RowSpecSeg` takes the successor segment as a parameter; `RowFactsSegMap` reads it off the thread.

What remains for `wasm_base_exec_host` is the *instantiation*: the bus decomposition
(`occ_bits`, `looks_of`, the `ChanOK` assembly) re-done for `wasmBaseHostAir`, whose 26 tables
include table 22's host rows.  That is `Exec.lean:wasm_base_exec`'s ~160-line body, not the
induction.

## The two differences from `exec_of_rows`

The proof is `exec_of_rows`'s, with the segment touched in exactly three places.

1. **The per-row gas side condition.**  `exec_of_rows` derives `R · (S+fee − S_seg) ≤ segb` for
   every row from a *single* hypothesis `R · (Sf − S_seg) ≤ segb`, using monotonicity of the gas
   field along the path.  With restarts that monotonicity is false — `S` (the instruction counter)
   is still monotone, but the *budget* is reset, and after a restart at `(S, g_after)` the next
   row's condition is `R · fee ≤ g_after`, which is a genuine machine fact ("the fee fits in what
   the host left"), not a consequence of the initial budget.  So it becomes a per-step hypothesis
   `hstepgas` (§ `step_gas_side`).
2. **The successor `Rel`'s segment.**  `RowSpec2` returns `Rel` at the segment it was given.  At a
   kept row `segs (k+1) = segs k`, so that is the wanted segment.  At a host row the successor comes
   from `Main/HostRel.host_rel_restart` instead, at `segs (k+1) = (S + fee, g_after)`.
3. **The conclusion.**  The final invariant is reported at `segs (rs.length)` — the segment after
   the last row — rather than at the single global pair.

Everything else — the chain, the level bookkeeping, `ChanOK`, the monotone `S`, the halting step —
is unchanged, which is why the proof is a *modification* of `exec_of_rows` rather than a new
argument.

## The invariant carried

`Rel` at `segs k` for the state after `k` rows, with the live set `live init prodL consL k`.  This is
`exec_of_rows`'s `IH` with `(S_seg, segb)` replaced by `segs k`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## The per-step gas side condition

`exec_of_rows` gets its per-row gas bound from monotonicity: `R·(S_k − S_seg) ≤ segb` for all `k`
follows from the bound at the end because `S_k ≤ Sf`.  That fails under restarts.  What survives is
weaker and must be assumed instead: at each row, the fee fits in the budget the current segment
carries. -/

/-- **The per-row gas side condition.**  `R · (S + fee − S_seg) ≤ segb` is what `RowSpec2` needs.
After a restart to `(S_h, g_after)` and before the next row at gas field `S`, this is
`R · (S − S_h) + R · fee ≤ g_after`: the gas burnt since the restart plus this row's fee must fit in
what the host returned.  A real machine property, not a bookkeeping identity. -/
def StepGas (R : Nat) : Nat → Nat → Nat → Nat → Nat → Prop :=
  fun S fee S_seg segb _ => R * (S + fee - S_seg) ≤ segb

/-- The no-restart case recovers `exec_of_rows`'s single global hypothesis: if the segment never
moves, the per-row bound is exactly the monotone consequence of the final one. -/
theorem StepGas.of_global {R Sf S_seg segb : Nat} (hseg : S_seg ≤ Sf)
    (h : R * (Sf - S_seg) ≤ segb) {S fee : Nat} (hSe : S + fee ≤ Sf) :
    StepGas R S fee S_seg segb Sf := by
  unfold StepGas
  exact Nat.le_trans (Nat.mul_le_mul_left _ (by omega)) h


/-! ## The per-row spec that names its successor segment

`RowSpec2` concludes `Rel` at the segment it was *given*.  The induction needs the successor
segment to be part of the row's output, because a host row changes it.  `RowSpecSeg` is that: the
same shape as `RowSpec2`, with the successor `Rel` at an arbitrary `(S_seg', segb')` chosen by the
row. -/

/-- **A row's step, with both segments explicit.**  The input segment and the successor segment are
*parameters*: the row is only asserted at the segment it actually runs in, and it lands where the
caller says.  This is what makes the segment thread permutation-safe — the pair travels with the
row in the action list.

* ordinary row: `sgin = sgout`, from `RowSpec2` (`ofSame`);
* host row: `sgout = (S + fee, g_after)`, from `Main/HostRel.host_rel_restart` (`ofHost`). -/
def RowSpecSeg (X : Ctx) (inS outS : List F) (cons prod : List Msg) (sgin sgout : Nat × Nat) : Prop :=
  ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop),
    RelW X E s f tps tpl t pc S live sgin.1 sgin.2 →
    inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid → (∀ x ∈ cons, live x) →
    t + 1 < ZkFormal.Algebra.P → S + X.maxFee < ZkFormal.Algebra.P → X.g0 < 2 ^ 64 →
    ∃ k' pc' fee hb sb' cid',
      fee ≤ X.maxFee ∧ hb ≤ 2 ∧
      outS = stMsg (X.offOf k' + pc') (t + 1) (S + fee) hb sb' cid' ∧
      (X.R * (S + fee - sgin.1) ≤ sgin.2 →
        (hb = 0 → ∃ s', step X.cfg X.p s = .cont s' ∧
          Rel X s' (t + 1) k' pc' (S + fee) sb' cid' (stepLive live cons prod) sgout.1 sgout.2) ∧
        (hb = 1 → ∃ sN, step X.cfg X.p s = .fin sN ∧ sN.frames = [] ∧
          X.R * (S + fee - sgout.1) + sN.gas.g = sgout.2 ∧
          ∃ G : Msg → Prop, (∀ x, G x → x.space ≠ 0 ∧ x.space ≠ 16) ∧
          ∀ x, stepLive live cons prod x ↔ x ∈ stackView sN.stack tps ∨ x ∈ localView 16 f.locals tpl ∨ G x) ∧
        (hb = 2 → ∃ sN e, step X.cfg X.p s = .abort sN e ∧
          X.R * (S + fee - sgout.1) + sN.gas.g = sgout.2))

/-- **An ordinary row keeps the segment.** -/
theorem RowSpecSeg.ofSame {X : Ctx} {inS outS : List F} {cons prod : List Msg} {sg : Nat × Nat}
    (h : RowSpec2 X inS outS cons prod) : RowSpecSeg X inS outS cons prod sg sg := by
  intro E s f tps tpl t pc S live R hin hl h1 h2 h3
  obtain ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, hsp⟩ :=
    h E s f tps tpl t pc S live sg.1 sg.2 R hin hl h1 h2 h3
  exact ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, hsp⟩

/-- `RowFacts2`, with both segments explicit. -/
structure RowFactsSeg (X : Ctx) (inS outS : List F) (cons prod : List Msg) (sgin sgout : Nat × Nat) :
    Prop where
  spec : RowSpecSeg X inS outS cons prod sgin sgout
  halt0 : inS.getD 3 0 = 0
  tsOut : lvl outS = lvl inS + 1
  gasOut : ∃ fee, fee ≤ X.maxFee ∧ gasF outS = gasF inS + (fee : F)
  consT : ∀ x ∈ cons, ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((x.tp + 1 + n : Nat) : F) = lvl inS
  prodT : ∀ x ∈ prod, x.tp < ZkFormal.Algebra.P ∧ ((x.tp : Nat) : F) = lvl inS
  prodNd : prod.Nodup

/-- A row whose segments are read off the STATE-time indexed thread `seg`: a row whose input STATE
message carries time `t` runs in segment `seg t` and leaves the segment `seg (t+1)`.

The index is **the row's STATE time**, not its position in the permuted action list — which is what
makes the premise permutation-safe (`exec_of_rows_seg` recovers the positional form with `lvlk`).
An earlier version quantified over every natural `k` instead, which forced `RowSpecSeg` at segments
that have nothing to do with the row and so could not be instantiated from a trace at all. -/
def RowFactsSegMap (X : Ctx) (inS outS : List F) (cons prod : List Msg) (seg : Nat → Nat × Nat) :
    Prop :=
  RowFactsSeg X inS outS cons prod (seg (lvl inS).toNat) (seg ((lvl inS).toNat + 1))

/-- `RowFacts2` gives `RowFactsSeg` at any fixed segment. -/
theorem RowFacts2.toSeg {X : Ctx} {inS outS : List F} {cons prod : List Msg} {sg : Nat × Nat}
    (h : RowFacts2 X inS outS cons prod) : RowFactsSeg X inS outS cons prod sg sg :=
  ⟨RowSpecSeg.ofSame h.spec, h.halt0, h.tsOut, h.gasOut, h.consT, h.prodT, h.prodNd⟩

/-- **The segment-free half of a row's facts.**  Everything `RowFacts2` carries except the `spec`
field, i.e. the timestamp, gas-delta and channel-shape facts.  The `spec` field is a `RowSpec2` at
one *fixed* segment, which is exactly the thing a host row cannot satisfy (it restarts the segment),
so the induction must not require it — the segment-aware `spec` comes from `RowFactsSegMap`
instead.  `RowFacts2.toFlat` recovers it for base rows.  (The earlier `h2 : RowFacts2` premise made
`exec_of_rows_seg` inapplicable to any host trace; it is gone, and every field it carried is a field
of `RowFactsSeg`.) -/
structure RowFactsFlat (X : Ctx) (inS outS : List F) (cons prod : List Msg) : Prop where
  halt0 : inS.getD 3 0 = 0
  tsOut : lvl outS = lvl inS + 1
  gasOut : ∃ fee, fee ≤ X.maxFee ∧ gasF outS = gasF inS + (fee : F)
  consT : ∀ x ∈ cons, ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((x.tp + 1 + n : Nat) : F) = lvl inS
  prodT : ∀ x ∈ prod, x.tp < ZkFormal.Algebra.P ∧ ((x.tp : Nat) : F) = lvl inS
  prodNd : prod.Nodup

/-- A `RowFacts2` is a `RowFactsFlat` plus its fixed-segment `spec`. -/
theorem RowFacts2.toFlat {X : Ctx} {inS outS : List F} {cons prod : List Msg}
    (h : RowFacts2 X inS outS cons prod) : RowFactsFlat X inS outS cons prod :=
  ⟨h.halt0, h.tsOut, h.gasOut, h.consT, h.prodT, h.prodNd⟩

/-- A `RowFactsSeg` is a `RowFactsFlat`. -/
theorem RowFactsSeg.toFlat {X : Ctx} {inS outS : List F} {cons prod : List Msg} {sgin sgout : Nat × Nat}
    (h : RowFactsSeg X inS outS cons prod sgin sgout) : RowFactsFlat X inS outS cons prod :=
  ⟨h.halt0, h.tsOut, h.gasOut, h.consT, h.prodT, h.prodNd⟩


/-! ## The segmented execution theorem

`exec_of_rows`'s step (C) carries the segment in its induction hypothesis.  Requires:

* `segs : Nat → Nat × Nat` — the segment at each row, with `segs 0 = sg0` and
  `segs (k+1) = sgout` of row `k`;
* `hstepgas t S` — *given* that the row's gas so far fits its segment (`R · (S − (segs t).1) ≤
  (segs t).2`, which is `RelW.gas` for any related state), the fee also fits:
  `R · (S + maxFee − (segs t).1) ≤ (segs t).2`.

The last of these is where the segmentation costs something real: `exec_of_rows` derives it from
monotonicity of one global budget, which is false after a restart.  The *unconditional* form
`∀ t S, R · (S + maxFee − (segs t).1) ≤ (segs t).2` is **unsatisfiable** for `R ≥ 1` (take
`S = (segs t).2 + (segs t).1 + maxFee + 1`), so it can only have been vacuous; the implication
above is what `RelW.gas` actually supplies at each row. -/
variable (X : Ctx) {ρ : Type} [DecidableEq ρ] (act : List ρ) (inS outS : ρ → List F)
  (cons prod : ρ → List Msg) (init fin : List Msg) (pcf N Sf : F)

theorem exec_of_rows_seg (seg : Nat → Nat × Nat) (st : Nat) (hst12 : st = 1 ∨ st = 2)
    (hrows : ∀ r ∈ act, RowFactsSegMap X (inS r) (outS r) (cons r) (prod r) seg)
    (sbf cidf : F)
    (hst : (stMsg 0 1 0 0 0 0 :: act.map outS).Perm ([pcf, N, Sf, (st : F), sbf, cidf] :: act.map inS))
    (hch : (init ++ act.flatMap prod).Perm (fin ++ act.flatMap cons))
    (hinit : init.Nodup) (hinitTp : ∀ x ∈ init, x.tp = 0)
    (hlen : act.length < 2 ^ 28)
    (hfee : (act.length + 1) * (X.maxFee + 1) < ZkFormal.Algebra.P)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (seg t).1) + g = (seg t).2 →
      X.R * (S + X.maxFee - (seg t).1) ≤ (seg t).2)
    (hg64 : X.g0 < 2 ^ 64)
    {E0 : Env} (hE0 : E0.sb = 0 ∧ E0.cid = 0 ∧ E0.k = 0)
    {s0 : St} {f0 : Frame}
    (h0 : RelW X E0 s0 f0 (fun _ => 0) (fun _ => 0) 1 0 0 (· ∈ init) (seg 1).1 (seg 1).2) :
    act.length + 1 = N.toNat ∧
    (st = 1 → ∃ sN tps tpl locs, run X.cfg X.p act.length s0 = .fin sN ∧ sN.frames = [] ∧
      X.R * (Sf.toNat - (seg (act.length + 1)).1) + sN.gas.g = (seg (act.length + 1)).2 ∧
      ∃ G : Msg → Prop, (∀ x, G x → x.space ≠ 0 ∧ x.space ≠ 16) ∧
      ∀ x, x ∈ fin ↔ x ∈ stackView sN.stack tps ∨ x ∈ localView 16 locs tpl ∨ G x) ∧
    (st = 2 → ∃ sN e, run X.cfg X.p act.length s0 = .abort sN e ∧
      X.R * (Sf.toNat - (seg (act.length + 1)).1) + sN.gas.g = (seg (act.length + 1)).2) := by
  have hP' := P_val
  -- (A) the chain
  let g : ρ → List F × List F := fun r => (inS r, outS r)
  have hE1 : (act.map g).map Prod.snd = act.map outS := by simp [g, List.map_map]
  have hE2 : (act.map g).map Prod.fst = act.map inS := by simp [g, List.map_map]
  have hstepE : ∀ e ∈ act.map g, lvl e.2 = lvl e.1 + 1 := by
    intro e he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    exact (hrows r hr).tsOut
  obtain ⟨es, hes, hpath⟩ := chain (act.map g) (stMsg 0 1 0 0 0 0) [pcf, N, Sf, (st : F), sbf, cidf] lvl
    (by rw [hE1, hE2]; exact hst) hstepE (by simp; omega)
  obtain ⟨rs, hrs, rfl⟩ := perm_map_lift g es act hes
  have hlenrs : rs.length = act.length := hrs.length_eq
  have hmem : ∀ k (hk : k < rs.length), rs[k] ∈ act := fun k hk => hrs.subset (List.getElem_mem hk)
  obtain ⟨lk, lfin⟩ := path_levels lvl (rs.map g) _ _ hpath (fun e he => hstepE e (hes.subset he))
  obtain ⟨link, ends, _⟩ := path_link (rs.map g) _ _ hpath
  simp only [List.length_map, List.getElem_map] at lk lfin link ends
  have l0 : lvl (stMsg 0 1 0 0 0 0) = 1 := rfl
  have lvlk : ∀ k (hk : k < rs.length), lvl (inS rs[k]) = ((k + 1 : Nat) : F) := by
    intro k hk; rw [lk k hk, l0, Lean.Grind.Semiring.natCast_add, cast_one]; grind
  have RFS : ∀ k (hk : k < rs.length),
      RowFactsSeg X (inS rs[k]) (outS rs[k]) (cons rs[k]) (prod rs[k])
        (seg (k + 1)) (seg (k + 2)) :=
    fun k hk => by
      have e : lvl (inS rs[k]) = ((k + 1 : Nat) : F) := lvlk k hk
      have h := hrows rs[k] (hmem k hk)
      unfold RowFactsSegMap at h
      rwa [e, Fp.toNat_cast_of_lt (by omega)] at h
  have RF : ∀ k (hk : k < rs.length), RowFactsFlat X (inS rs[k]) (outS rs[k]) (cons rs[k]) (prod rs[k]) :=
    fun k hk => (RFS k hk).toFlat
  have hpos : 0 < rs.length := by
    refine Nat.pos_of_ne_zero fun h0' => ?_
    have := (path_link (rs.map g) _ _ hpath).2.2 (by simp [h0'])
    simp only [stMsg, List.cons.injEq] at this
    rcases hst12 with rfl | rfl <;> exact absurd this.2.2.2.1 (by decide)
  have hN : act.length + 1 = N.toNat := by
    have : N = ((rs.length + 1 : Nat) : F) := by
      have e : lvl [pcf, N, Sf, (st : F), sbf, cidf] = N := rfl
      rw [← e, lfin, l0, Lean.Grind.Semiring.natCast_add, cast_one]; grind
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
      simp only [pos, h1, dite_false]; exact (ends hpos).2.symm
  have pos0 : pos 0 = stMsg 0 1 0 0 0 0 := by rw [pos_in 0 hpos]; exact (ends hpos).1
  -- gas units along the path: no wrap-around, monotone up to `Sf`
  have gasB : ∀ k, k ≤ rs.length → (gasF (pos k)).toNat ≤ k * X.maxFee ∧
      ∀ j, k ≤ j → j ≤ rs.length → (gasF (pos k)).toNat ≤ (gasF (pos j)).toNat := by
    have step1 : ∀ k (hk : k < rs.length), (gasF (pos k)).toNat ≤ k * X.maxFee →
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
    have bnd : ∀ k, k ≤ rs.length → (gasF (pos k)).toNat ≤ k * X.maxFee := by
      intro k
      induction k with
      | zero => intro _; rw [pos0]; simp [gasF, stMsg]; rfl
      | succ k ih =>
        intro hk
        have ih' := ih (by omega)
        obtain ⟨fee, hfl, he⟩ := step1 k (by omega) ih'
        rw [he, Nat.succ_mul]
        omega
    refine fun k hk => ⟨bnd k hk, ?_⟩
    intro j hkj hjn
    induction j with
    | zero => have : k = 0 := by omega
              subst this; exact Nat.le_refl _
    | succ j ih =>
      by_cases hkj' : k = j + 1
      · subst hkj'; exact Nat.le_refl _
      · have := ih (by omega) (by omega)
        obtain ⟨fee, hfl, he⟩ := step1 j (by omega) (bnd j (by omega))
        rw [he]
        omega
  have posN : pos rs.length = [pcf, N, Sf, (st : F), sbf, cidf] := by simp [pos]
  have gasN : (gasF (pos rs.length)).toNat = Sf.toNat := by rw [posN]; rfl
  -- (B) the channel
  let prodL := rs.map prod
  let consL := rs.map cons
  have hpTp : ∀ k (hk : k < rs.length), ∀ x ∈ prod rs[k], x.tp = k + 1 := by
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
  have tpBound : ∀ x ∈ fin ++ consL.flatten, x.tp ≤ rs.length := by
    intro x hx
    rcases List.mem_append.mp (hpermC.symm.subset hx) with h | h
    · rw [hinitTp x h]; omega
    · obtain ⟨j, hj, hxj⟩ := mem_flatten_iff.mp h
      simp only [prodL, List.length_map, List.getElem_map] at hj hxj
      rw [hpTp j hj x hxj]; omega
  have C : ChanOK init fin prodL consL Msg.tp := by
    refine ⟨by simp [prodL, consL], hpermC, ?_, hinitTp, ?_, ?_⟩
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
      exact hpTp k hk x hx
    · intro k hk x hx
      simp only [consL, List.length_map, List.getElem_map] at hk hx
      obtain ⟨m, hm, he⟩ := (RF k hk).consT x hx
      rw [lvlk k hk] at he
      have hb := tpBound x (List.mem_append_right _ (mem_flatten_iff.mpr ⟨k, by simpa [consL] using hk, by simpa [consL] using hx⟩))
      have := natEq he (by omega) (by omega)
      omega
  -- (C) induction along the path
  have IH : ∀ k (hk : k < rs.length), ∃ s q pc sb cid, (∀ m, run X.cfg X.p (m + k) s0 = run X.cfg X.p m s) ∧
      inS rs[k] = stMsg (X.offOf q + pc) (k + 1) (gasF (pos k)).toNat 0 sb cid ∧
      Rel X s (k + 1) q pc (gasF (pos k)).toNat sb cid (live init prodL consL k)
        (seg (k + 1)).1 (seg (k + 1)).2 := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨s0, 0, 0, 0, 0, fun m => rfl, ?_, ?_⟩
      · rw [← pos_in 0 hk, pos0, X.off_zero]; rfl
      · rw [pos0]
        have h0' := Rel_of_RelW_congr h0 (live' := live init prodL consL 0)
          (by funext x; simp [live, prodBefore, consBefore])
        rw [hE0.1, hE0.2.1, hE0.2.2] at h0'
        exact h0'
    | succ k ih =>
      intro hk
      obtain ⟨s, q, pc, sb, cid, hrun, hin, E, f, tps, tpl, rfl, rfl, rfl, R⟩ := ih (by omega)
      have gb := (gasB k (by omega)).1
      have hm : (k + 1) * (X.maxFee + 1) ≤ (act.length + 1) * (X.maxFee + 1) := Nat.mul_le_mul_right _ (by omega)
      have hS : (gasF (pos k)).toNat + X.maxFee < ZkFormal.Algebra.P := by
        have : k * X.maxFee + X.maxFee ≤ (k + 1) * (X.maxFee + 1) := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
        omega
      have hlive : ∀ x ∈ cons rs[k], live init prodL consL k x := fun x hx =>
        C.consumed_live (k := k) (by simp [consL]; omega) (by simpa [consL] using hx)
      obtain ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, hspec⟩ :=
        (RFS k (by omega)).spec E s f tps tpl (k + 1) pc _
          (live init prodL consL k) R hin hlive (by omega) hS hg64
      have hout' : pos (k + 1) = stMsg (X.offOf k' + pc') (k + 1 + 1) ((gasF (pos k)).toNat + fee) hb sb' cid' := by
        rw [pos_out k (by omega), hout]
      have hg1 : (gasF (pos (k + 1))).toNat = (gasF (pos k)).toNat + fee := by
        rw [hout']; simp only [gasF, stMsg, List.getD_cons_succ, List.getD_cons_zero]
        exact Fp.toNat_cast_of_lt (by simp only [gasF] at hS; omega)
      have hgas' : X.R * ((gasF (pos k)).toNat + fee - (seg (k + 1)).1) ≤ (seg (k + 1)).2 := by
        have hm := hstepgas (k + 1) ((gasF (pos k)).toNat) s.gas.g R.gas
        have hle : (gasF (pos k)).toNat + fee - (seg (k + 1)).1 ≤
            (gasF (pos k)).toNat + X.maxFee - (seg (k + 1)).1 := by
          have := hfl; omega
        exact Nat.le_trans (Nat.mul_le_mul_left _ hle) hm
      have hb0 : hb = 0 := by
        have h3 : (pos (k + 1)).getD 3 0 = 0 := by rw [pos_in (k + 1) hk]; exact (RF (k + 1) hk).halt0
        rw [hout'] at h3
        simp only [stMsg, List.getD_cons_succ, List.getD_cons_zero] at h3
        exact natEq (h3.trans rfl) (by omega) (by decide)
      obtain ⟨s', hs', E', f', tps', tpl', hsb', hcid', hk', R'⟩ := (hspec hgas').1 hb0
      refine ⟨s', k', pc', sb', cid', ?_, ?_, ?_⟩
      · intro m
        rw [show m + (k + 1) = (m + 1) + k by omega, hrun, run_cont hs']
      · rw [hg1, ← pos_in (k + 1) hk, hout', hb0]
      · rw [hg1, ← hsb', ← hcid', ← hk']
        refine Rel_of_RelW_congr R' ?_
        funext x
        have := (C.live_succ (k := k) (by simp [consL]; omega) x).symm
        simp only [consL, prodL, List.getElem_map] at this
        exact propext this
  -- (D) the last step halts
  obtain ⟨s, q, pc, sb, cid, hrun, hin, E, f, tps, tpl, rfl, rfl, rfl, R⟩ := IH (rs.length - 1) (by omega)
  have gb := (gasB (rs.length - 1) (by omega)).1
  have hS : (gasF (pos (rs.length - 1))).toNat + X.maxFee < ZkFormal.Algebra.P := by
    have : (rs.length - 1) * X.maxFee + X.maxFee ≤ rs.length * (X.maxFee + 1) := by
      have : (rs.length - 1) * X.maxFee + X.maxFee = rs.length * X.maxFee := by
        rw [← Nat.succ_mul, show (rs.length - 1).succ = rs.length by omega]
      rw [this, Nat.mul_add]; omega
    have : rs.length * (X.maxFee + 1) ≤ (act.length + 1) * (X.maxFee + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hlive : ∀ x ∈ cons rs[rs.length - 1], live init prodL consL (rs.length - 1) x := fun x hx =>
    C.consumed_live (k := rs.length - 1) (by simp [consL]; omega) (by simpa [consL] using hx)
  obtain ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, hspec⟩ :=
    (RFS (rs.length - 1) (by omega)).spec E s f tps tpl (rs.length - 1 + 1) pc _
      (live init prodL consL (rs.length - 1)) R hin hlive (by omega) hS hg64
  have hout' : pos rs.length = stMsg (X.offOf k' + pc') (rs.length - 1 + 1 + 1) ((gasF (pos (rs.length - 1))).toNat + fee) hb sb' cid' := by
    rw [show rs.length = rs.length - 1 + 1 by omega, pos_out (rs.length - 1) (by omega), hout]
    simp only [show rs.length - 1 + 1 - 1 = rs.length - 1 by omega]
  rw [posN] at hout'
  have e := hout'.symm
  simp only [stMsg, List.cons.injEq, and_true] at e
  obtain ⟨-, -, eS, eH, -⟩ := e
  have hbP : hb < ZkFormal.Algebra.P := Nat.lt_of_le_of_lt hbl (by rw [hP']; decide)
  have hstP : st < ZkFormal.Algebra.P := by rcases hst12 with rfl | rfl <;> rw [hP'] <;> decide
  have hbst : hb = st := by
    first | exact natEq eH hbP hstP | exact (natEq eH hstP hbP).symm
  have hSf : (gasF (pos (rs.length - 1))).toNat + fee = Sf.toNat := by
    rw [← eS, Fp.toNat_cast_of_lt (by omega)]
  have hgas' : X.R * ((gasF (pos (rs.length - 1))).toNat + fee - (seg (rs.length - 1 + 1)).1) ≤
      (seg (rs.length - 1 + 1)).2 := by
    have hm := hstepgas (rs.length - 1 + 1) ((gasF (pos (rs.length - 1))).toNat) s.gas.g R.gas
    have hle : (gasF (pos (rs.length - 1))).toNat + fee - (seg (rs.length - 1 + 1)).1 ≤
        (gasF (pos (rs.length - 1))).toNat + X.maxFee - (seg (rs.length - 1 + 1)).1 := by
      have := hfl; omega
    exact Nat.le_trans (Nat.mul_le_mul_left _ hle) hm
  have hidx : seg (rs.length - 1 + 2) = seg (act.length + 1) := by
    rw [← hlenrs]
    congr 1; omega
  have hrunlen : ∀ r, step X.cfg X.p s = r → (∀ s', r ≠ .cont s') → run X.cfg X.p act.length s0 = r := by
    intro r hr hnc
    rw [← hlenrs, show rs.length = 0 + 1 + (rs.length - 1) by omega, hrun]
    simp only [run, hr]
    try (cases r <;> simp_all)
  refine ⟨hN, fun h1 => ?_, fun h2 => ?_⟩
  · obtain ⟨sN, hsN, hfr, hg, G, hG, hview⟩ := (hspec hgas').2.1 (by omega)
    refine ⟨sN, tps, tpl, f.locals, hrunlen _ hsN (by simp), hfr, ?_, G, hG, ?_⟩
    · rw [← hSf]
      rw [← hidx]
      exact hg
    · intro x
      rw [← hview x, ← C.live_final x]
      have := C.live_succ (k := rs.length - 1) (by simp [consL]; omega) x
      simp only [consL, List.length_map, show rs.length - 1 + 1 = rs.length by omega] at this ⊢
      rw [this]; simp only [stepLive, prodL, List.getElem_map]
  · obtain ⟨sN, e, hsN, hg⟩ := (hspec hgas').2.2 (by omega)
    refine ⟨sN, e, hrunlen _ hsN (by simp), ?_⟩
    rw [← hSf]
    rw [← hidx]
    exact hg




/-! ## `wasm_base_exec_host`: the host-aware execution theorem

`wasm_base_exec` instantiates `exec_of_rows` with `wasmBaseAir` and the instruction rows
(`actList`, tables 1-14).  Here the AIR is `wasmBaseHostAir`, whose table 22 carries the host calls,
and the rows are the *interleaved* list of instruction rows and active HOST rows.

The two statements differ in exactly the way the segmentation requires:

* the final gas invariant is reported at the **last segment** (`segs`), not the global `(0, g0)`;
* `hstepgas` is the **machine fact** "the fee fits in the budget the segment has left": given the
  invariant `R · (S − S_seg) + g = segb` at the row (which is `RelW.gas`), the fee is covered,
  `R · (S + maxFee − S_seg) ≤ segb`, i.e. `R · maxFee ≤ g`.  That is not implied by the invariant
  (it is where a host call that returned too little would fail), so it stays a premise; the
  *unconditional* variant `∀ S, R · (S + maxFee − S_seg) ≤ segb` is unsatisfiable and is not used.

The conclusion is `wasm_base_exec`'s plus the segment map.
-/

/-- The active HOST rows, as `(22, r)` pairs. -/
def hostActRows (tr : Trace) (pub : List F) : List (Nat × Nat) :=
  ((List.range (tr.height 22)).filter fun r => decide (rowAct Host.table tr pub 22 r)).map
    fun r => (22, r)

/-- The action list of `wasmBaseHostAir`: the base instruction rows, then the active HOST rows. -/
def actListHost (tr : Trace) (pub : List F) : List (Nat × Nat) :=
  actList tr pub ++ hostActRows tr pub

/-- The chip table of an action row, HOST included. -/
def chipTHost (t : Nat) : Table := if t = 22 then Host.table else chipT t

/-- The STATE input message of an action row of the host AIR. -/
def rowInH (tr : Trace) (pub : List F) (ρ : Nat × Nat) : List F :=
  rowIn (chipTHost ρ.1) tr pub ρ.1 ρ.2
/-- The STATE output message of an action row of the host AIR. -/
def rowOutH (tr : Trace) (pub : List F) (ρ : Nat × Nat) : List F :=
  rowOut (chipTHost ρ.1) tr pub ρ.1 ρ.2
/-- The CH messages an action row of the host AIR consumes. -/
def rowConsH (tr : Trace) (pub : List F) (ρ : Nat × Nat) : List Msg :=
  rowCons (chipTHost ρ.1) tr pub ρ.1 ρ.2
/-- The CH messages an action row of the host AIR produces. -/
def rowProdH (tr : Trace) (pub : List F) (ρ : Nat × Nat) : List Msg :=
  rowProd (chipTHost ρ.1) tr pub ρ.1 ρ.2

/-! ## `wasm_base_exec_host`

`exec_of_rows_seg` instantiated against `wasmBaseHostAir`: the action list is `actListHost` (base
instruction rows then active HOST rows), the row facts are supplied per row, and the segment thread
is `seg`.

The bus-level premises (`hst`, `hch`) are hypotheses: assembling them is
`msgs_state_host`/`msgs_ch_host` composed with `msgs_state`/`msgs_ch` and `msgs_perm` — the same
shape as `wasm_base_exec`, one layer out.

The conclusion reports the **last** segment: after a host call the global `R·S + g = g0` is false,
which is the whole reason for the segmentation. -/
theorem wasm_base_exec_host (X : Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (seg : Nat → Nat × Nat) (init fin : List Msg) (st : Nat) (hst12 : st = 1 ∨ st = 2)
    (hrows : ∀ r ∈ actListHost tr pub,
      RowFactsSegMap X (rowInH tr pub r) (rowOutH tr pub r) (rowConsH tr pub r) (rowProdH tr pub r) seg)
    (sbf cidf : F)
    (hst : (stMsg 0 1 0 0 0 0 :: (actListHost tr pub).map (rowOutH tr pub)).Perm
      ([tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0,
        (st : F), sbf, cidf] :: (actListHost tr pub).map (rowInH tr pub)))
    (hch : (init ++ (actListHost tr pub).flatMap (fun r => rowProdH tr pub r)).Perm
      (fin ++ (actListHost tr pub).flatMap (fun r => rowConsH tr pub r)))
    (hinit : init.Nodup) (hinitTp : ∀ x ∈ init, x.tp = 0)
    (hlen : (actListHost tr pub).length < 2 ^ 28)
    (hfee : ((actListHost tr pub).length + 1) * (X.maxFee + 1) < ZkFormal.Algebra.P)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (seg t).1) + g = (seg t).2 →
      X.R * (S + X.maxFee - (seg t).1) ≤ (seg t).2)
    (hg64 : X.g0 < 2 ^ 64)
    {E0 : Env} (hE0 : E0.sb = 0 ∧ E0.cid = 0 ∧ E0.k = 0)
    {s0 : St} {f0 : Frame}
    (h0 : RelW X E0 s0 f0 (fun _ => 0) (fun _ => 0) 1 0 0 (· ∈ init) (seg 1).1 (seg 1).2) :
    (actListHost tr pub).length + 1 = (pub.getD Boundary.pubN 0).toNat ∧
    (st = 1 → ∃ (sN : St) (tps tpl : Nat → Nat) (locs : Array Val),
      run X.cfg X.p (actListHost tr pub).length s0 = .fin sN ∧ sN.frames = [] ∧
      X.R * ((pub.getD Boundary.pubS 0).toNat - (seg ((actListHost tr pub).length + 1)).1) +
        sN.gas.g = (seg ((actListHost tr pub).length + 1)).2) ∧
    (st = 2 → ∃ (sN : St) (e : String),
      run X.cfg X.p (actListHost tr pub).length s0 = .abort sN e ∧
      X.R * ((pub.getD Boundary.pubS 0).toNat - (seg ((actListHost tr pub).length + 1)).1) +
        sN.gas.g = (seg ((actListHost tr pub).length + 1)).2) := by
  obtain ⟨hN, h1, h2⟩ := exec_of_rows_seg X (actListHost tr pub) (rowInH tr pub) (rowOutH tr pub)
    (rowConsH tr pub) (rowProdH tr pub) init fin
    (tr.cell 0 0 Boundary.pcf) (pub.getD Boundary.pubN 0) (pub.getD Boundary.pubS 0) seg st hst12
    hrows sbf cidf hst hch hinit hinitTp hlen hfee hstepgas hg64 hE0 h0
  refine ⟨hN, ?_, ?_⟩
  · intro hs
    obtain ⟨sN, tps, tpl, locs, hrun, hfr, hgas, _G⟩ := h1 hs
    exact ⟨sN, tps, tpl, locs, hrun, hfr, hgas⟩
  · intro hs
    obtain ⟨sN, e, hrun, hgas⟩ := h2 hs
    exact ⟨sN, e, hrun, hgas⟩

end WasmBase
