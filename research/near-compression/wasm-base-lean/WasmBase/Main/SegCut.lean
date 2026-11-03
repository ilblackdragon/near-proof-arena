import WasmBase.Main.SegHarness
import NearSpecV3.Wasm.Segment
import NearSpecV3.E2E.CallMachine

/-!
# WasmBase.Main.SegCut — the execution theorem for a segment cut mid-call (E2E M4)

`Main/SegHarness.lean:exec_of_rows_seg` proves a whole call from function entry: the STATE bus
starts at `stMsg 0 1 0 0 0 0`, every boundary-produced channel message has `tp = 0`, and the last
row halts.  At M4 a call is proved as a chain of **segments**, each cut between two steps.  This
file proves the execution side of one segment, and the chaining.

* `Bnd X sg s t S m L` — the **boundary relation**: the STATE message `m` is
  `stMsg (offOf k + pc) (t + 1) S 0 sb cid` and the spec state `s` is related (`Rel`) at time
  `t + 1` to exactly the channel messages `L`, in gas segment `sg (t + 1)`.  The frame
  environment is arbitrary (any frame stack, not only the entry frame).
* `exec_of_rows_cut` — `exec_of_rows_seg` from an arbitrary boundary: the STATE permutation starts
  at `m0` (with `Bnd … s0 t0 S0 m0 init`), the boundary-produced channel messages have `tp ≤ t0`,
  timestamps are global (the first row has `ts = t0 + 1`), and the final STATE message may have
  `halted = 0` (a cut), giving `seg n s0 = .cont sN` and `Bnd … sN (t0 + n) Sf fin`, or
  `halted = 1/2`, giving `.fin`/`.abort` as in `exec_of_rows_seg`.
* `foldSegments_of_bnd`, `CutSeg`, `cuts_foldSegments` — chaining: a list of cut segments whose
  boundaries match gives `foldSegments … ks s0 = .cont sN`, and `cuts_csteps` lifts it to the call
  machine (`csteps_foldSegments`); `cuts_halt` ends the chain in a returning/trapping segment.
* `RelW.relabel`, `Bnd.relabel` — the boundary relabelling: activation ids of the live frames to
  depths, live locals spaces and call records relabelled the same way, **dead locals spaces
  dropped** (they could collide with the new depth labels, so the next segment must not re-produce
  them).
-/

namespace WasmBase

open ZkFormal.Algebra
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-- **The boundary relation** of a cut.  `m` is the STATE message at the cut (not halted) and `L`
the live channel messages there; `s` is related to them at time `t + 1` (the timestamp the next row
reads), in the gas segment `sg (t + 1)`. -/
def Bnd (X : Ctx) (sg : Nat → Nat × Nat) (s : St) (t S : Nat) (m : List F) (L : List Msg) : Prop :=
  ∃ k pc sb cid, m = stMsg (X.offOf k + pc) (t + 1) S 0 sb cid ∧
    Rel X s (t + 1) k pc S sb cid (· ∈ L) (sg (t + 1)).1 (sg (t + 1)).2

/-- A `RelW` at a general frame environment gives the boundary relation (the form the brief states
the initial hypothesis in). -/
theorem Bnd.of_relW {X : Ctx} {sg : Nat → Nat × Nat} {E : Env} {s : St} {f : Frame}
    {tps tpl : Nat → Nat} {t pc S : Nat} {L : List Msg}
    (h : RelW X E s f tps tpl (t + 1) pc S (· ∈ L) (sg (t + 1)).1 (sg (t + 1)).2) :
    Bnd X sg s t S (stMsg (X.offOf E.k + pc) (t + 1) S 0 E.sb E.cid) L :=
  ⟨E.k, pc, E.sb, E.cid, rfl, E, f, tps, tpl, rfl, rfl, rfl, h⟩

theorem Rel.congr_live {X : Ctx} {s : St} {t k pc S sb cid : Nat} {live live' : Msg → Prop}
    {a b : Nat} (h : Rel X s t k pc S sb cid live a b) (e : live = live') :
    Rel X s t k pc S sb cid live' a b := e ▸ h

/-- `seg` one step further on a non-terminal step. -/
theorem seg_succ_cont {cfg : NearCfg} {p : Prepared} {k : Nat} {s0 s s' : St}
    (h : NearSpecV3.Wasm.seg cfg p k s0 = .cont s) (hs : step cfg p s = .cont s') :
    NearSpecV3.Wasm.seg cfg p (k + 1) s0 = .cont s' := by
  rw [seg_add, h, Res.cont_bind]
  simp only [NearSpecV3.Wasm.seg, hs, Res.cont_bind]

/-- `seg` ending on a terminal step. -/
theorem seg_succ_stop {cfg : NearCfg} {p : Prepared} {k : Nat} {s0 s : St} {r : Res}
    (h : NearSpecV3.Wasm.seg cfg p k s0 = .cont s) (hs : step cfg p s = r) :
    NearSpecV3.Wasm.seg cfg p (k + 1) s0 = r := by
  rw [seg_add, h, Res.cont_bind]
  simp only [NearSpecV3.Wasm.seg, hs, Res.bind_cont]

/-- A `seg` that reaches a cut lets `run` continue from it. -/
theorem run_of_seg_cont {cfg : NearCfg} {p : Prepared} {n : Nat} {s0 sN : St}
    (h : NearSpecV3.Wasm.seg cfg p n s0 = .cont sN) (m : Nat) :
    run cfg p (n + m) s0 = run cfg p m sN := by
  rw [run_seg, h, Res.cont_bind]

/-- A `seg` that ends in a terminal result is that `run`'s result. -/
theorem run_of_seg_stop {cfg : NearCfg} {p : Prepared} {n : Nat} {s0 : St} {r : Res}
    (h : NearSpecV3.Wasm.seg cfg p n s0 = r) (hnc : ∀ s', r ≠ .cont s') :
    run cfg p n s0 = r := by
  have e := run_seg cfg p n 0 s0
  rw [Nat.add_zero, h] at e
  rw [e]
  cases r with
  | cont s' => exact absurd rfl (hnc s')
  | _ => rfl

/-! ## The execution theorem for a cut segment -/

section
variable (X : Ctx) {ρ : Type} [DecidableEq ρ] (act : List ρ) (inS outS : ρ → List F)
  (cons prod : ρ → List Msg) (init fin : List Msg) (pcf N Sf : F)

/-- **`exec_of_rows_cut`.**  A segment of `n = act.length` rows from the boundary `(s0, m0, init)`
at time `t0` (its first row reads `ts = t0 + 1`) to the final STATE message
`[pcf, N, Sf, st, sbf, cidf]`.

Hypotheses beyond `exec_of_rows_seg`'s, and why:
* `h0 : Bnd X sg s0 t0 S0 m0 init` replaces `stMsg 0 1 0 0 0 0` and the entry `RelW`;
* `hinitTp : x.tp ≤ t0` replaces `x.tp = 0` (the boundary produces live messages with their real,
  global producer times);
* `ht : t0 + n + 1 + (2^30 + 2^16) < P` — the time-check `tp + 1 + d = ts` (`d < 2^30 + 2^16`,
  `RowFacts.consT`) must not wrap: `tp ≤ t0 + n` and `ts ≤ t0 + n`, so `tp + 1 + d < P`.  It also
  bounds the STATE timestamps (`t0 + n + 1 < P`) and the chain length (`n < P`);
* `hfee : S0 + (n + 1) · (maxFee + 1) < P` — the gas field starts at `S0`, not `0`.

Conclusion: `N = t0 + n + 1`; `halted = 0` gives the cut (`seg n s0 = .cont sN`, `run` continues
from `sN`, and `Bnd … sN (t0 + n) Sf.toNat final fin`: the final live set is exactly `fin`);
`halted = 1/2` give `exec_of_rows_seg`'s `.fin`/`.abort` conclusions, for `seg` and `run`. -/
theorem exec_of_rows_cut (sg : Nat → Nat × Nat) (st : Nat) (hst2 : st ≤ 2)
    (hrows : ∀ r ∈ act, RowFactsSegMap X (inS r) (outS r) (cons r) (prod r) sg)
    (t0 S0 : Nat) (m0 : List F) (sbf cidf : F)
    (hst : (m0 :: act.map outS).Perm ([pcf, N, Sf, (st : F), sbf, cidf] :: act.map inS))
    (hch : (init ++ act.flatMap prod).Perm (fin ++ act.flatMap cons))
    (hinit : init.Nodup) (hinitTp : ∀ x ∈ init, x.tp ≤ t0)
    (ht : t0 + act.length + 1 + (2 ^ 30 + 2 ^ 16) < ZkFormal.Algebra.P)
    (hfee : S0 + (act.length + 1) * (X.maxFee + 1) < ZkFormal.Algebra.P)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64)
    {s0 : St} (h0 : Bnd X sg s0 t0 S0 m0 init) :
    N.toNat = t0 + act.length + 1 ∧
    (st = 0 → ∃ sN, NearSpecV3.Wasm.seg X.cfg X.p act.length s0 = .cont sN ∧
      (∀ m, run X.cfg X.p (act.length + m) s0 = run X.cfg X.p m sN) ∧
      Bnd X sg sN (t0 + act.length) Sf.toNat [pcf, N, Sf, ((0 : Nat) : F), sbf, cidf] fin) ∧
    (st = 1 → ∃ sN tps tpl locs, NearSpecV3.Wasm.seg X.cfg X.p act.length s0 = .fin sN ∧
      run X.cfg X.p act.length s0 = .fin sN ∧ sN.frames = [] ∧
      X.R * (Sf.toNat - (sg (t0 + act.length + 1)).1) + sN.gas.g = (sg (t0 + act.length + 1)).2 ∧
      ∃ G : Msg → Prop, (∀ x, G x → x.space ≠ 0 ∧ x.space ≠ 16) ∧
      ∀ x, x ∈ fin ↔ x ∈ stackView sN.stack tps ∨ x ∈ localView 16 locs tpl ∨ G x) ∧
    (st = 2 → ∃ sN e, NearSpecV3.Wasm.seg X.cfg X.p act.length s0 = .abort sN e ∧
      run X.cfg X.p act.length s0 = .abort sN e ∧
      X.R * (Sf.toNat - (sg (t0 + act.length + 1)).1) + sN.gas.g = (sg (t0 + act.length + 1)).2) := by
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
    exact (hrows r hr).tsOut
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
      RowFactsSeg X (inS rs[k]) (outS rs[k]) (cons rs[k]) (prod rs[k])
        (sg (t0 + k + 1)) (sg (t0 + k + 1 + 1)) :=
    fun k hk => by
      have e : lvl (inS rs[k]) = ((t0 + k + 1 : Nat) : F) := lvlk k hk
      have h := hrows rs[k] (hmem k hk)
      unfold RowFactsSegMap at h
      rwa [e, Fp.toNat_cast_of_lt (by omega)] at h
  have RF : ∀ k (hk : k < rs.length), RowFactsFlat X (inS rs[k]) (outS rs[k]) (cons rs[k]) (prod rs[k]) :=
    fun k hk => (RFS k hk).toFlat
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
        (sg (t0 + k + 1)).1 (sg (t0 + k + 1)).2 := by
    intro k
    induction k with
    | zero =>
      intro _ _
      refine ⟨s0, k0, pc0, sb0, cid0, rfl, ?_, ?_⟩
      · rw [gas0, pos0]
      · rw [gas0]
        exact R0.congr_live (by funext x; simp [live, prodBefore, consBefore])
    | succ k ih =>
      intro hk hcase
      obtain ⟨s, q, pc, sb, cid, hrun, hin, E, f, tps, tpl, rfl, rfl, rfl, R⟩ := ih (by omega) (Or.inl (by omega))
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
          (live init prodL consL k) R (by rw [← pos_in k (by omega)]; exact hin) hlive (by omega) hS hg64
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
      obtain ⟨s', hs', E', f', tps', tpl', hsb', hcid', hk', R'⟩ := (hspec hgas').1 hb0
      refine ⟨s', k', pc', sb', cid', seg_succ_cont hrun hs', ?_, ?_⟩
      · rw [hg1, hout', hb0, show t0 + (k + 1) + 1 = t0 + k + 1 + 1 by omega]
      · rw [hg1, show t0 + (k + 1) + 1 = t0 + k + 1 + 1 by omega, ← hsb', ← hcid', ← hk']
        refine Rel_of_RelW_congr R' ?_
        funext x
        have := (C.live_succ (k := k) (by simp [consL]; omega) x).symm
        simp only [consL, prodL, List.getElem_map] at this
        exact propext this
  refine ⟨hN, fun h0 => ?_, ?_⟩
  -- (D0) a cut: the state after the last row is related to the final boundary
  · obtain ⟨s, q, pc, sb, cid, hrun, hin, R⟩ := IH rs.length (Nat.le_refl _) (Or.inr h0)
    rw [hlenrs] at hrun
    refine ⟨s, hrun, run_of_seg_cont hrun, q, pc, sb, cid, ?_, ?_⟩
    · subst h0; rw [← posN, hin, gasN, hlenrs]
    · rw [← gasN, ← hlenrs]
      refine R.congr_live ?_
      funext x
      have := C.live_final x
      simp only [consL, List.length_map] at this
      exact propext this
  -- (D) the last step halts
  have hst12 : st ≠ 0 → 0 < rs.length := by
    intro hne
    refine Nat.pos_of_ne_zero fun h0' => ?_
    have := enil h0'
    simp only [stMsg, List.cons.injEq] at this
    have e := this.2.2.2.1
    have hstP : st < ZkFormal.Algebra.P := by rw [hP']; omega
    have := natEq (L := 0) (R := st) e (by rw [hP']; decide) hstP
    omega
  by_cases hne : st = 0
  · exact ⟨fun h1 => by omega, fun h2 => by omega⟩
  have hpos := hst12 hne
  obtain ⟨s, q, pc, sb, cid, hrun, hin, E, f, tps, tpl, rfl, rfl, rfl, R⟩ :=
    IH (rs.length - 1) (by omega) (Or.inl (by omega))
  have gb := gasB (rs.length - 1) (by omega)
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
    (RFS (rs.length - 1) (by omega)).spec E s f tps tpl (t0 + (rs.length - 1) + 1) pc _
      (live init prodL consL (rs.length - 1)) R (by rw [← pos_in _ (by omega)]; exact hin) hlive (by omega) hS hg64
  have hout' : pos rs.length = stMsg (X.offOf k' + pc') (t0 + (rs.length - 1) + 1 + 1)
      ((gasF (pos (rs.length - 1))).toNat + fee) hb sb' cid' := by
    rw [show rs.length = rs.length - 1 + 1 by omega, pos_out (rs.length - 1) (by omega), hout]
    simp only [show rs.length - 1 + 1 - 1 = rs.length - 1 by omega]
  rw [posN] at hout'
  have e := hout'.symm
  simp only [stMsg, List.cons.injEq, and_true] at e
  obtain ⟨-, -, eS, eH, -⟩ := e
  have hbP : hb < ZkFormal.Algebra.P := Nat.lt_of_le_of_lt hbl (by rw [hP']; decide)
  have hstP : st < ZkFormal.Algebra.P := by rw [hP']; omega
  have hbst : hb = st := natEq eH hbP hstP
  have hSf : (gasF (pos (rs.length - 1))).toNat + fee = Sf.toNat := by
    rw [← eS, Fp.toNat_cast_of_lt (by omega)]
  have hgas' : X.R * ((gasF (pos (rs.length - 1))).toNat + fee - (sg (t0 + (rs.length - 1) + 1)).1) ≤
      (sg (t0 + (rs.length - 1) + 1)).2 := by
    have hm := hstepgas (t0 + (rs.length - 1) + 1) ((gasF (pos (rs.length - 1))).toNat) s.gas.g R.gas
    have hle : (gasF (pos (rs.length - 1))).toNat + fee - (sg (t0 + (rs.length - 1) + 1)).1 ≤
        (gasF (pos (rs.length - 1))).toNat + X.maxFee - (sg (t0 + (rs.length - 1) + 1)).1 := by
      have := hfl; omega
    exact Nat.le_trans (Nat.mul_le_mul_left _ hle) hm
  have hidx : sg (t0 + (rs.length - 1) + 1 + 1) = sg (t0 + act.length + 1) := by
    rw [← hlenrs]; congr 1; omega
  have hseglen : ∀ r, step X.cfg X.p s = r →
      NearSpecV3.Wasm.seg X.cfg X.p act.length s0 = r := by
    intro r hr
    rw [← hlenrs, show rs.length = rs.length - 1 + 1 by omega]
    exact seg_succ_stop hrun hr
  refine ⟨fun h1 => ?_, fun h2 => ?_⟩
  · obtain ⟨sN, hsN, hfr, hg, G, hG, hview⟩ := (hspec hgas').2.1 (by omega)
    have hs := hseglen _ hsN
    refine ⟨sN, tps, tpl, f.locals, hs, run_of_seg_stop hs (by simp), hfr, ?_, G, hG, ?_⟩
    · rw [← hSf, ← hidx]; exact hg
    · intro x
      rw [← hview x, ← C.live_final x]
      have := C.live_succ (k := rs.length - 1) (by simp [consL]; omega) x
      simp only [consL, List.length_map, show rs.length - 1 + 1 = rs.length by omega] at this ⊢
      rw [this]; simp only [stepLive, prodL, List.getElem_map]
  · obtain ⟨sN, e, hsN, hg⟩ := (hspec hgas').2.2 (by omega)
    have hs := hseglen _ hsN
    refine ⟨sN, e, hs, run_of_seg_stop hs (by simp), ?_⟩
    rw [← hSf, ← hidx]; exact hg
end

/-! ## Chaining segments

The spec side: a list of segments, each taking the boundary relation at point `j` to the one at
point `j + 1`, runs as `foldSegments`.  Then the trace side: a list of `CutSeg`s (one segment's rows
and bus facts each), whose boundaries are the points of a sequence `bs`, gives exactly such a list. -/

/-- The boundary relation is about the *set* of live messages. -/
theorem Bnd.congr {X : Ctx} {sg : Nat → Nat × Nat} {s : St} {t S : Nat} {m : List F} {L L' : List Msg}
    (h : Bnd X sg s t S m L) (e : ∀ x, x ∈ L ↔ x ∈ L') : Bnd X sg s t S m L' := by
  obtain ⟨k, pc, sb, cid, hm, R⟩ := h
  exact ⟨k, pc, sb, cid, hm, R.congr_live (funext fun x => propext (e x))⟩

/-- **Spec-side chaining.**  If segment `j` (length `ks[j]`) takes every state satisfying `B j` to a
cut state satisfying `B (j + 1)`, then the segments `ks` run as `foldSegments` from `B 0` to
`B ks.length`. -/
theorem foldSegments_of_steps (cfg : NearCfg) (p : Prepared) :
    ∀ (ks : List Nat) (B : Nat → St → Prop) (s : St), B 0 s →
      (∀ j (hj : j < ks.length) (s : St), B j s →
        ∃ s', NearSpecV3.Wasm.seg cfg p ks[j] s = .cont s' ∧ B (j + 1) s') →
      ∃ sN, foldSegments cfg p ks s = .cont sN ∧ B ks.length sN
  | [], _, s, h0, _ => ⟨s, rfl, h0⟩
  | k :: ks, B, s, h0, hstep => by
    obtain ⟨s1, h1, hB1⟩ := hstep 0 (by simp) s h0
    obtain ⟨sN, hN, hBN⟩ := foldSegments_of_steps cfg p ks (fun j => B (j + 1)) s1 hB1
      (fun j hj s hs => hstep (j + 1) (by simp; omega) s hs)
    refine ⟨sN, ?_, by simpa using hBN⟩
    have h1' : NearSpecV3.Wasm.seg cfg p k s = .cont s1 := h1
    simp only [foldSegments, h1', Res.cont_bind, hN]

/-- A last segment that stops after the cuts. -/
theorem foldSegments_append_stop {cfg : NearCfg} {p : Prepared} {ks : List Nat} {k : Nat} {s s' : St}
    {r : Res} (h : foldSegments cfg p ks s = .cont s') (hl : NearSpecV3.Wasm.seg cfg p k s' = r) :
    foldSegments cfg p (ks ++ [k]) s = r := by
  rw [foldSegments_eq_seg, List.sum_append, seg_add, ← foldSegments_eq_seg, h, Res.cont_bind]
  simpa using hl

/-- A boundary point: time `t` (the cut is between the rows at `ts = t` and `ts = t + 1`), gas
units `S`, STATE message `m`, live channel messages `L`. -/
structure BndPt where
  t : Nat
  S : Nat
  m : List F
  L : List Msg

/-- **One segment of the trace**: the hypotheses of `exec_of_rows_cut`, bundled.  `st` is the final
`halted` flag: `0` for a cut. -/
structure CutSeg (X : Ctx) (sg : Nat → Nat × Nat) (ρ : Type) [DecidableEq ρ] where
  act : List ρ
  inS : ρ → List F
  outS : ρ → List F
  cons : ρ → List Msg
  prod : ρ → List Msg
  init : List Msg
  fin : List Msg
  pcf : F
  N : F
  Sf : F
  sbf : F
  cidf : F
  st : Nat
  t0 : Nat
  S0 : Nat
  m0 : List F
  hst2 : st ≤ 2
  hrows : ∀ r ∈ act, RowFactsSegMap X (inS r) (outS r) (cons r) (prod r) sg
  hst : (m0 :: act.map outS).Perm ([pcf, N, Sf, (st : F), sbf, cidf] :: act.map inS)
  hch : (init ++ act.flatMap prod).Perm (fin ++ act.flatMap cons)
  hinit : init.Nodup
  hinitTp : ∀ x ∈ init, x.tp ≤ t0
  ht : t0 + act.length + 1 + (2 ^ 30 + 2 ^ 16) < ZkFormal.Algebra.P
  hfee : S0 + (act.length + 1) * (X.maxFee + 1) < ZkFormal.Algebra.P

namespace CutSeg
variable {X : Ctx} {sg : Nat → Nat × Nat} {ρ : Type} [DecidableEq ρ]

/-- The segment's length (rows = spec steps). -/
def len (c : CutSeg X sg ρ) : Nat := c.act.length

/-- The segment's start boundary. -/
def start (c : CutSeg X sg ρ) : BndPt := ⟨c.t0, c.S0, c.m0, c.init⟩

/-- The segment's end boundary (for a cut, `st = 0`). -/
def stop (c : CutSeg X sg ρ) : BndPt :=
  ⟨c.t0 + c.act.length, c.Sf.toNat, [c.pcf, c.N, c.Sf, ((0 : Nat) : F), c.sbf, c.cidf], c.fin⟩

/-- A cut segment takes its start boundary to its end boundary. -/
theorem cut (c : CutSeg X sg ρ) (hc : c.st = 0)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64) {s0 : St} (h0 : Bnd X sg s0 c.t0 c.S0 c.m0 c.init) :
    ∃ sN, NearSpecV3.Wasm.seg X.cfg X.p c.len s0 = .cont sN ∧
      Bnd X sg sN c.stop.t c.stop.S c.stop.m c.stop.L := by
  obtain ⟨sN, h1, -, h2⟩ := (exec_of_rows_cut X c.act c.inS c.outS c.cons c.prod c.init c.fin c.pcf c.N
    c.Sf sg c.st c.hst2 c.hrows c.t0 c.S0 c.m0 c.sbf c.cidf c.hst c.hch c.hinit c.hinitTp c.ht c.hfee
    hstepgas hg64 h0).2.1 hc
  exact ⟨sN, h1, h2⟩

end CutSeg

/-- The boundary relation at a point. -/
def BndAt (X : Ctx) (sg : Nat → Nat × Nat) (b : BndPt) (s : St) : Prop := Bnd X sg s b.t b.S b.m b.L

/-- Segment `c` sits between boundary points `b` and `b'`: same times, gas units and STATE
messages, and the same live sets (as sets). -/
def CutSeg.Between {X : Ctx} {sg : Nat → Nat × Nat} {ρ : Type} [DecidableEq ρ] (c : CutSeg X sg ρ)
    (b b' : BndPt) : Prop :=
  c.start.t = b.t ∧ c.start.S = b.S ∧ c.start.m = b.m ∧ (∀ x, x ∈ c.start.L ↔ x ∈ b.L) ∧
  c.stop.t = b'.t ∧ c.stop.S = b'.S ∧ c.stop.m = b'.m ∧ (∀ x, x ∈ c.stop.L ↔ x ∈ b'.L)

theorem CutSeg.bnd_start {X : Ctx} {sg : Nat → Nat × Nat} {ρ : Type} [DecidableEq ρ]
    {c : CutSeg X sg ρ} {b : BndPt} {s : St}
    (e1 : c.start.t = b.t) (e2 : c.start.S = b.S) (e3 : c.start.m = b.m)
    (e4 : ∀ x, x ∈ c.start.L ↔ x ∈ b.L) (h : BndAt X sg b s) :
    Bnd X sg s c.t0 c.S0 c.m0 c.init := by
  have := Bnd.congr h (fun x => (e4 x).symm)
  simp only [CutSeg.start] at e1 e2 e3
  unfold BndAt at this
  rw [← e1, ← e2, ← e3] at this
  exact this

theorem CutSeg.Between.run {X : Ctx} {sg : Nat → Nat × Nat} {ρ : Type} [DecidableEq ρ]
    {c : CutSeg X sg ρ} {b b' : BndPt} (hb : c.Between b b') (hc : c.st = 0)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64) {s : St} (h : BndAt X sg b s) :
    ∃ s', NearSpecV3.Wasm.seg X.cfg X.p c.len s = .cont s' ∧ BndAt X sg b' s' := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hb
  obtain ⟨s', h1, h2⟩ := c.cut hc hstepgas hg64 (CutSeg.bnd_start e1 e2 e3 e4 h)
  refine ⟨s', h1, ?_⟩
  have := Bnd.congr h2 e8
  unfold BndAt; rw [← e5, ← e6, ← e7]; exact this

/-- **Trace-side chaining.**  Cut segments `cs`, segment `i` between boundary points `bs i` and
`bs (i + 1)`: from a state related at `bs 0`, `foldSegments` over their lengths reaches a state
related at `bs cs.length`. -/
theorem cuts_foldSegments (X : Ctx) (sg : Nat → Nat × Nat) {ρ : Type} [DecidableEq ρ]
    (cs : List (CutSeg X sg ρ)) (bs : Nat → BndPt)
    (hcut : ∀ c ∈ cs, c.st = 0)
    (hlink : ∀ i (hi : i < cs.length), cs[i].Between (bs i) (bs (i + 1)))
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64) {s0 : St} (h0 : BndAt X sg (bs 0) s0) :
    ∃ sN, foldSegments X.cfg X.p (cs.map CutSeg.len) s0 = .cont sN ∧ BndAt X sg (bs cs.length) sN := by
  obtain ⟨sN, h1, h2⟩ := foldSegments_of_steps X.cfg X.p (cs.map CutSeg.len)
    (fun j s => BndAt X sg (bs j) s) s0 h0 (fun j hj s hs => by
      simp only [List.length_map] at hj
      simp only [List.getElem_map]
      exact (hlink j hj).run (hcut _ (List.getElem_mem hj)) hstepgas hg64 hs)
  exact ⟨sN, h1, by simpa using h2⟩

/-- **The chain, ending in a halting segment.**  After the cuts `cs`, a last segment `cl` from
`bs cs.length` whose final STATE message is halted (`st = 1`, return; `st = 2`, trap): the whole
`foldSegments` ends in `.fin`/`.abort`, with `exec_of_rows_cut`'s final facts. -/
theorem cuts_halt (X : Ctx) (sg : Nat → Nat × Nat) {ρ : Type} [DecidableEq ρ]
    (cs : List (CutSeg X sg ρ)) (bs : Nat → BndPt) (cl : CutSeg X sg ρ)
    (hcut : ∀ c ∈ cs, c.st = 0)
    (hlink : ∀ i (hi : i < cs.length), cs[i].Between (bs i) (bs (i + 1)))
    (hlast : cl.start.t = (bs cs.length).t ∧ cl.start.S = (bs cs.length).S ∧
      cl.start.m = (bs cs.length).m ∧ (∀ x, x ∈ cl.start.L ↔ x ∈ (bs cs.length).L))
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64) {s0 : St} (h0 : BndAt X sg (bs 0) s0) :
    (cl.st = 1 → ∃ sN tps tpl locs, foldSegments X.cfg X.p (cs.map CutSeg.len ++ [cl.len]) s0 = .fin sN ∧
      sN.frames = [] ∧
      X.R * (cl.Sf.toNat - (sg (cl.t0 + cl.len + 1)).1) + sN.gas.g = (sg (cl.t0 + cl.len + 1)).2 ∧
      ∃ G : Msg → Prop, (∀ x, G x → x.space ≠ 0 ∧ x.space ≠ 16) ∧
      ∀ x, x ∈ cl.fin ↔ x ∈ stackView sN.stack tps ∨ x ∈ localView 16 locs tpl ∨ G x) ∧
    (cl.st = 2 → ∃ sN e, foldSegments X.cfg X.p (cs.map CutSeg.len ++ [cl.len]) s0 = .abort sN e ∧
      X.R * (cl.Sf.toNat - (sg (cl.t0 + cl.len + 1)).1) + sN.gas.g = (sg (cl.t0 + cl.len + 1)).2) := by
  obtain ⟨s1, h1, hB⟩ := cuts_foldSegments X sg cs bs hcut hlink hstepgas hg64 h0
  obtain ⟨e1, e2, e3, e4⟩ := hlast
  obtain ⟨-, -, hf, ha⟩ := exec_of_rows_cut X cl.act cl.inS cl.outS cl.cons cl.prod cl.init cl.fin cl.pcf
    cl.N cl.Sf sg cl.st cl.hst2 cl.hrows cl.t0 cl.S0 cl.m0 cl.sbf cl.cidf cl.hst cl.hch cl.hinit cl.hinitTp
    cl.ht cl.hfee hstepgas hg64 (CutSeg.bnd_start e1 e2 e3 e4 hB)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨sN, tps, tpl, locs, hs, -, hfr, hg, G, hG, hv⟩ := hf h
    exact ⟨sN, tps, tpl, locs, foldSegments_append_stop h1 hs, hfr, hg, G, hG, hv⟩
  · obtain ⟨sN, e, hs, -, hg⟩ := ha h
    exact ⟨sN, e, foldSegments_append_stop h1 hs, hg⟩

/-! ## On the call machine -/

open NearSpecV3.Wasm.CallCut in
/-- **The cuts as a call-machine run** (`csteps_foldSegments`): an `inCall` configuration at a state
related at `bs 0` with at least `Σ len` fuel moves to one at a state related at `bs cs.length`. -/
theorem cuts_csteps (X : Ctx) (sg : Nat → Nat × Nat) {ρ : Type} [DecidableEq ρ]
    (q : CallArgs) (hq : q.cfg = X.cfg) (k : EntK)
    (cs : List (CutSeg X sg ρ)) (bs : Nat → BndPt)
    (hcut : ∀ c ∈ cs, c.st = 0)
    (hlink : ∀ i (hi : i < cs.length), cs[i].Between (bs i) (bs (i + 1)))
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64) {s0 : St} (h0 : BndAt X sg (bs 0) s0)
    (n : Nat) (hn : (cs.map CutSeg.len).sum ≤ n) :
    ∃ sN, CSteps q (.ent X.p k (.cont s0) n) (.ent X.p k (.cont sN) (n - (cs.map CutSeg.len).sum)) ∧
      BndAt X sg (bs cs.length) sN := by
  obtain ⟨sN, h1, h2⟩ := cuts_foldSegments X sg cs bs hcut hlink hstepgas hg64 h0
  rw [← hq] at h1
  exact ⟨sN, csteps_foldSegments q X.p k _ s0 sN n h1 hn, h2⟩

open NearSpecV3.Wasm.CallCut in
/-- **The call's result from the cut** (`cden_foldSegments`): from an `inCall` configuration at a
state related at `bs 0`, the call's result is the result from the last cut state. -/
theorem cuts_cden (X : Ctx) (sg : Nat → Nat × Nat) {ρ : Type} [DecidableEq ρ]
    (q : CallArgs) (hq : q.cfg = X.cfg) (k : EntK)
    (cs : List (CutSeg X sg ρ)) (bs : Nat → BndPt)
    (hcut : ∀ c ∈ cs, c.st = 0)
    (hlink : ∀ i (hi : i < cs.length), cs[i].Between (bs i) (bs (i + 1)))
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64) {s0 : St} (h0 : BndAt X sg (bs 0) s0) (m : Nat) :
    ∃ sN, cden q (.ent X.p k (.cont s0) ((cs.map CutSeg.len).sum + m)) = cden q (.ent X.p k (.cont sN) m) ∧
      BndAt X sg (bs cs.length) sN := by
  obtain ⟨sN, h1, h2⟩ := cuts_foldSegments X sg cs bs hcut hlink hstepgas hg64 h0
  rw [← hq] at h1
  refine ⟨sN, ?_, h2⟩
  rw [cden_foldSegments q X.p k _ s0 m, h1]

#print axioms exec_of_rows_cut
#print axioms cuts_foldSegments
#print axioms cuts_halt
#print axioms cuts_csteps
#print axioms cuts_cden

/-! ## Relabelling activation ids to depths at a cut

The segment AIR relabels the activation ids of the live frames to their **depths** (0 for the entry
frame, 1, 2, … up the frame stack) at every cut, so the boundary is a function of the spec state.
`RelW.relabel` proves the relation survives: relabel the locals spaces `16 + cid` of the live frames
and the call records (space 4: slot = callee id, `l2` = caller id) by `σ` (the depth map), drop the
messages of dead locals spaces (returned activations, `deadSp`), keep everything else.  The relabelled
environment has `cid = rest.length`, its caller chain has ids `sv'.length - 1 - i` (depths), and it
has no dead spaces left. -/

/-- Relabel a message's activation ids by `σ`: call records (space 4) at slot and caller id, locals
spaces `16 + c` to `16 + σ c`; other spaces unchanged. -/
def rlMsg (σ : Nat → Nat) (x : Msg) : Msg :=
  if x.space = 4 then { x with slot := σ x.slot, l2 := σ x.l2 }
  else if 16 ≤ x.space then { x with space := 16 + σ (x.space - 16) } else x

/-- `x` is in no locals space, or in the locals space of an activation in `A`. -/
def keepA (A : List Nat) (x : Msg) : Prop := 16 ≤ x.space → x.space - 16 ∈ A

instance (A : List Nat) : DecidablePred (keepA A) := fun x => by unfold keepA; infer_instance

/-- The relabelled live set: images of the kept live messages. -/
def relabelLive (σ : Nat → Nat) (A : List Nat) (L : Msg → Prop) : Msg → Prop :=
  fun y => ∃ x, L x ∧ keepA A x ∧ y = rlMsg σ x

theorem rlMsg_low {σ : Nat → Nat} {x : Msg} (h4 : x.space ≠ 4) (h16 : x.space < 16) : rlMsg σ x = x := by
  simp only [rlMsg, h4, if_false, show ¬ 16 ≤ x.space by omega]

theorem rlMsg_space (σ : Nat → Nat) (x : Msg) :
    (rlMsg σ x).space = if x.space = 4 then 4 else if 16 ≤ x.space then 16 + σ (x.space - 16) else x.space := by
  unfold rlMsg; split
  · rename_i h; simp [h]
  · split <;> rfl

theorem relabel_low {σ : Nat → Nat} {A : List Nat} {L : Msg → Prop} {y : Msg} (h4 : y.space ≠ 4)
    (h16 : y.space < 16) : relabelLive σ A L y ↔ L y := by
  constructor
  · rintro ⟨x, hx, -, rfl⟩
    have hs := rlMsg_space σ x
    by_cases a : x.space = 4
    · rw [if_pos a] at hs; exact absurd hs h4
    by_cases b : 16 ≤ x.space
    · rw [if_neg a, if_pos b] at hs; omega
    · rwa [rlMsg_low a (by omega)]
  · intro h; exact ⟨y, h, fun h' => absurd h' (by omega), (rlMsg_low h4 h16).symm⟩

theorem rlMsg_local (σ : Nat → Nat) (c j : Nat) (v : Val) (tp : Nat) :
    rlMsg σ (enc (16 + c) j v tp) = enc (16 + σ c) j v tp := by
  simp only [rlMsg, enc, show ¬ (16 + c = 4) by omega, if_false, show 16 ≤ 16 + c by omega, if_true,
    show 16 + c - 16 = c by omega]

theorem rlMsg_call (σ : Nat → Nat) (c r sb cid ch tp : Nat) :
    rlMsg σ (callMsg c r sb cid ch tp) = callMsg (σ c) r sb (σ cid) ch tp := by
  simp [rlMsg, callMsg]

theorem localView_rl {σ : Nat → Nat} {c : Nat} {locs : Array Val} {tpl : Nat → Nat} {x : Msg}
    (h : x ∈ localView (16 + c) locs tpl) : rlMsg σ x ∈ localView (16 + σ c) locs tpl := by
  obtain ⟨j, hj, rfl⟩ := mem_localView.mp h
  rw [rlMsg_local]; exact mem_localView.mpr ⟨j, hj, rfl⟩

theorem localView_rl_inv {σ : Nat → Nat} {c d : Nat} {locs : Array Val} {tpl : Nat → Nat} {y : Msg}
    (hd : σ c = d) (h : y ∈ localView (16 + d) locs tpl) :
    ∃ x, x ∈ localView (16 + c) locs tpl ∧ y = rlMsg σ x := by
  obtain ⟨j, hj, rfl⟩ := mem_localView.mp h
  exact ⟨_, mem_localView.mpr ⟨j, hj, rfl⟩, by rw [rlMsg_local, hd]⟩

/-- The saved callers with depth ids (the bottom one 0). -/
def svR : List Saved → List Saved
  | [] => []
  | c :: sv => { c with cid := sv.length } :: svR sv

@[simp] theorem svR_length : ∀ sv : List Saved, (svR sv).length = sv.length
  | [] => rfl
  | _ :: sv => by simp [svR, svR_length sv]

/-- The ids of `svR sv` are depths: the `i`-th saved caller from the top has id `length - 1 - i`. -/
theorem svR_cid : ∀ (sv : List Saved) (i : Nat) (hi : i < (svR sv).length),
    ((svR sv)[i]'hi).cid = sv.length - 1 - i
  | [], _, hi => by simp at hi
  | c :: sv, 0, _ => by simp [svR]
  | c :: sv, i + 1, hi => by
    simp only [svR, List.getElem_cons_succ, List.length_cons]
    rw [svR_cid sv i (by simp [svR] at hi; simpa using hi)]; omega

theorem chainCharge_svR (X : Ctx) : ∀ (k : Nat) (sv : List Saved), chainCharge X k (svR sv) = chainCharge X k sv
  | _, [] => rfl
  | k, c :: sv => by simp only [svR, chainCharge]; rw [chainCharge_svR X c.k sv]

section ChainFacts
variable {X : Ctx} {t : Nat}

theorem Chain.len : ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved},
    Chain X t cid sb k rest sv → rest.length = sv.length
  | _, _, _, [], [], _ => rfl
  | _, _, _, _ :: _, _ :: _, h => by simp [h.2.2.2.2.2.2.2.2.2.2.2.2.len]
  | _, _, _, [], _ :: _, h => h.elim
  | _, _, _, _ :: _, [], h => h.elim

theorem Chain.ids_lt : ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved},
    Chain X t cid sb k rest sv → ∀ c ∈ sv, c.cid < cid
  | _, _, _, [], [], _ => by simp
  | _, _, _, _ :: _, c :: sv, h => by
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact h.2.2.2.2.1
    · have := h.2.2.2.2.2.2.2.2.2.2.2.2.ids_lt c' hc'; have := h.2.2.2.2.1; omega
  | _, _, _, [], _ :: _, h => h.elim
  | _, _, _, _ :: _, [], h => h.elim

theorem Chain.len_le : ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved},
    Chain X t cid sb k rest sv → sv.length ≤ cid
  | _, _, _, [], [], _ => by simp
  | _, _, _, _ :: _, c :: sv, h => by
    have := h.2.2.2.2.2.2.2.2.2.2.2.2.len_le; have := h.2.2.2.2.1; simp; omega
  | _, _, _, [], _ :: _, h => h.elim
  | _, _, _, _ :: _, [], h => h.elim

theorem Chain.svR : ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved},
    Chain X t cid sb k rest sv → Chain X t sv.length sb k rest (svR sv)
  | _, _, _, [], [], h => ⟨rfl, h.2⟩
  | _, _, _, _ :: _, c :: sv, h => by
    obtain ⟨a1, a2, a3, a4, -, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h
    exact ⟨a1, a2, a3, a4, by simp, a6, a7, a8, a9, a10, a11, a12, by simpa using a13.svR⟩
  | _, _, _, [], _ :: _, h => h.elim
  | _, _, _, _ :: _, [], h => h.elim

/-- `σ` maps the chain's ids to depths. -/
def DepthOK (σ : Nat → Nat) : Nat → List Saved → Prop
  | cid, [] => σ cid = 0
  | cid, c :: sv => σ cid = sv.length + 1 ∧ DepthOK σ c.cid sv

theorem DepthOK.top {σ : Nat → Nat} : ∀ {cid : Nat} {sv : List Saved}, DepthOK σ cid sv → σ cid = sv.length
  | _, [], h => h
  | _, _ :: _, h => by simpa using h.1

theorem DepthOK.congr {σ σ' : Nat → Nat} : ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved},
    Chain X t cid sb k rest sv → DepthOK σ' cid sv → (∀ x, x ≤ cid → σ x = σ' x) → DepthOK σ cid sv
  | _, _, _, [], [], _, h, e => by simp only [DepthOK] at h ⊢; rw [e _ (Nat.le_refl _), h]
  | _, _, _, _ :: _, c :: sv, hc, h, e => by
    refine ⟨by rw [e _ (Nat.le_refl _)]; exact h.1, DepthOK.congr hc.2.2.2.2.2.2.2.2.2.2.2.2 h.2 ?_⟩
    intro x hx; have := hc.2.2.2.2.1; exact e x (by omega)
  | _, _, _, [], _ :: _, hc, _, _ => hc.elim
  | _, _, _, _ :: _, [], hc, _, _ => hc.elim

theorem DepthOK.exists : ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved},
    Chain X t cid sb k rest sv → ∃ σ, DepthOK σ cid sv
  | _, _, _, [], [], _ => ⟨fun _ => 0, rfl⟩
  | cid, _, _, _ :: _, c :: sv, hc => by
    obtain ⟨σ', h'⟩ := DepthOK.exists hc.2.2.2.2.2.2.2.2.2.2.2.2
    refine ⟨fun x => if x = cid then sv.length + 1 else σ' x, by simp, ?_⟩
    refine DepthOK.congr hc.2.2.2.2.2.2.2.2.2.2.2.2 h' ?_
    intro x hx; have := hc.2.2.2.2.1; simp only [show x ≠ cid by omega, if_false]
  | _, _, _, [], _ :: _, hc => hc.elim
  | _, _, _, _ :: _, [], hc => hc.elim

theorem DepthOK.below {σ : Nat → Nat} : ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved},
    Chain X t cid sb k rest sv → DepthOK σ cid sv → ∀ c ∈ sv, σ c.cid < sv.length
  | _, _, _, [], [], _, _ => by simp
  | _, _, _, _ :: _, c :: sv, hc, h => by
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · rw [h.2.top]; simp
    · have := DepthOK.below hc.2.2.2.2.2.2.2.2.2.2.2.2 h.2 c' hc'; simp; omega
  | _, _, _, [], _ :: _, hc, _ => hc.elim
  | _, _, _, _ :: _, [], hc, _ => hc.elim

/-- Chain messages are call records or in the locals space of a saved caller. -/
theorem chainMsgs_space_ids : ∀ {cid k : Nat} {rest : List Frame} {sv : List Saved} {x : Msg},
    chainMsgs X cid k rest sv x → x.space = 4 ∨ (16 ≤ x.space ∧ x.space - 16 ∈ sv.map Saved.cid)
  | _, _, [], [], _, h => h.elim
  | _, _, _ :: _, c :: sv, x, h => by
    rcases h with rfl | h | h
    · exact Or.inl rfl
    · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; right; simp
    · rcases chainMsgs_space_ids h with h | ⟨h1, h2⟩
      · exact Or.inl h
      · right; exact ⟨h1, List.mem_cons_of_mem _ h2⟩
  | _, _, [], _ :: _, _, h => h.elim
  | _, _, _ :: _, [], _, h => h.elim

theorem chainMsgs_rl {σ : Nat → Nat} : ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved},
    Chain X t cid sb k rest sv → DepthOK σ cid sv → ∀ x,
      chainMsgs X cid k rest sv x → chainMsgs X sv.length k rest (svR sv) (rlMsg σ x)
  | _, _, _, [], [], _, _, _, h => h.elim
  | _, _, _, _ :: _, c :: sv, hc, hd, x, h => by
    have ht := hd.1
    have hc' := hd.2.top
    rcases h with rfl | h | h
    · left; rw [rlMsg_call, ht, hc']; simp [svR]
    · right; left; have := localView_rl (σ := σ) h; rw [hc'] at this; simpa [svR] using this
    · right; right; simpa [svR] using chainMsgs_rl hc.2.2.2.2.2.2.2.2.2.2.2.2 hd.2 x h
  | _, _, _, [], _ :: _, hc, _, _, _ => hc.elim
  | _, _, _, _ :: _, [], hc, _, _, _ => hc.elim

theorem chainMsgs_rl_inv {σ : Nat → Nat} : ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved},
    Chain X t cid sb k rest sv → DepthOK σ cid sv → ∀ y,
      chainMsgs X sv.length k rest (svR sv) y → ∃ x, chainMsgs X cid k rest sv x ∧ y = rlMsg σ x
  | _, _, _, [], [], _, _, _, h => by simp [svR, chainMsgs] at h
  | _, _, _, _ :: _, c :: sv, hc, hd, y, h => by
    have ht := hd.1
    have hc' := hd.2.top
    simp only [svR, List.length_cons, chainMsgs] at h
    rcases h with rfl | h | h
    · refine ⟨_, Or.inl rfl, ?_⟩; rw [rlMsg_call, ht, hc']
    · obtain ⟨x, hx, rfl⟩ := localView_rl_inv hc' h
      exact ⟨x, Or.inr (Or.inl hx), rfl⟩
    · obtain ⟨x, hx, rfl⟩ := chainMsgs_rl_inv hc.2.2.2.2.2.2.2.2.2.2.2.2 hd.2 y (by simpa using h)
      exact ⟨x, Or.inr (Or.inr hx), rfl⟩
  | _, _, _, [], _ :: _, hc, _, _, _ => hc.elim
  | _, _, _, _ :: _, [], hc, _, _, _ => hc.elim

end ChainFacts

/-- **Relabelling to depths.**  A related state stays related when the live frames' activation ids
are replaced by their depths (`σ`, with the current frame at depth `E.rest.length`), the live
locals spaces and call records are relabelled by `σ`, and the messages of dead locals spaces are
dropped (`A` = the live ids).  In the relabelled environment the caller chain is `svR sv` (ids =
depths, `svR_cid`) and every live message in space 4 or `≥ 16` is a chain message: no dead spaces. -/
theorem RelW.relabel {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {a b : Nat} (R : RelW X E s f tps tpl t pc S live a b) :
    ∃ (σ : Nat → Nat) (A : List Nat) (sv : List Saved), σ E.cid = E.rest.length ∧
      RelW X ⟨E.sb, E.rest.length, E.rest, relabelLive σ A E.live, E.k⟩ s f tps tpl t pc S (relabelLive σ A live) a b ∧
      Chain X t E.rest.length E.sb E.k E.rest (svR sv) ∧
      (∀ y, relabelLive σ A E.live y → (y.space = 4 ∨ 16 ≤ y.space) →
        chainMsgs X E.rest.length E.k E.rest (svR sv) y) := by
  obtain ⟨sv, hc, hin, hout, hrl⟩ := R.calls.chain
  obtain ⟨tpb, htpb, hbud⟩ := R.calls.budget
  obtain ⟨σ, hd⟩ := DepthOK.exists hc
  have hlen := hc.len
  have htop : σ E.cid = E.rest.length := by rw [hd.top, hlen]
  let A := E.cid :: sv.map Saved.cid
  have keepChain : ∀ x, chainMsgs X E.cid E.k E.rest sv x → keepA A x := by
    intro x hx h16
    rcases chainMsgs_space_ids hx with h | ⟨-, h⟩
    · omega
    · exact List.mem_cons_of_mem _ h
  -- low spaces are untouched
  have lowE : ∀ y, y.space ≠ 4 → y.space < 16 → (relabelLive σ A E.live y ↔ E.live y) :=
    fun y h4 h16 => relabel_low h4 h16
  -- the relabelled outer messages in space 4 or `≥ 16` are exactly the relabelled chain
  have outR : ∀ y, relabelLive σ A E.live y → (y.space = 4 ∨ 16 ≤ y.space) →
      chainMsgs X E.rest.length E.k E.rest (svR sv) y := by
    rintro y ⟨x, hx, hk, rfl⟩ hs
    have hxs : x.space = 4 ∨ 16 ≤ x.space := by
      have := rlMsg_space σ x
      by_cases a4 : x.space = 4
      · exact Or.inl a4
      by_cases a16 : 16 ≤ x.space
      · exact Or.inr a16
      rw [if_neg a4, if_neg a16] at this; rw [this] at hs; omega
    rcases hout x hx hxs with h | ⟨d1, -, d3, d4⟩
    · rw [hlen]; exact chainMsgs_rl hc hd x h
    · exfalso
      rcases List.mem_cons.mp (hk d1) with h | h
      · exact d3 (by omega)
      · obtain ⟨c, hcm, hce⟩ := List.mem_map.mp h
        exact d4 c hcm (by omega)
  refine ⟨σ, A, sv, htop, ?_, by rw [hlen]; exact hc.svR, outR⟩
  have hsepR : ∀ x, relabelLive σ A E.live x → x.space ≠ 0 ∧ x.space ≠ 16 + E.rest.length := by
    rintro y ⟨x, hx, hk, rfl⟩
    have hsep := R.envSep x hx
    have hs := rlMsg_space σ x
    by_cases a4 : x.space = 4
    · rw [if_pos a4] at hs; rw [hs]; omega
    by_cases a16 : 16 ≤ x.space
    · rw [if_neg a4, if_pos a16] at hs; rw [hs]
      refine ⟨by omega, ?_⟩
      rcases List.mem_cons.mp (hk a16) with h | h
      · exact absurd (show x.space = E.lsp by simp only [Env.lsp]; omega) hsep.2
      · obtain ⟨c, hcm, hce⟩ := List.mem_map.mp h
        have := DepthOK.below hc hd c hcm
        rw [hce] at this; omega
    · rw [if_neg a4, if_neg a16] at hs; rw [hs]; omega
  have hheap : HeapOK ⟨E.sb, E.rest.length, E.rest, relabelLive σ A E.live, E.k⟩ s t := by
    obtain ⟨T, tpm, h1, h2, h3, h4⟩ := R.heap.mem
    obtain ⟨tpg, g1, g2⟩ := R.heap.glob
    exact ⟨R.heap.pages, ⟨T, tpm, h1, h2, h3, fun x hx => (lowE x (by omega) (by omega)).trans (h4 x hx)⟩,
      ⟨tpg, g1, fun x hx => (lowE x (by omega) (by omega)).trans (g2 x hx)⟩⟩
  have hcalls : CallsOK X ⟨E.sb, E.rest.length, E.rest, relabelLive σ A E.live, E.k⟩ s t := by
    refine ⟨?_, ⟨svR sv, ?_, ?_, ?_, ?_⟩, ⟨tpb, htpb, fun x hx => (lowE x (by omega) (by omega)).trans (hbud x hx)⟩⟩
    · have := hc.len_le; have := R.calls.cidLtT; show E.rest.length < t; omega
    · show Chain X t E.rest.length E.sb E.k E.rest (svR sv); rw [hlen]; exact hc.svR
    · intro y hy
      have hy' : chainMsgs X sv.length E.k E.rest (svR sv) y := by rw [← hlen]; exact hy
      obtain ⟨x, hx, rfl⟩ := chainMsgs_rl_inv hc hd y hy'
      exact ⟨x, hin x hx, keepChain x hx, rfl⟩
    · intro y hy hs; exact Or.inl (outR y hy hs)
    · show s.stackRem + chainCharge X E.k (svR sv) < 2 ^ 30; rw [chainCharge_svR]; exact hrl
  refine ⟨R.frames, R.kLt, R.fn, R.pcEq, R.pcLt, R.labels, R.base, R.sbLe, R.height, R.nloc, R.gas, R.segLt,
    R.segbLt, R.numS, R.numL, R.tpsLt, R.tplLt, hsepR, ?_, R.sbLt, ?_, hheap, hcalls, ?_⟩
  · intro h0
    have h0' : E.rest.length = 0 := h0
    have hr : E.rest = [] := List.length_eq_zero_iff.mp h0'
    have hsv : sv = [] := List.length_eq_zero_iff.mp (by rw [← hlen, h0'])
    refine ⟨hr, ?_⟩
    have hc0 := hc; rw [hr, hsv] at hc0; exact hc0.2
  · have := hc.len_le; have := R.cidLt; show E.rest.length < 2 ^ 28; omega
  · intro y
    constructor
    · rintro ⟨x, hx, hk, rfl⟩
      rcases (R.live x).mp hx with h | h | h
      · obtain ⟨i, hi, rfl⟩ := mem_stackView.mp h
        left; rw [rlMsg_low (by simp) (by simp)]; exact mem_stackView.mpr ⟨i, hi, rfl⟩
      · right; left
        have := localView_rl (σ := σ) h
        simp only [Env.lsp] at this ⊢; rwa [htop] at this
      · right; right; exact ⟨x, h, hk, rfl⟩
    · rintro (h | h | h)
      · obtain ⟨i, hi, rfl⟩ := mem_stackView.mp h
        refine ⟨_, (R.live _).mpr (Or.inl h), fun h' => absurd h' (by simp), (rlMsg_low (by simp) (by simp)).symm⟩
      · simp only [Env.lsp] at h
        obtain ⟨x, hx, rfl⟩ := localView_rl_inv htop h
        refine ⟨x, (R.live x).mpr (Or.inr (Or.inl hx)), ?_, rfl⟩
        intro _; obtain ⟨j, -, rfl⟩ := mem_localView.mp hx; simp [A]
      · obtain ⟨x, hx, hk, rfl⟩ := h
        exact ⟨x, (R.live x).mpr (Or.inr (Or.inr hx)), hk, rfl⟩

/-- **The boundary relation, relabelled.**  At a cut, the STATE message's activation id may be
replaced by the current frame's depth `s.frames.length - 1` and the live list by its relabelled,
dead-space-free image: the boundary is then a function of the spec state (and producer times). -/
theorem Bnd.relabel {X : Ctx} {sg : Nat → Nat × Nat} {s : St} {t S : Nat} {m : List F} {L : List Msg}
    (h : Bnd X sg s t S m L) :
    ∃ (σ : Nat → Nat) (A : List Nat), Bnd X sg s t S (m.set 5 ((s.frames.length - 1 : Nat) : F))
      ((L.filter (fun x => decide (keepA A x))).map (rlMsg σ)) := by
  obtain ⟨k, pc, sb, cid, rfl, E, f, tps, tpl, rfl, rfl, rfl, R⟩ := h
  obtain ⟨σ, A, sv, -, R', -, -⟩ := R.relabel
  have hfr : s.frames.length - 1 = E.rest.length := by rw [R.frames]; simp
  refine ⟨σ, A, E.k, pc, E.sb, E.rest.length, ?_, ⟨E.sb, E.rest.length, E.rest, relabelLive σ A E.live, E.k⟩,
    f, tps, tpl, rfl, rfl, rfl, ?_⟩
  · rw [hfr]; rfl
  · refine (congrArg (fun L => RelW X _ s f tps tpl (t + 1) pc S L _ _) (funext fun y => propext ?_)).mp R'
    simp only [relabelLive, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨x, hx, hk, rfl⟩; exact ⟨x, ⟨hx, hk⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hk⟩, rfl⟩; exact ⟨x, hx, hk, rfl⟩

#print axioms RelW.relabel
#print axioms Bnd.relabel

end WasmBase
