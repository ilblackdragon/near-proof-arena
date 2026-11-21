import WasmBase.Main.SegSigma
import WasmBase.Main.SegMemFrame

/-!
# WasmBase.Main.SegExecJH — the `J`-segment induction with the halting step, and the memory frame under `J` (E2E M6, σ-thread)

`exec_rowsJ` (`Main/SegSigma.lean`) carries a time-indexed state invariant `J` through a segment's
rows, but concludes only the cut case and the per-row relation.  Here:

* **`exec_rowsJH`** — `exec_rowsJ` plus `exec_of_rows_cut`'s halting conclusions (`st ∈ {1, 2}`):
  the last row's pre-state `s` (after `n − 1` rows) satisfies **`J (t0 + n) s`**, and its step is the
  terminal one (`.fin` with no frames left / `.abort`), with the gas equation at `Sf`.  (The
  restricted spec `RowSpecSegJ` gives `J` only for continuing post-states, so the pin of a halting
  segment is on the last pre-state.)  The proof is `exec_rowsJ`'s, with `exec_of_rows_cut`'s part (D)
  (the last step halts) added, using `J` at the last pre-state.
* **`exec_frameJ`**, **`exec_pagesJ`** — `CutSeg.frame` / `CutSeg.pages` (`Main/SegMemFrame.lean`)
  for rows whose facts are restricted to `J` (`RowFactsSegMapJ`): the byte frame (a run from the
  in-boundary block augmented by one untouched byte) and the page count, through `exec_rowsJ`.
-/

namespace WasmBase

open ZkFormal.Algebra
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

section
variable (X : Ctx) {ρ : Type} [DecidableEq ρ] (act : List ρ) (inS outS : ρ → List F)
  (cons prod : ρ → List Msg) (init fin : List Msg) (pcf N Sf : F)

/-- **`exec_rowsJ`: the segment induction with a time-indexed state invariant `J`.**  The hypotheses
of `exec_of_rows_cutQ` with the row premises restricted to `J` (`RowFactsSegMapJ`, `RowQJ`) and
`J (t0 + 1) s0`.  Conclusions: `N = t0 + n + 1`; at a cut, `exec_of_rows_cutQ`'s conclusion plus
`J (t0 + n + 1) sN`; for any status, `exec_rows_rel`'s per-row relation plus `J` at every row. -/
theorem exec_rowsJH (sg : Nat → Nat × Nat) (st : Nat) (hst2 : st ≤ 2) (J : Nat → St → Prop)
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
    (st ≠ 0 → 0 < act.length ∧ ∃ s, NearSpecV3.Wasm.seg X.cfg X.p (act.length - 1) s0 = .cont s ∧
      J (t0 + act.length) s ∧
      (st = 1 → ∃ sN tps tpl locs, step X.cfg X.p s = .fin sN ∧
        NearSpecV3.Wasm.seg X.cfg X.p act.length s0 = .fin sN ∧
        run X.cfg X.p act.length s0 = .fin sN ∧ sN.frames = [] ∧
        X.R * (Sf.toNat - (sg (t0 + act.length + 1)).1) + sN.gas.g = (sg (t0 + act.length + 1)).2 ∧
        ∃ G : Msg → Prop, (∀ x, G x → x.space ≠ 0 ∧ x.space ≠ 16) ∧
        ∀ x, x ∈ fin ↔ x ∈ stackView sN.stack tps ∨ x ∈ localView 16 locs tpl ∨ G x) ∧
      (st = 2 → ∃ sN e, step X.cfg X.p s = .abort sN e ∧
        NearSpecV3.Wasm.seg X.cfg X.p act.length s0 = .abort sN e ∧
        run X.cfg X.p act.length s0 = .abort sN e ∧
        X.R * (Sf.toNat - (sg (t0 + act.length + 1)).1) + sN.gas.g = (sg (t0 + act.length + 1)).2)) ∧
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
  refine ⟨hN, fun h0 => ?_, fun hne => ?_, ((hrs.flatMap_right prod).append_left init).nodup_iff.mp (e1 ▸ C.nodup), ?_, ?_⟩
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
  -- (D) the last step halts (`exec_of_rows_cut`'s (D), with `J` at the last pre-state)
  · have hpos : 0 < rs.length := by
      refine Nat.pos_of_ne_zero fun h0' => ?_
      have := enil h0'
      simp only [stMsg, List.cons.injEq] at this
      have e := this.2.2.2.1
      have hstP : st < ZkFormal.Algebra.P := by rw [hP']; omega
      have := natEq (L := 0) (R := st) e (by rw [hP']; decide) hstP
      omega
    obtain ⟨s, q, pc, sb, cid, hrun, hin, ⟨E, f, tps, tpl, rfl, rfl, rfl, R⟩, -, hJs⟩ :=
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
        (live init prodL consL (rs.length - 1)) R hJs (by rw [← pos_in _ (by omega)]; exact hin) hlive (by omega)
        hS hg64
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
    have hrun' : NearSpecV3.Wasm.seg X.cfg X.p (act.length - 1) s0 = .cont s := by rw [← hlenrs]; exact hrun
    have hJ' : J (t0 + act.length) s := by
      rw [show t0 + act.length = t0 + (rs.length - 1) + 1 by omega]; exact hJs
    refine ⟨by omega, s, hrun', hJ', fun h1 => ?_, fun h2 => ?_⟩
    · obtain ⟨sN, hsN, hfr, hg, G, hG, hview⟩ := (hspec hgas').2.1 (by omega)
      have hs := hseglen _ hsN
      refine ⟨sN, tps, tpl, f.locals, hsN, hs, run_of_seg_stop hs (by simp), hfr, ?_, G, hG, ?_⟩
      · rw [← hSf, ← hidx]; exact hg
      · intro x
        rw [← hview x, ← C.live_final x]
        have := C.live_succ (k := rs.length - 1) (by simp [consL]; omega) x
        simp only [consL, List.length_map, show rs.length - 1 + 1 = rs.length by omega] at this ⊢
        rw [this]; simp only [stepLive, prodL, List.getElem_map]
    · obtain ⟨sN, e, hsN, hg⟩ := (hspec hgas').2.2 (by omega)
      have hs := hseglen _ hsN
      refine ⟨sN, e, hsN, hs, run_of_seg_stop hs (by simp), ?_⟩
      rw [← hSf, ← hidx]; exact hg
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
    exact C.consumed_live (k := k) (by simp [consL]; omega) (by simpa [consL] using hx)end

section
variable (X : Ctx) {ρ : Type} [DecidableEq ρ] (act : List ρ) (inS outS : ρ → List F)
  (cons prod : ρ → List Msg) (init fin : List Msg) (pcf N Sf : F)

/-- **The byte frame of a cut segment, rows restricted to `J`** (`CutSeg.frame` through
`exec_rowsJ`): an in-bounds address with no space-3 message in the in-boundary block keeps its byte. -/
theorem exec_frameJ (sg : Nat → Nat × Nat) (J : Nat → St → Prop)
    (hrows : ∀ r ∈ act, RowFactsSegMapJ X J (inS r) (outS r) (cons r) (prod r) sg)
    (t0 S0 : Nat) (m0 : List F) (sbf cidf : F)
    (hst : (m0 :: act.map outS).Perm ([pcf, N, Sf, ((0 : Nat) : F), sbf, cidf] :: act.map inS))
    (hch : (init ++ act.flatMap prod).Perm (fin ++ act.flatMap cons))
    (hinit : init.Nodup) (hinitTp : ∀ x ∈ init, x.tp ≤ t0)
    (ht : t0 + act.length + 1 + (2 ^ 30 + 2 ^ 16) < ZkFormal.Algebra.P)
    (hfee : S0 + (act.length + 1) * (X.maxFee + 1) < ZkFormal.Algebra.P)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64)
    {s0 sN : St} (h0 : Bnd X sg s0 t0 S0 m0 init) (hJ0 : J (t0 + 1) s0)
    {addr : Nat} (ha : addr < memBytes s0) (hfree : ∀ y ∈ init, y.space = 3 → y.slot ≠ addr)
    (hseg : NearSpecV3.Wasm.seg X.cfg X.p act.length s0 = .cont sN) :
    readByte sN addr = readByte s0 addr ∧ addr < memBytes sN := by
  let x : Msg := encB addr (readByte s0 addr).toNat t0
  have hxi : x ∉ init := fun h => hfree x h rfl rfl
  have hch' : ((init ++ [x]) ++ act.flatMap prod).Perm ((fin ++ [x]) ++ act.flatMap cons) := by
    have e1 : ((init ++ [x]) ++ act.flatMap prod).Perm (x :: (init ++ act.flatMap prod)) := by
      rw [List.append_assoc, List.singleton_append]; exact List.perm_middle
    have e2 : ((fin ++ [x]) ++ act.flatMap cons).Perm (x :: (fin ++ act.flatMap cons)) := by
      rw [List.append_assoc, List.singleton_append]; exact List.perm_middle
    exact e1.trans ((hch.cons x).trans e2.symm)
  have hinit' : (init ++ [x]).Nodup :=
    List.nodup_append.mpr ⟨hinit, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, fun a ha b hb e => by
      rw [List.mem_singleton] at hb; subst e; subst hb; exact hxi ha⟩
  have hinitTp' : ∀ y ∈ init ++ [x], y.tp ≤ t0 := fun y hy => by
    rcases List.mem_append.mp hy with h | h
    · exact hinitTp y h
    · rw [List.mem_singleton] at h; subst h; exact Nat.le_refl _
  have h0' : Bnd X sg s0 t0 S0 m0 (init ++ [x]) := by
    obtain ⟨k, pc, sb, cid, hm, E, f, tps, tpl, hsb, hcid, hk, R⟩ := h0
    refine ⟨k, pc, sb, cid, hm, ?_⟩
    have R' := R.addByte (addr := addr) (tp := t0) ha (fun y hy h3 => hfree y hy h3) (Nat.lt_succ_self _)
    refine ⟨{ E with live := fun y => E.live y ∨ y = x }, f, tps, tpl, hsb, hcid, hk, ?_⟩
    have e : (fun y => y ∈ init ∨ y = x) = (· ∈ init ++ [x]) := by
      funext y; simp [List.mem_append]
    exact e ▸ R'
  obtain ⟨-, hcut, -⟩ := exec_rowsJ X act inS outS cons prod (init ++ [x]) (fin ++ [x]) pcf N Sf sg 0
    (by decide) J hrows t0 S0 m0 sbf cidf hst hch' hinit' hinitTp' ht hfee hstepgas hg64 h0'
    (fun _ _ => True) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) trivial hJ0
  obtain ⟨sN', h1, -, h2, -, -⟩ := hcut rfl
  rw [hseg] at h1
  cases h1
  obtain ⟨k, pc, sb, cid, -, E, f, tps, tpl, -, -, -, R⟩ := h2
  have hx : x ∈ fin ++ [x] := List.mem_append_right _ (List.mem_singleton_self x)
  have hlx : E.live x := R.env_msg hx (by simp [x]) (by simp [x, Env.lsp]; omega)
  obtain ⟨e1, e2⟩ := heap_read R.heap hlx
  exact ⟨UInt8.toNat_inj.mp e1, e2⟩

/-- **The page count across a cut segment, rows restricted to `J`** (`CutSeg.pages` through
`exec_rowsJ`). -/
theorem exec_pagesJ (sg : Nat → Nat × Nat) (J : Nat → St → Prop)
    (hrows : ∀ r ∈ act, RowFactsSegMapJ X J (inS r) (outS r) (cons r) (prod r) sg)
    (t0 S0 : Nat) (m0 : List F) (sbf cidf : F)
    (hst : (m0 :: act.map outS).Perm ([pcf, N, Sf, ((0 : Nat) : F), sbf, cidf] :: act.map inS))
    (hch : (init ++ act.flatMap prod).Perm (fin ++ act.flatMap cons))
    (hinit : init.Nodup) (hinitTp : ∀ x ∈ init, x.tp ≤ t0)
    (ht : t0 + act.length + 1 + (2 ^ 30 + 2 ^ 16) < ZkFormal.Algebra.P)
    (hfee : S0 + (act.length + 1) * (X.maxFee + 1) < ZkFormal.Algebra.P)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64)
    {s0 sN : St} (h0 : Bnd X sg s0 t0 S0 m0 init) (hJ0 : J (t0 + 1) s0)
    (hpk : ∀ r ∈ act, PagesKeep X (inS r))
    (hseg : NearSpecV3.Wasm.seg X.cfg X.p act.length s0 = .cont sN) :
    sN.pages.size = s0.pages.size := by
  obtain ⟨-, hcut, -⟩ := exec_rowsJ X act inS outS cons prod init fin pcf N Sf sg 0 (by decide) J hrows t0 S0 m0
    sbf cidf hst hch hinit hinitTp ht hfee hstepgas hg64 h0 (fun s _ => s.pages.size = s0.pages.size)
    (fun r hr E s f tps tpl t pc S live a b s' R _ hin _ hs hq => by
      show s'.pages.size = s0.pages.size
      rw [hpk r hr E s f tps tpl t pc S live a b s' R hin hs]; exact hq) rfl hJ0
  obtain ⟨sN', h1, -, -, h2, -⟩ := hcut rfl
  rw [hseg] at h1
  cases h1
  exact h2

end

#print axioms exec_rowsJH
#print axioms exec_frameJ
#print axioms exec_pagesJ

end WasmBase
