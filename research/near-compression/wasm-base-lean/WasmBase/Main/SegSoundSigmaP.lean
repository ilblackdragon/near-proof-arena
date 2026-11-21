import WasmBase.Main.SegMemFrame
import WasmBase.Main.HostTwinP

/-!
# WasmBase.Main.SegSoundSigmaP — segment soundness with the host side **and the page count** pinned, segment-pinned relies (E2E M6, COVER items 3–4)

`seg_sound_σ` (`Main/SegSoundSigma.lean`, unchanged) has two HOST premises that cannot be discharged
from the honest run as stated:

* **gas segments** — `HostRelyσ.reg`/`.wf` are `RowQJ`s: they quantify over related pre-states at
  **every** gas segment `(a, b)`, so over every gas register `g`, while the two-run lemma (and the
  host call) needs the honest `g`.  But the segment induction only ever uses the clause at the row's
  own segment `sg t` (and with `t + 1 < P`, `S + maxFee < P`).  **`RowQS`** is `RowQJ` with exactly
  those hypotheses; **`exec_rowsJS`** is `exec_rowsJ` (copied) with `RowQS` relies.
* **page count** — `RelW` does not pin `pages.size`, and the host call's bounds checks read it.  The
  thread invariant becomes `SigP σ np` (`Main/HostTwinP.lean`): instruction rows keep it by
  `SigKeep` + `seg_instr_pagesKeep` (`rowJKeep_sigP`), HOST rows by `HoldRowSP`.

**`seg_sound_σP`** is `seg_sound_σ` with `HoldRowSP` (the σ-and-page-pinned HOST row facts) and
`HostRelyP` (`RowQS` relies) in place of `HoldRowSσ`/`HostRelyσ`, `SigP` pins in and out.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
open HostFoot StepSide
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. Segment-pinned relies -/

/-- **`RowQJ` at the row's own gas segment** (with the bounds the induction supplies). -/
def RowQS (X : Ctx) (J : Nat → St → Prop) (Q : St → (Msg → Prop) → Prop) (inS : List F)
    (cons prod : List Msg) (sg : Nat → Nat × Nat) : Prop :=
  ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) (s' : St),
    RelW X E s f tps tpl t pc S live (sg t).1 (sg t).2 → J t s → inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
    (∀ x ∈ cons, live x) → t + 1 < ZkFormal.Algebra.P → S + X.maxFee < ZkFormal.Algebra.P →
    step X.cfg X.p s = .cont s' → Q s live → Q s' (stepLive live cons prod)

theorem RowQ.toS {X : Ctx} {J : Nat → St → Prop} {Q : St → (Msg → Prop) → Prop} {inS : List F}
    {cons prod : List Msg} {sg : Nat → Nat × Nat} (h : RowQ X Q inS cons prod) : RowQS X J Q inS cons prod sg :=
  fun E s f tps tpl t pc S live s' R _ hin hl _ _ hs hQ => h E s f tps tpl t pc S live _ _ s' R hin hl hs hQ

theorem RowQJ.toS {X : Ctx} {J : Nat → St → Prop} {Q : St → (Msg → Prop) → Prop} {inS : List F}
    {cons prod : List Msg} {sg : Nat → Nat × Nat} (h : RowQJ X J Q inS cons prod) : RowQS X J Q inS cons prod sg :=
  fun E s f tps tpl t pc S live s' R hJ hin hl _ _ hs hQ => h E s f tps tpl t pc S live _ _ s' R hJ hin hl hs hQ

theorem rowQS_and {X : Ctx} {J : Nat → St → Prop} {Q1 Q2 : St → (Msg → Prop) → Prop} {inS : List F}
    {cons prod : List Msg} {sg : Nat → Nat × Nat} (h1 : RowQS X J Q1 inS cons prod sg)
    (h2 : RowQS X J Q2 inS cons prod sg) :
    RowQS X J (fun s live => Q1 s live ∧ Q2 s live) inS cons prod sg :=
  fun E s f tps tpl t pc S live s' R hJ hin hl ht hS hs hQ =>
    ⟨h1 E s f tps tpl t pc S live s' R hJ hin hl ht hS hs hQ.1, h2 E s f tps tpl t pc S live s' R hJ hin hl ht hS hs hQ.2⟩

/-! ## 2. The segment induction with segment-pinned relies -/

section
variable (X : Ctx) {ρ : Type} [DecidableEq ρ] (act : List ρ) (inS outS : ρ → List F)
  (cons prod : ρ → List Msg) (init fin : List Msg) (pcf N Sf : F)

/-- **`exec_rowsJ`: the segment induction with a time-indexed state invariant `J`.**  The hypotheses
of `exec_of_rows_cutQ` with the row premises restricted to `J` (`RowFactsSegMapJ`, `RowQJ`) and
`J (t0 + 1) s0`.  Conclusions: `N = t0 + n + 1`; at a cut, `exec_of_rows_cutQ`'s conclusion plus
`J (t0 + n + 1) sN`; for any status, `exec_rows_rel`'s per-row relation plus `J` at every row. -/
theorem exec_rowsJS (sg : Nat → Nat × Nat) (st : Nat) (hst2 : st ≤ 2) (J : Nat → St → Prop)
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
    (Q : St → (Msg → Prop) → Prop) (hQ : ∀ r ∈ act, RowQS X J Q (inS r) (cons r) (prod r) sg)
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
        exact hQ rs[k] (hmem k (by omega)) E s f tps tpl (t0 + k + 1) pc _ (live init prodL consL k) s' R hJk
          (by rw [← pos_in k (by omega)]; exact hin) hlive (by omega) hS hs' hQk
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

/-! ## 3. Instruction rows keep `SigP` -/

/-- An instruction row keeps the σ-thread (`rowJKeep_sig`) and the page count (`PagesKeep`). -/
theorem rowJKeep_sigP {X : Ctx} {inS : List F} {σ : Nat → St} {np : Nat} (h : CodeNonHost X inS)
    (hk : σ ((lvl inS).toNat + 1) = σ (lvl inS).toNat) (hpk : PagesKeep X inS) : RowJKeep X (SigP σ np) inS := by
  intro E s f tps tpl t pc S live a b s' R hin ht hJ hs
  exact ⟨rowJKeep_sig h hk E s f tps tpl t pc S live a b s' R hin ht hJ.1 hs,
    by rw [hpk E s f tps tpl t pc S live a b s' R hin hs]; exact hJ.2⟩

/-- **The HOST rows' segment facts, σ- and page-pinned** (named premise; `Main/HostIfCover2.lean`
discharges it from `HostIf` and the coverage facts). -/
def HoldRowSP (X : Ctx) (tr : Trace) (pub : List F) (sg : Nat → Nat × Nat) (σ : Nat → St) (np : Nat) : Prop :=
  ∀ r, r < tr.height 22 → rowAct Host.table tr pub 22 r →
    RowFactsSegJ X (SigP σ np) (rowInM tr pub (22, r)) (rowOutM tr pub (22, r))
      (consCHS tr pub (22, r)) (prodCHS tr pub (22, r))
      (sg (rowNat tr 22 r 1)) (sg (rowNat tr 22 r 1 + 1))

/-- **The HOST rows' register and `RegWF` relies at their own segment** (`RowQS`). -/
structure HostRelyP (X : Ctx) (tr : Trace) (pub : List F) (sg : Nat → Nat × Nat) (σ : Nat → St) (np : Nat) :
    Prop where
  reg : ∀ ρ ∈ actListM2 tr pub, ρ.1 = 22 →
    RowQS X (SigP σ np) (fun s live => RegC live s) (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ) sg
  wf : ∀ ρ ∈ actListM2 tr pub, ρ.1 = 22 →
    RowQS X (SigP σ np) (fun s _ => RegWF s) (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ) sg

/-- **Assembling the σ- and page-pinned row facts** (`rowFactsSegMapJ_seg` with `SigP`). -/
theorem rowFactsSegMapJ_segP (X : M2Ctx) {nloc ngl : Nat} {tr : Trace} {pub : List F}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hcode : CodeOK X.toCtx tr)
    (hI : SegInstrRows X.toCtx tr pub) {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {σ : Nat → St} {np : Nat} (hsk : SigKeep tr pub σ) (hhold : HoldRowSP X.toCtx tr pub sg σ np) :
    ∀ ρ ∈ actListM2 tr pub, RowFactsSegMapJ X.toCtx (SigP σ np) (rowInM tr pub ρ) (rowOutM tr pub ρ)
      (consCHS tr pub ρ) (prodCHS tr pub ρ) sg := by
  intro ρ hρ
  by_cases h22 : ρ.1 = 22
  · obtain ⟨t, r⟩ := ρ
    simp only at h22
    subst h22
    rcases mem_actListM2 hρ with ⟨-, hr, ha⟩ | ⟨htI, -, -⟩
    · exact hhold r hr ha
    · exfalso; rcases htI with ⟨_, h⟩ | h | h | h <;> simp_all
  · exact RowFactsSeg.toJ (rowFactsSegMap_instr X.toCtx hI hkeep hρ h22)
      (rowJKeep_sigP (seg_instr_codeNonHost X H hcode ρ hρ h22) (hsk ρ hρ h22)
        (seg_instr_pagesKeep X H hcode ρ hρ h22))

/-! ## 4. The segment soundness theorem, σ- and page-pinned -/

/-- **`seg_sound_σP`**: `seg_sound_σ` with `HoldRowSP`/`HostRelyP` (page count on the thread,
relies at the row's own gas segment) in place of `HoldRowSσ`/`HostRelyσ`. -/
theorem seg_sound_σP (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {σ : Nat → St} {np : Nat} (hsk : SigKeep tr pub σ) (hhold : HoldRowSP X.toCtx tr pub sg σ np)
    (hrely : HostRelyP X.toCtx tr pub sg σ np)
    (hst0 : pub.getD Boundary.pubStatus 0 = 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    (hT : TombDead tr pub (finS tr pub))
    {s0 : St} (h0 : BndC X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hw0 : RegWF s0) (hσ0 : SigP σ np ((pub.getD pubTIn 0).toNat + 1) s0) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    ∃ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN ∧
      (∀ m, run X.toCtx.cfg X.toCtx.p ((actListM2 tr pub).length + m) s0 = run X.toCtx.cfg X.toCtx.p m sN) ∧
      BndC X.toCtx sg sN (pub.getD pubTOut 0).toNat (pub.getD pubSOut 0).toNat (segFinM tr pub) (finS tr pub) ∧
      cutoList tr = cutView X.toCtx sN ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxOut = SegSha.limbsF d ∧
        SegSha.wbytes d = cutDigest (cutView X.toCtx sN)) ∧
      (∀ y ∈ cutView X.toCtx sN, MsgWF y) ∧
      RegWF sN ∧ SigP σ np ((pub.getD pubTOut 0).toNat + 1) sN := by
  have hP := P_val
  have hrk : InstrRegKeep X.toCtx tr pub := seg_instr_regKeep X H hcode
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfacts X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMapJ_segP X H hcode hI hkeep hsk hhold
  have hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1 :=
    fun ρ hρ => (hrows ρ hρ).flat.tsOut
  have hlenEq := seg_len H hts (by omega)
  have hlv : ∀ ρ ∈ actListM2 tr pub, (lvl (rowInM tr pub ρ)).toNat < 2 ^ 30 := by
    intro ρ hρ
    have := seg_row_lvl H hts (by omega) ρ hρ
    omega
  have ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P := by omega
  have hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.toCtx.maxFee + 1) < P := by
    have e : (pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat = (actListM2 tr pub).length := by omega
    rw [e] at hfeeN; exact hfeeN
  have hst := seg_hst H
  rw [segMF_eq, hst0] at hst
  have hQ : ∀ ρ ∈ actListM2 tr pub, RowQS X.toCtx (SigP σ np)
      (fun s live => (RegC live s ∧ SpC live) ∧ RegWF s) (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ) sg := by
    intro ρ hρ
    by_cases h22 : ρ.1 = 22
    · exact rowQS_and (rowQS_and (hrely.reg ρ hρ h22) (RowQ.toS (hostRely_sp X.toCtx tr pub ρ hρ h22)))
        (hrely.wf ρ hρ h22)
    · exact RowQ.toS (rowQ_and (rowQ_and (seg_instr_rowQ_reg H hρ h22 (hlv ρ hρ) (hrk ρ hρ h22))
        (seg_instr_rowQ_sp H hρ h22 (hlv ρ hρ))) (rowQ_regWF_keep (hrk ρ hρ h22)))
  obtain ⟨-, hcut, -⟩ := exec_rowsJS X.toCtx (actListM2 tr pub) (rowInM tr pub) (rowOutM tr pub) (consCHS tr pub)
    (prodCHS tr pub) (initS tr pub) (finS tr pub) (pub.getD pubPcOut 0) (pub.getD pubTOut 0 + 1)
    (pub.getD pubSOut 0) sg 0 (by decide) (SigP σ np) hrows (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat
    (segM0 tr pub) (pub.getD pubSbOut 0) (tr.cell 0 0 (ix Segb.cols "cidf")) hst (seg_hch H X.toCtx hb hg) hinit
    (fun x hx => Nat.le_of_eq (seg_initS_tp tr pub x hx)) ht hfee hstepgas hg64 h0.1 _ hQ ⟨⟨h0.2.1, h0.2.2⟩, hw0⟩
    hσ0
  obtain ⟨sN, h1, h2, h3, ⟨⟨h4, h5⟩, h6⟩, hJ⟩ := hcut rfl
  have hB : BndC X.toCtx sg sN ((pub.getD pubTIn 0).toNat + (actListM2 tr pub).length) (pub.getD pubSOut 0).toNat
      (segFinM tr pub) (finS tr pub) := ⟨h3, h4, h5⟩
  obtain ⟨σ', A, hIds, -, hv⟩ := cutView_eqL (M2Ctx.toCtx_fns_nodup X) hB
  have hset : ∀ y, y ∈ cutoList tr ↔ y ∈ cutView X.toCtx sN :=
    fun y => (cuto_link H hl hIds seg_cuto_in_fin (seg_finSplit H) hT y).trans (hv y)
  have e := ctx_out_eq (cuto_sorted H hl) hset (cutView_nodup X.toCtx h6)
  obtain ⟨d, hd6, hW, hpub, hsha⟩ := ctx_out_sha H hC hl
  refine ⟨hlenEq, sN, h1, h2, by rw [hlenEq]; exact hB, e, ⟨d, hd6, hW, hpub, by rw [hsha, e]⟩,
    cutView_wf (cuto_wf H hl) hset, h6, ?_⟩
  rw [hlenEq]; exact hJ

#print axioms exec_rowsJS
#print axioms rowFactsSegMapJ_segP
#print axioms seg_sound_σP

end WasmBase
