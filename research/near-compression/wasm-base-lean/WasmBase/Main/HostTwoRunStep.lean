import WasmBase.Main.HostTwoRunCall

/-!
# WasmBase.Main.HostTwoRunStep — the two-run footprint at the `step` level, and the pinned premise's non-vacuity (E2E M6)

* **`step_host_two_run`**: a `step` whose instruction is a `call` of an import `name` (an arm of
  `hostCall`, constant fee) from two states with the same head frame position, low-equivalent on the
  arm's read set (`Low`: equal host parts — `sideR` and `gas.g` —, equal top-`k` stack entries, equal
  page count, equal bytes on the read set): if one step continues, so does the other, and the two
  post-states are **one `HostEff` applied to the two pre-call states** (same `sideR`, same `gas.g`).
* **`low_of_sideR`**: `sideR` + `gas.g` equality is exactly the host-part half of `Low` — the σ-thread
  (`SigJ`) plus `RelW.gas` provide it; the rest of `Low` (arguments, bytes read) is the row's
  consumed STK/HOSTB messages (named `HostReadCovered` in `Main/HostSigmaBridge.lean`).
* **`pinned_cont_g`**: hence the refutation pattern of `HostVacuity.not_rowSpecSeg_of_sigma` (two
  related pre-states, both continuing, *different* `gas.g`) cannot occur among the pre-states the
  σ-pinned premise ranges over, once the read set is covered.
* **`Vacuity` instance** (spec level, `decide`): on `HostVacuity`'s `block_index` program, `sA` and a
  σ-twin `sC` (same `sideR`, different Wasm-visible junk: an extra stack entry below the call,
  different globals) step to corresponding states (same `g`, same pushed value), checked both by
  evaluation and by `step_host_two_run`; while the pair `(sA, sB)` that refutes the unpinned premise
  differs in `sideR` (`sideR_sA_ne_sB`), i.e. is excluded by the pin.
-/

namespace WasmBase
namespace TwoRun
open NearSpecV3.Wasm
open HostFoot
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. `Low` under frame and gas changes -/

theorem low_setFrame {A : Nat → Prop} {k : Nat} {s s' : St} (h : Low A k s s') (f f' : Frame) :
    Low A k (setFrame s f) (setFrame s' f') := by
  have e1 : ∀ (u : St) (g : Frame), hostR (setFrame u g) = hostR u := by
    intro u g; unfold setFrame; split <;> rfl
  have e2 : ∀ (u : St) (g : Frame), (setFrame u g).stack = u.stack := by
    intro u g; unfold setFrame; split <;> rfl
  have e3 : ∀ (u : St) (g : Frame), (setFrame u g).pages = u.pages := by
    intro u g; unfold setFrame; split <;> rfl
  refine ⟨by rw [e1, e1]; exact h.host, by rw [e2]; exact h.kle, by rw [e2]; exact h.kle', ?_,
    agree_congr h.mem (e3 _ _) (e3 _ _)⟩
  simp only [topK, e2]; exact h.top

/-- The host part is `sideR` plus the gas register. -/
theorem hostR_of_sideR {s s' : St} (h : sideR s = sideR s') (hg : s.gas.g = s'.gas.g) : hostR s = hostR s' := by
  have hg' : s.gas = s'.gas := by
    have := congrArg St.gas h
    simp only [sideR, StepSide.sideG, hostSide] at this
    cases e1 : s.gas; cases e2 : s'.gas
    rw [e1, e2] at this; rw [e1, e2] at hg
    simp only [Gas.mk.injEq] at this hg ⊢
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, hg, this.2.2.2.2.2⟩
  have := h
  simp only [sideR, StepSide.sideG, hostSide, St.mk.injEq] at this
  simp only [hostR, hostSide, St.mk.injEq]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, hg', this.2.2.2.2.2.2.2.2.2.2⟩

/-- **The host-part half of `Low` from the σ-thread**: equal `sideR` and gas register. -/
theorem low_of_sideR {A : Nat → Prop} {k : Nat} {s s' : St} (h : sideR s = sideR s') (hg : s.gas.g = s'.gas.g)
    (hk : k ≤ s.stack.size) (hk' : k ≤ s'.stack.size) (htop : topK k s = topK k s') (hm : Agree A s s') :
    Low A k s s' :=
  ⟨hostR_of_sideR h hg, hk, hk', htop, hm⟩

/-! ## 2. `charge` with a constant fee -/

theorem charge_two {A : Nat → Prop} {k : Nat} {s s' : St} (h : Low A k s s') (fee : Fee) {x : St}
    (hc : charge s fee 0 = .cont x) :
    ∃ G, x = { s with gas := G } ∧ charge s' fee 0 = .cont { s' with gas := G } := by
  obtain ⟨eg, -⟩ := Tw.eqs (tw_start h)
  unfold charge at hc ⊢
  dsimp only at hc ⊢
  rw [eg]
  split at hc
  · split at hc
    · cases hc
    · split at hc <;> cases hc
  · split at hc
    · split at hc
      · cases hc
      · split at hc <;> cases hc
    · cases hc
      refine ⟨_, rfl, ?_⟩
      rw [if_neg ‹_›, if_neg ‹_›]

/-! ## 3. The step -/

/-- The spec `step` at a `call` of an import, by the fee shape of the instruction. -/
theorem step_call (cfg : NearCfg) (p : Prepared) {s : St} {f : Frame} {rest : List Frame}
    (hfr : s.frames = f :: rest) {pf : PFunc} (hpf : p.funcs[f.fn]? = some pf) {fi : Nat}
    (hcode : pf.code[f.pc]? = some (.call fi)) (himp : fi < p.m.imports.size)
    {name : String} (hname : p.m.imports[fi].name = name) :
    (pf.gas[f.pc]? = some none → step cfg p s = callHost (setFrame s { f with pc := f.pc + 1 }) name) ∧
    (∀ kd fee, kd ≠ .linear → pf.gas[f.pc]? = some (some (kd, fee)) →
      step cfg p s = match charge s fee 0 with
        | .cont s1 => callHost (setFrame s1 { f with pc := f.pc + 1 }) name
        | r => r) := by
  have hexec : ∀ (u : St), exec cfg p u f pf (.call fi) = callHost (setFrame u { f with pc := f.pc + 1 }) name := by
    intro u; simp only [exec, callFunc, dif_pos himp, hname]
  refine ⟨fun hg => ?_, fun kd fee hkd hg => ?_⟩
  · unfold step; rw [hfr]; simp only [hpf, hcode, hg]; exact hexec s
  · unfold step; rw [hfr]; simp only [hpf, hcode, hg, hkd, if_false]
    cases charge s fee 0 <;> simp only [hexec]


/-- **`step_host_two_run`.**  At a `call` of an import `name` (an arm of `hostCall`) with a constant
fee, from two states at the same code position that are low-equivalent on the arm's read set: if the
step continues from `s`, it continues from `s'`, and the two post-states are one effect applied to
the two pre-call states (`u`, `u'`: the states after the fee, with the frame advanced). -/
theorem step_host_two_run (cfg : NearCfg) (p : Prepared) {s s' : St} {f f' : Frame} {rest rest' : List Frame}
    (hfr : s.frames = f :: rest) (hfr' : s'.frames = f' :: rest') (hfn : f'.fn = f.fn) (hpc : f'.pc = f.pc)
    {pf : PFunc} (hpf : p.funcs[f.fn]? = some pf) {fi : Nat} (hcode : pf.code[f.pc]? = some (.call fi))
    (himp : fi < p.m.imports.size) (hlin : ∀ kd fee, pf.gas[f.pc]? = some (some (kd, fee)) → kd ≠ .linear)
    {name : String} (hname : p.m.imports[fi].name = name) (hn : (hostCall name).isSome)
    {A : Nat → Prop} {k : Nat} (hL : Low A k s s') (hk : nargs name ≤ k) (hA : ∀ b, readSetOf name s b → A b)
    {x : St} (hx : step cfg p s = .cont x) :
    ∃ (x' : St) (eff : HostEff) (G : Gas), step cfg p s' = .cont x' ∧
      x = eff.apply (setFrame { s with gas := G } { f with pc := f.pc + 1 }) ∧
      x' = eff.apply (setFrame { s' with gas := G } { f' with pc := f'.pc + 1 }) ∧
      sideR x = sideR x' ∧ x.gas.g = x'.gas.g := by
  have hpf' : p.funcs[f'.fn]? = some pf := by rw [hfn]; exact hpf
  have hcode' : pf.code[f'.pc]? = some (.call fi) := by rw [hpc]; exact hcode
  -- the call itself, from a charged pair
  have key : ∀ G, (callHost (setFrame { s with gas := G } { f with pc := f.pc + 1 }) name = .cont x) →
      ∃ (x' : St) (eff : HostEff), callHost (setFrame { s' with gas := G } { f' with pc := f'.pc + 1 }) name = .cont x' ∧
        x = eff.apply (setFrame { s with gas := G } { f with pc := f.pc + 1 }) ∧
        x' = eff.apply (setFrame { s' with gas := G } { f' with pc := f'.pc + 1 }) ∧
        sideR x = sideR x' ∧ x.gas.g = x'.gas.g := by
    intro G hc
    have hL1 := low_setFrame (low_gas hL G) { f with pc := f.pc + 1 } { f' with pc := f'.pc + 1 }
    have hst : (setFrame { s with gas := G } { f with pc := f.pc + 1 }).stack = s.stack := by
      unfold setFrame; split <;> rfl
    have hpg : (setFrame { s with gas := G } { f with pc := f.pc + 1 }).pages = s.pages := by
      unfold setFrame; split <;> rfl
    have hA1 : ∀ b, readSetOf name (setFrame { s with gas := G } { f with pc := f.pc + 1 }) b → A b := by
      rw [readSetOf_congr name hst (by rw [hpg])]; exact hA
    obtain ⟨x', eff, h1, -, h2, h3, h4, h5⟩ := callHost_two_run_cont hL1 hn hk hA1 hc
    exact ⟨x', eff, h1, h2, h3, h4, h5⟩
  obtain ⟨n1, n2⟩ := step_call cfg p hfr hpf hcode himp hname
  obtain ⟨m1, m2⟩ := step_call cfg p hfr' hpf' hcode' himp hname
  cases hg : pf.gas[f.pc]? with
  | none =>
    exfalso
    unfold step at hx; rw [hfr] at hx; simp only [hpf, hcode, hg] at hx; cases hx
  | some o =>
    have hg' : pf.gas[f'.pc]? = some o := by rw [hpc]; exact hg
    cases o with
    | none =>
      rw [n1 hg] at hx
      rw [m1 hg']
      obtain ⟨eg, -⟩ := Tw.eqs (tw_start hL)
      have e1 : ({ s with gas := s.gas } : St) = s := rfl
      have e2 : ({ s' with gas := s.gas } : St) = s' := by rw [← eg]
      obtain ⟨x', eff, h1, h2, h3, h4, h5⟩ := key s.gas (by rw [e1]; exact hx)
      rw [e2] at h1 h3
      exact ⟨x', eff, s.gas, h1, by rw [e1]; exact h2, by rw [e2]; exact h3, h4, h5⟩
    | some kf =>
      obtain ⟨kd, fee⟩ := kf
      have hkd := hlin kd fee hg
      rw [n2 kd fee hkd hg] at hx
      rw [m2 kd fee hkd hg']
      cases hc : charge s fee 0 with
      | cont s1 =>
        rw [hc] at hx
        obtain ⟨G, rfl, hc'⟩ := charge_two hL fee hc
        rw [hc']
        obtain ⟨x', eff, h1, h2, h3, h4, h5⟩ := key G hx
        exact ⟨x', eff, G, h1, h2, h3, h4, h5⟩
      | _ => rw [hc] at hx; cases hx

/-! ## 4. The refutation pattern of `HostVacuity` is excluded on the σ-thread -/

/-- **On the σ-thread, with the read set covered, two continuing host steps land at the same gas
register** (and host side): the hypothesis `hne` of `not_rowSpecSeg_of_sigma` is unsatisfiable for
pre-states the pinned premise ranges over. -/
theorem pinned_cont_g (cfg : NearCfg) (p : Prepared) {σ : Nat → St} {t : Nat} {s s' : St}
    (hJ : SigJ σ t s) (hJ' : SigJ σ t s') (hg : s.gas.g = s'.gas.g)
    {f f' : Frame} {rest rest' : List Frame}
    (hfr : s.frames = f :: rest) (hfr' : s'.frames = f' :: rest') (hfn : f'.fn = f.fn) (hpc : f'.pc = f.pc)
    {pf : PFunc} (hpf : p.funcs[f.fn]? = some pf) {fi : Nat} (hcode : pf.code[f.pc]? = some (.call fi))
    (himp : fi < p.m.imports.size) (hlin : ∀ kd fee, pf.gas[f.pc]? = some (some (kd, fee)) → kd ≠ .linear)
    {name : String} (hname : p.m.imports[fi].name = name) (hn : (hostCall name).isSome)
    {k : Nat} (hk : nargs name ≤ k) (hks : k ≤ s.stack.size) (hks' : k ≤ s'.stack.size)
    (htop : topK k s = topK k s') (hm : Agree (readSetOf name s) s s')
    {x x' : St} (hx : step cfg p s = .cont x) (hx' : step cfg p s' = .cont x') :
    x.gas.g = x'.gas.g ∧ sideR x = sideR x' := by
  have hL : Low (readSetOf name s) k s s' := low_of_sideR (hJ.trans hJ'.symm) hg hks hks' htop hm
  obtain ⟨y, -, -, h1, -, -, h4, h5⟩ := step_host_two_run cfg p hfr hfr' hfn hpc hpf hcode himp hlin hname hn hL hk
    (fun _ h => h) hx
  rw [hx'] at h1; cases h1
  exact ⟨h5, h4⟩

/-! ## 5. The concrete instance: `HostVacuity`'s `block_index` program -/

namespace Vacuity2
open WasmBase.Vacuity

/-- A σ-twin of `sA`: the same host side (`sideR`) and gas register, different Wasm-visible junk
the host call does not read (a stack entry below the call, a global). -/
def sC : St := { sA with stack := #[.i64 7], globals := #[.i32 5] }

theorem sideR_sA_sC : sideR sA = sideR sC := rfl
theorem g_sA_sC : sA.gas.g = sC.gas.g := rfl

/-- The pair that refutes the unpinned premise is excluded by the pin: different host sides. -/
theorem sideR_sA_ne_sB : sideR sA ≠ sideR sB := by
  intro h
  have := congrArg (fun s : St => s.gas.burnt) h
  simp only [sideR, StepSide.sideG, hostSide, sA, sB, gA] at this
  exact absurd this (by decide)

/-- Evaluated: the σ-twins step to the same gas register and push the same value. -/
theorem gOf_C : gOf (step {} p0 sC) = some 999999735231889 := by decide
theorem topOf_C : topOf (step {} p0 sC) = some 10 := by decide

/-- **The σ-pinned premise is satisfiable and non-trivially inhabited at a continuing host call**:
`sA` and its σ-twin `sC` both continue, to equal gas registers and host sides, and the generic
`step_host_two_run` applies (`block_index`: no arguments, empty read set). -/
theorem twin_witness :
    sideR sA = sideR sC ∧ sA.gas.g = sC.gas.g ∧ HostFoot.vis sA ≠ HostFoot.vis sC ∧
    ∃ tA tC, step {} p0 sA = .cont tA ∧ step {} p0 sC = .cont tC ∧ tA.gas.g = tC.gas.g ∧
      sideR tA = sideR tC ∧ tA.stack.back?.map Val.bits = some 10 ∧ tC.stack.back?.map Val.bits = some 10 := by
  obtain ⟨tA, hA, gA'⟩ := cont_of_gOf gOf_A
  obtain ⟨tC, hC, gC'⟩ := cont_of_gOf gOf_C
  have h1 := topOf_A; have h2 := topOf_C
  rw [hA] at h1; rw [hC] at h2
  have hL : Low (readSetOf "block_index" sA) 0 sA sC :=
    low_of_sideR rfl rfl (Nat.zero_le _) (Nat.zero_le _) rfl
      ⟨fun i h => by simp [sA] at h, fun i h => by simp [sC, sA] at h, rfl, fun _ h => h.elim⟩
  obtain ⟨y, -, -, hy, -, -, h4, h5⟩ := step_host_two_run (rest := []) (rest' := []) {} p0 rfl rfl rfl rfl
    (pf := pf0) rfl (fi := 0) rfl (by decide) (by intro kd fee h; cases h) (name := "block_index") rfl rfl hL
    (Nat.le_refl _) (fun _ h => h) hA
  rw [hC] at hy; cases hy
  refine ⟨rfl, rfl, fun h => ?_, tA, tC, hA, hC, h5, h4, h1, h2⟩
  have := congrArg Vis.globals h
  simp [HostFoot.vis, sA, sC] at this

end Vacuity2

#print axioms step_host_two_run
#print axioms pinned_cont_g
#print axioms Vacuity2.sideR_sA_ne_sB
#print axioms Vacuity2.twin_witness

end TwoRun
end WasmBase
