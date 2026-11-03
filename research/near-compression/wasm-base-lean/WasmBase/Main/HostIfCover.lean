import WasmBase.Main.HostIf
import WasmBase.Main.HostSigmaBridge

/-!
# WasmBase.Main.HostIfCover — `HostIf` + FOOT2's two-run footprint ⇒ the σ-pinned HOST premises

`Main/HostIf.lean` reduced `HoldRowSσ`/`HostRelyσ` for the thread `thread hts σc` to `HostIf` (the
bus contract) + `HostFootprint` (named) + `HostRowsFlat` (named).  With FOOT2's results
(`Main/HostTwoRun*.lean`, `Main/HostSigmaBridge.lean`) this file:

* **`holdRowSσ_of_hostIf_cover`** — `HoldRowSσ X tr pub sg (thread hts σc)` from `HostIf`, FOOT2's
  coverage in its own form (`HostCoverT`: at every honest pre-state of every HOST row on the thread,
  `HostCallAt` + `HostReadCovered` + `HostEffRely`), and the flat row facts.  The witness of
  `HostIf.ans` is the honest pre-state of `holdRowSσ_of_cover`; the `HostTransfer` half of
  `HostFootprint` is no longer needed (FOOT2's `hostStepTwin_of_cover` replaces it).
* **`hostRowsFlat_of`** — `HostRowsFlat` from the HOST row's STATE shape (`host_rowIn`/`host_rowOut`:
  `halt0`, `tsOut`, `gasOut`) plus two named AIR facts: the fee column bound (`HostFeeOK`) and the
  producer/consumer times and no-duplicate productions of the row's fused CH traffic (`HostRowsTimes`).
* **`seg_sound_hostIf'`** — `seg_sound_σ` relative to `HostIf` + `HostCoverT` + `HostRegFootT` (the
  register half of `HostFootprint`) + `HostFeeOK` + `HostRowsTimes`, pins `σc 0` / `σc m`.

## Why the register half stays named

`HostRelyσ.reg`/`.wf` are `RowQJ`s: they quantify over related pre-states at **every** gas segment
`(a, b)`, while the two-run lemma needs the two pre-states to have the same gas register (`Low`,
`low_of_sideR`), which only the row's own segment `sg (ts)` pins.  So `HostRegFootT` (a continuing
step from a thread pre-state lands at `(σc (j+1)).registers`) is derivable from FOOT2's lemma only at
the row's segment; at other segments it needs either a gas-independent register lemma for the arms
or a segment-pinned `RowQJ` in the induction (`exec_rowsJ` only ever uses it at `sg`).
-/

namespace WasmBase
namespace HostIf

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
open HostFoot StepSide TwoRun
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. Coverage, in FOOT2's form -/

/-- **Read coverage for every HOST row** (FOOT2's `HostCallAt` + `HostReadCovered` + `HostEffRely`),
at every honest pre-state on the thread `σ`. -/
def HostCoverT (X : Ctx) (tr : Trace) (pub : List F) (sg : Nat → Nat × Nat) (σ : Nat → St) : Prop :=
  ∀ r, HAct tr pub r →
    ∀ (EH : Env) (sH : St) (fH : Frame) (tpsH tplH : Nat → Nat) (tH pcH SH : Nat) (liveH : Msg → Prop),
      WasmBase.RowPre X (SigJ σ) (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (sg (rowNat tr 22 r 1))
        EH sH fH tpsH tplH tH pcH SH liveH →
      ∃ (name : String) (k : Nat),
        HostCallAt X (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (sg (rowNat tr 22 r 1)) σ name ∧
        HostReadCovered X σ (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (sg (rowNat tr 22 r 1)) name k sH fH ∧
        HostEffRely X σ (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (prodCHS tr pub (22, r))
          (sg (rowNat tr 22 r 1)) (sg (rowNat tr 22 r 1 + 1)) sH liveH

/-- The register half of `HostFootprint`, alone. -/
def HostRegFootT (X : Ctx) (tr : Trace) (pub : List F) (hts : List Nat) (σc : Nat → St) : Prop :=
  ∀ r, HAct tr pub r →
    HostRegFoot X (σc (rank hts (rowNat tr 22 r 1))) (σc (rank hts (rowNat tr 22 r 1) + 1))
      (rowInM tr pub (22, r)) (consCHS tr pub (22, r))

/-! ## 2. `HoldRowSσ` from `HostIf` + coverage -/

/-- **`HoldRowSσ` from the host contract and FOOT2's coverage.** -/
theorem holdRowSσ_of_hostIf_cover {X : Ctx} {tr : Trace} {pub : List F} {sg : Nat → Nat × Nat}
    {hts : List Nat} {σc : Nat → St} (hI : HostIf X tr pub sg hts σc)
    (hcov : HostCoverT X tr pub sg (thread hts σc)) (hfl : HostRowsFlat X tr pub) (hg64 : X.g0 < 2 ^ 64) :
    HoldRowSσ X tr pub sg (thread hts σc) := by
  refine holdRowSσ_of_cover (fun r hr ha => ?_) (fun r hr ha => hfl r ⟨hr, ha⟩)
  have hA : HAct tr pub r := ⟨hr, ha⟩
  obtain ⟨E0, w, f0, tps0, tpl0, t0, pc0, S0, live0, ⟨R0, hin0, hl0, ht0, hS0⟩, hw, hpost⟩ := hI.ans r hA
  obtain ⟨e0, e1⟩ := thread_at_host hI hA (host_time_mod hin0)
  have hpre : WasmBase.RowPre X (SigJ (thread hts σc)) (rowInM tr pub (22, r)) (consCHS tr pub (22, r))
      (sg (rowNat tr 22 r 1)) E0 w f0 tps0 tpl0 t0 pc0 S0 live0 :=
    ⟨R0, show sideR w = thread hts σc t0 by rw [hw, e0], hin0, hl0, ht0, hS0, hg64⟩
  have hspec : RowSpecAt X (SigJ (thread hts σc)) (rowOutM tr pub (22, r)) (consCHS tr pub (22, r))
      (prodCHS tr pub (22, r)) (sg (rowNat tr 22 r 1)) (sg (rowNat tr 22 r 1 + 1)) w f0 tps0 tpl0 t0 S0 live0 := by
    obtain ⟨k', pc', fee, hb, sb', cid', a1, a2, a3, a4⟩ := hpost
    refine ⟨k', pc', fee, hb, sb', cid', a1, a2, a3, fun hg => ?_⟩
    obtain ⟨c0, c1, c2⟩ := a4 hg
    refine ⟨fun e => ?_, c1, c2⟩
    obtain ⟨s', hs', hR, hσ⟩ := c0 e
    exact ⟨s', hs', hR, show sideR s' = thread hts σc (t0 + 1) by rw [hσ, e1]⟩
  obtain ⟨name, k, hc, hcv, hrl⟩ := hcov r hA E0 w f0 tps0 tpl0 t0 pc0 S0 live0 hpre
  exact ⟨E0, w, f0, tps0, tpl0, t0, pc0, S0, live0, name, k, hpre, hspec, hc, hcv, hrl⟩

/-- **`HostRelyσ` from the host contract and the register half alone** (`hostRelyσ_of_hostIf` reads
only `HostFootprint.regs`). -/
theorem hostRelyσ_of_hostIf_regs {X : Ctx} {tr : Trace} {pub : List F} {sg : Nat → Nat × Nat}
    {hts : List Nat} {σc : Nat → St} (hI : HostIf X tr pub sg hts σc) (hreg : HostRegFootT X tr pub hts σc) :
    HostRelyσ X tr pub (thread hts σc) := by
  have key : ∀ ρ ∈ actListM2 tr pub, ρ.1 = 22 → ∃ r, ρ = (22, r) ∧ HAct tr pub r := by
    intro ρ hρ h22
    obtain ⟨t, r⟩ := ρ
    simp only at h22
    subst h22
    rcases mem_actListM2 hρ with ⟨-, hr, ha⟩ | ⟨htI, -, -⟩
    · exact ⟨r, rfl, hr, ha⟩
    · exfalso; rcases htI with ⟨_, h⟩ | h | h | h <;> simp_all
  -- the register files at a HOST row's pre-state and continuing post-state
  have regs : ∀ r, HAct tr pub r → ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat)
      (live : Msg → Prop) (a b : Nat) (s' : St), RelW X E s f tps tpl t pc S live a b →
      SigJ (thread hts σc) t s → rowInM tr pub (22, r) = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
      (∀ x ∈ consCHS tr pub (22, r), live x) → step X.cfg X.p s = .cont s' →
      s.registers = (σc (rank hts (rowNat tr 22 r 1))).registers ∧
        s'.registers = (σc (rank hts (rowNat tr 22 r 1) + 1)).registers := by
    intro r hA E s f tps tpl t pc S live a b s' R hJ hin hl hs
    obtain ⟨e0, -⟩ := thread_at_host hI hA (host_time_mod hin)
    have hJ' : sideR s = σc (rank hts (rowNat tr 22 r 1)) := by
      have : sideR s = thread hts σc t := hJ
      rw [this, e0]
    refine ⟨?_, hreg r hA E s f tps tpl t pc S live a b s' R hJ' hin hl hs⟩
    have : (sideR s).registers = s.registers := rfl
    rw [← this, hJ']
  refine ⟨fun ρ hρ h22 => ?_, fun ρ hρ h22 => ?_⟩
  · obtain ⟨r, rfl, hA⟩ := key ρ hρ h22
    intro E s f tps tpl t pc S live a b s' R hJ hin hl hs hQ
    obtain ⟨e1, e2⟩ := regs r hA E s f tps tpl t pc S live a b s' R hJ hin hl hs
    obtain ⟨tpr, htpr⟩ := hQ
    rw [e1] at htpr
    obtain ⟨tpr', h'⟩ := hI.reg r hA live tpr htpr hl
    exact ⟨tpr', by rw [e2]; exact h'⟩
  · obtain ⟨r, rfl, hA⟩ := key ρ hρ h22
    intro E s f tps tpl t pc S live a b s' R hJ hin hl hs hw
    obtain ⟨-, e2⟩ := regs r hA E s f tps tpl t pc S live a b s' R hJ hin hl hs
    refine ⟨step_regIds hs hw.1, ?_⟩
    rw [e2]; exact hI.cap _

/-! ## 3. The flat row facts of a HOST row -/

/-- The HOST row's fee column is a step fee (`≤ maxFee`): the code-record binding of the call's fee
(named, AIR/`CodeOK` side). -/
def HostFeeOK (X : Ctx) (tr : Trace) (pub : List F) : Prop :=
  ∀ r, HAct tr pub r → rowNat tr 22 r 4 ≤ X.maxFee

/-- The producer/consumer times and no-duplicate productions of a HOST row's fused CH traffic
(stack arguments and result, HOSTB bytes, REG-C net traffic, gas register) — named AIR facts. -/
def HostRowsTimes (tr : Trace) (pub : List F) : Prop :=
  ∀ r, HAct tr pub r →
    (∀ x ∈ consCHS tr pub (22, r), ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((x.tp + 1 + n : Nat) : F) = lvl (rowInM tr pub (22, r))) ∧
    (∀ x ∈ prodCHS tr pub (22, r), x.tp < P ∧ ((x.tp : Nat) : F) = lvl (rowInM tr pub (22, r))) ∧
    (prodCHS tr pub (22, r)).Nodup

/-- **`HostRowsFlat` from the STATE shape + `HostFeeOK` + `HostRowsTimes`.**  `halt0`, `tsOut`,
`gasOut` are the HOST row's STATE messages (`host_rowIn`, `host_rowOut`). -/
theorem hostRowsFlat_of {X : Ctx} {tr : Trace} {pub : List F} (hfee : HostFeeOK X tr pub)
    (htm : HostRowsTimes tr pub) : HostRowsFlat X tr pub := by
  intro r hA
  obtain ⟨hc, hp, hn⟩ := htm r hA
  have eI : rowInM tr pub (22, r) = rowIn Host.table tr pub 22 r := rfl
  have eO : rowOutM tr pub (22, r) = rowOut Host.table tr pub 22 r := rfl
  refine ⟨?_, ?_, ⟨rowNat tr 22 r 4, hfee r hA, ?_⟩, hc, hp, hn⟩
  · rw [eI, host_rowIn]; rfl
  · rw [eI, eO, host_rowIn, host_rowOut]; rfl
  · rw [eI, eO, host_rowIn, host_rowOut]; rfl

/-! ## 4. Segment soundness relative to the contract and coverage -/

/-- **`seg_sound_hostIf'`**: `seg_sound_hostIf` with `HostFootprint` replaced by FOOT2's coverage
(`HostCoverT`) and its register half (`HostRegFootT`), and `HostRowsFlat` by `HostFeeOK` +
`HostRowsTimes`. -/
theorem seg_sound_hostIf' (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {hts : List Nat} {σc : Nat → St} (hI : HostIf X.toCtx tr pub sg hts σc)
    (hcov : HostCoverT X.toCtx tr pub sg (thread hts σc)) (hreg : HostRegFootT X.toCtx tr pub hts σc)
    (hfee : HostFeeOK X.toCtx tr pub) (htm : HostRowsTimes tr pub)
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
      (initS tr pub)) (hw0 : RegWF s0) (hσ0 : sideR s0 = σc 0) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    ∃ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN ∧
      (∀ m, run X.toCtx.cfg X.toCtx.p ((actListM2 tr pub).length + m) s0 = run X.toCtx.cfg X.toCtx.p m sN) ∧
      BndC X.toCtx sg sN (pub.getD pubTOut 0).toNat (pub.getD pubSOut 0).toNat (segFinM tr pub) (finS tr pub) ∧
      cutoList tr = cutView X.toCtx sN ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxOut = SegSha.limbsF d ∧
        SegSha.wbytes d = cutDigest (cutView X.toCtx sN)) ∧
      (∀ y ∈ cutView X.toCtx sN, MsgWF y) ∧
      RegWF sN ∧ sideR sN = σc hts.length := by
  have hP := P_val
  have hfl := hostRowsFlat_of hfee htm
  have hsz : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 < P := by omega
  have hInstr : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfacts X H hcode hfunc htI hr ha
  have htsO : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1 := by
    intro ρ hρ
    by_cases h22 : ρ.1 = 22
    · obtain ⟨t, r⟩ := ρ
      simp only at h22
      subst h22
      rcases mem_actListM2 hρ with ⟨-, hr, ha⟩ | ⟨htI, -, -⟩
      · exact (hfl r ⟨hr, ha⟩).tsOut
      · exfalso; rcases htI with ⟨_, h⟩ | h | h | h <;> simp_all
    · exact (RowFactsSeg.toFlat (rowFactsSegMap_instr X.toCtx hInstr hkeep hρ h22)).tsOut
  have hrange := hostTimes_range H htsO hsz hI
  have hin : sideR s0 = thread hts σc ((pub.getD pubTIn 0).toNat + 1) := by
    rw [hσ0, thread_in (fun x hx => (hrange x hx).1) (by omega)]
  obtain ⟨hlenEq, sN, h1, h2, h3, h4, h5, h6, hwN, hσN⟩ :=
    seg_sound_σ X H hC hl hcode hfunc hb hg hkeep (sigKeep_of_hostIf_seg H htsO hsz hI)
      (holdRowSσ_of_hostIf_cover hI hcov hfl hg64) (hostRelyσ_of_hostIf_regs hI hreg) hst0 hlen htin hfeeN
      hstepgas hg64 hinit hT h0 hw0 hin
  refine ⟨hlenEq, sN, h1, h2, h3, h4, h5, h6, hwN, ?_⟩
  rw [hσN, thread_out (fun x hx => by have := (hrange x hx).2; omega) (by omega)]

#print axioms holdRowSσ_of_hostIf_cover
#print axioms hostRelyσ_of_hostIf_regs
#print axioms hostRowsFlat_of
#print axioms seg_sound_hostIf'

end HostIf
end WasmBase
