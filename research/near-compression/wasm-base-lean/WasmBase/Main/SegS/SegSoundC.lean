import WasmBase.Main.SegSoundC
import WasmBase.Main.SegS.SegLinkage
/-!
# WasmBase.Main.SegS.SegSoundC — `SegSoundC`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegSoundC.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- **`seg_sound_cS`: segment soundness (cut case), `TombDead` discharged, `HostBLinked` reduced to
`linked`, the out-state's `RegWF` and `InDom` (given the out geometry) concluded.** -/
theorem seg_sound_cS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIfS SegSha.compressW nloc ngl pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hbL : HostBLinkedL tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X.toCtx tr pub sg)
    (hrely : HostRely X.toCtx tr pub)
    (hst0 : pub.getD Boundary.pubStatus 0 = 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (h0 : BndC X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hw0 : RegWF s0) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    ∃ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN ∧
      (∀ m, run X.toCtx.cfg X.toCtx.p ((actListM2 tr pub).length + m) s0 = run X.toCtx.cfg X.toCtx.p m sN) ∧
      BndC X.toCtx sg sN (pub.getD pubTOut 0).toNat (pub.getD pubSOut 0).toNat (segFinM tr pub) (finS tr pub) ∧
      cutoList tr = cutView X.toCtx sN ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxOut = SegSha.limbsF d ∧
        SegSha.wbytes d = cutDigest (cutView X.toCtx sN)) ∧
      (∀ y ∈ cutView X.toCtx sN, MsgWF y) ∧
      RegWF sN ∧ (MemGeom pub sN → WasmView.InDom X.toCtx sN) := by
  have hP := P_val
  have hrk : InstrRegKeep X.toCtx tr pub := seg_instr_regKeepS X H hcode
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfactsS X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMap_seg X.toCtx hI hkeep hhold
  have hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1 :=
    fun ρ hρ => (hrows ρ hρ).tsOut
  have hb : HostBLinked tr pub := hostBLinked_ofS H hts (by omega) hbL
  have hT := seg_tombDeadS X H hcode hfunc hb hg hkeep hhold 0 (by omega) (by rw [hst0]; rfl) hlen htin hfeeN
    hstepgas hg64 hinit h0.1
  obtain ⟨hlenEq, sN, h1, h2, h3, h4, h5, h6⟩ :=
    seg_soundS X H hC hl hcode hfunc hb hg hkeep hhold hrely hst0 hlen htin hfeeN hstepgas hg64 hinit hT h0 hw0
  -- `RegWF` through the segment
  have ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P := by omega
  have hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.toCtx.maxFee + 1) < P := by
    have e : (pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat = (actListM2 tr pub).length := by omega
    rw [e] at hfeeN; exact hfeeN
  let c := segCutS X.toCtx H hrows hb hg hst0 hinit ht hfee
  have hwfR : ∀ ρ ∈ c.act, RowQ X.toCtx (fun s _ => RegWF s) (c.inS ρ) (c.cons ρ) (c.prod ρ) := by
    intro ρ hρ
    by_cases h22 : ρ.1 = 22
    · exact hrely.wf ρ hρ h22
    · exact rowQ_regWF_keep (hrk ρ hρ h22)
  obtain ⟨-, hq⟩ := exec_of_rows_cutQ X.toCtx c.act c.inS c.outS c.cons c.prod c.init c.fin c.pcf c.N c.Sf sg
    c.st c.hst2 c.hrows c.t0 c.S0 c.m0 c.sbf c.cidf c.hst c.hch c.hinit c.hinitTp c.ht c.hfee hstepgas hg64 h0.1
    (fun s _ => RegWF s) hwfR hw0
  obtain ⟨sN', h1', -, -, hwN⟩ := hq rfl
  have e : sN' = sN := by
    have h1'' : NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN' := h1'
    rw [h1] at h1''
    cases h1''; rfl
  subst e
  exact ⟨hlenEq, sN', h1, h2, h3, h4, h5, h6, hwN, fun hG => seg_inDom X h3.1 hwN h6 (pages_lt_of_memGeom hG)⟩

/-- **`seg_sound_anyS`: segment soundness for the published status `st ≤ 2`** — a cut (`st = 0`,
`seg_sound_cS`) or a halting segment (`st ∈ {1, 2}`, `seg_sound_haltS`). -/
theorem seg_sound_anyS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIfS SegSha.compressW nloc ngl pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hbL : HostBLinkedL tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X.toCtx tr pub sg)
    (hrely : HostRely X.toCtx tr pub)
    (st : Nat) (hst2 : st ≤ 2) (hstN : pub.getD Boundary.pubStatus 0 = ((st : Nat) : F))
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (h0 : BndC X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hw0 : RegWF s0) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    (st = 0 → SegCutOut X tr pub sg s0) ∧ (st ≠ 0 → SegHaltOut X tr pub sg s0 st) := by
  have hP := P_val
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfactsS X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMap_seg X.toCtx hI hkeep hhold
  have hlenEq := seg_lenS H (fun ρ hρ => (hrows ρ hρ).tsOut) (by omega)
  have hb : HostBLinked tr pub := hostBLinked_ofS H (fun ρ hρ => (hrows ρ hρ).tsOut) (by omega) hbL
  refine ⟨hlenEq, fun h => ?_, fun h => ?_⟩
  · subst h
    exact (seg_sound_cS X H hC hl hcode hfunc hbL hg hkeep hhold hrely (by rw [hstN]; rfl) hlen htin hfeeN
      hstepgas hg64 hinit h0 hw0).2
  · exact (seg_sound_haltS X H hC hl hcode hfunc hb hg hkeep hhold st (by omega) hstN hlen htin hfeeN hstepgas
      hg64 hinit h0.1).2

end WasmBase
