import WasmBase.Main.SegSound
import WasmBase.Main.SegS.SegCutWords
/-!
# WasmBase.Main.SegS.SegSound — `SegSound`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegSound.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-- **Segment soundness (cut case) with the CUTO link discharged.** -/
theorem seg_sound_cut_linkS (X : Ctx) (hnd : X.M.fns.Nodup) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (Hh : HoldsXS nloc ngl pub tr) (hl : CutoHiLimbs tr)
    {sg : Nat → Nat × Nat} {ρ : Type} [DecidableEq ρ]
    (c : CutSeg X sg ρ) (hc : c.st = 0)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64)
    (hreg : ∀ r ∈ c.act, RowQ X (fun s live => RegC live s) (c.inS r) (c.cons r) (c.prod r))
    (hsp : ∀ r ∈ c.act, RowQ X (fun _ live => SpC live) (c.inS r) (c.cons r) (c.prod r))
    (hwf : ∀ r ∈ c.act, RowQ X (fun s _ => RegWF s) (c.inS r) (c.cons r) (c.prod r))
    {s0 : St} (h0 : BndC X sg s0 c.t0 c.S0 c.m0 c.init) (hw0 : RegWF s0)
    (hin : ∀ r, r < tr.height 31 → rowNat tr 31 r 0 = 1 → cutoMsg tr pub r ∈ c.fin)
    (hS : FinSplit tr pub c.fin) (hT : TombDead tr pub c.fin)
    (ctxOut : ArenaCore.Bytes) (hsha : ctxOut = cutDigest (cutoList tr)) :
    ∃ sN, NearSpecV3.Wasm.seg X.cfg X.p c.len s0 = .cont sN ∧
      (∀ m, run X.cfg X.p (c.len + m) s0 = run X.cfg X.p m sN) ∧
      BndC X sg sN c.stop.t c.stop.S c.stop.m c.fin ∧
      cutoList tr = cutView X sN ∧ ctxOut = cutDigest (cutView X sN) ∧ ∀ y ∈ cutView X sN, MsgWF y := by
  obtain ⟨h0b, h0r, h0s⟩ := h0
  obtain ⟨-, hcut⟩ := exec_of_rows_cutQ X c.act c.inS c.outS c.cons c.prod c.init c.fin c.pcf c.N c.Sf sg c.st
    c.hst2 c.hrows c.t0 c.S0 c.m0 c.sbf c.cidf c.hst c.hch c.hinit c.hinitTp c.ht c.hfee hstepgas hg64 h0b
    (fun s live => (RegC live s ∧ SpC live) ∧ RegWF s)
    (fun r hr => rowQ_and (rowQ_and (hreg r hr) (hsp r hr)) (hwf r hr)) ⟨⟨h0r, h0s⟩, hw0⟩
  obtain ⟨sN, h1, h2, h3, ⟨h4, h5⟩, h6⟩ := hcut hc
  have hB : BndC X sg sN c.stop.t c.stop.S c.stop.m c.fin := ⟨h3, h4, h5⟩
  obtain ⟨σ, A, hIds, -, hv⟩ := cutView_eqL hnd hB
  have hset : ∀ y, y ∈ cutoList tr ↔ y ∈ cutView X sN :=
    fun y => (cuto_linkS Hh hl hIds hin hS hT y).trans (hv y)
  have e := ctx_out_eq (cuto_sortedS Hh hl) hset (cutView_nodup X h6)
  exact ⟨sN, h1, h2, hB, e, by rw [hsha, e], cutView_wf (cuto_wfS Hh hl) hset⟩

/-- **Segment soundness (cut case), public `ctx_out`.**  As `seg_sound_cut_linkS`, with S2's chip
hypothesis `ChipIf compressW …` in place of the stream lemma: the public `ctx_out` limbs
(`pub[49 … 67)`) are those of a SHA-384 digest `d` of the spec view, `wbytes d = cutDigest (cutView X sN)`
(`ctx_out_shaS`). -/
theorem seg_sound_cut_pubS (X : Ctx) (hnd : X.M.fns.Nodup) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (Hh : HoldsXS nloc ngl pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIfS SegSha.compressW nloc ngl pub tr chip) (hl : CutoHiLimbs tr)
    {sg : Nat → Nat × Nat} {ρ : Type} [DecidableEq ρ]
    (c : CutSeg X sg ρ) (hc : c.st = 0)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64)
    (hreg : ∀ r ∈ c.act, RowQ X (fun s live => RegC live s) (c.inS r) (c.cons r) (c.prod r))
    (hsp : ∀ r ∈ c.act, RowQ X (fun _ live => SpC live) (c.inS r) (c.cons r) (c.prod r))
    (hwf : ∀ r ∈ c.act, RowQ X (fun s _ => RegWF s) (c.inS r) (c.cons r) (c.prod r))
    {s0 : St} (h0 : BndC X sg s0 c.t0 c.S0 c.m0 c.init) (hw0 : RegWF s0)
    (hin : ∀ r, r < tr.height 31 → rowNat tr 31 r 0 = 1 → cutoMsg tr pub r ∈ c.fin)
    (hS : FinSplit tr pub c.fin) (hT : TombDead tr pub c.fin) :
    ∃ sN, NearSpecV3.Wasm.seg X.cfg X.p c.len s0 = .cont sN ∧
      (∀ m, run X.cfg X.p (c.len + m) s0 = run X.cfg X.p m sN) ∧
      BndC X sg sN c.stop.t c.stop.S c.stop.m c.fin ∧ cutoList tr = cutView X sN ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub Chips.Seg.pubCtxOut = SegSha.limbsF d ∧
        SegSha.wbytes d = cutDigest (cutView X sN)) ∧ ∀ y ∈ cutView X sN, MsgWF y := by
  obtain ⟨d, h6, hW, hpub, hsha⟩ := ctx_out_shaS Hh hC hl
  obtain ⟨sN, h1, h2, hB, e, e2, hwf'⟩ := seg_sound_cut_linkS X hnd Hh hl c hc hstepgas hg64 hreg hsp hwf h0 hw0
    hin hS hT (SegSha.wbytes d) hsha
  exact ⟨sN, h1, h2, hB, e, ⟨d, h6, hW, hpub, e2⟩, hwf'⟩

end WasmBase
