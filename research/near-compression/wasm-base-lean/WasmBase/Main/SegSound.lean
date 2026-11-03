import WasmBase.Main.SegLink

/-!
# WasmBase.Main.SegSound — segment soundness with the CUTO link discharged (E2E M4b, S3)

`seg_sound_cut_holds` (`Main/SegCuto.lean`) left the CUTO link as a premise of its last conjunct.
`cuto_link` (`Main/SegLink.lean`) proves it from the trace, so here the out-boundary digest is an
unconditional conclusion:

**`seg_sound_cut_link`**: for a cut segment `c` (`CutSeg`, the rows and bus facts of
`exec_of_rows_cut`) of a `HoldsX (wasmBaseSegAir …)` trace, from a state related to the in-boundary
by `BndC` with a well-formed register file, with the per-row clause facts, there is `sN` with
`seg n s0 = .cont sN`, `run` continuing from `sN`, `BndC` at the out-boundary, **CUTO's hashed list
equal to `cutView X sN`**, the public `ctx_out = cutDigest (cutView X sN)` (given S2's stream lemma in
the form `ctxOut = cutDigest (cutoList tr)`), and every view entry `MsgWF`.

Named hypotheses (beyond `seg_sound_cut`'s and S2's):
* `CutoHiLimbs tr` — SHA chip limb bound on CUTO's `hi` halves (S1);
* `hin`, `FinSplit tr pub c.fin` — the bus-level split of the final live list: CUTO's consumptions are
  in it, and it is CUTO ∪ MEMB (space 3) ∪ SEGB (space 7) ∪ DROP consumptions.  These are what the
  segment's CH-bus decomposition (the open trace → `CutSeg` instantiation, below) yields;
* `TombDead tr pub c.fin` — every activation a taken `RET` tombstones is `< 2^28`, non-zero, and has
  no live call record at the cut.  An execution fact (ids are `CALL` times, a returned activation's
  record is consumed and its id never reused); proving it needs the per-row execution trace that
  `exec_of_rows_cut` builds internally but does not export.

Open: the trace → `CutSeg` instantiation for `wasmBaseSegAir` (the segment analogue of
`m2_hst`/`m2_hch`/`rowFactsSegMap_m2`, adding SEGB/CUTI/CUTO/DROP/MEMB/MPATH/CIDMAP traffic), which
would also discharge `hin`/`FinSplit`.
-/

namespace WasmBase

open ZkFormal.Algebra
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-- **Segment soundness (cut case) with the CUTO link discharged.** -/
theorem seg_sound_cut_link (X : Ctx) (hnd : X.M.fns.Nodup) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (Hh : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hl : CutoHiLimbs tr)
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
    fun y => (cuto_link Hh hl hIds hin hS hT y).trans (hv y)
  have e := ctx_out_eq (cuto_sorted Hh hl) hset (cutView_nodup X h6)
  exact ⟨sN, h1, h2, hB, e, by rw [hsha, e], cutView_wf (cuto_wf Hh hl) hset⟩

#print axioms seg_sound_cut_link

end WasmBase
