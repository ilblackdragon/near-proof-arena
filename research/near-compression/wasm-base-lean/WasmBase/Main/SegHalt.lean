import WasmBase.Main.SegTomb

/-!
# WasmBase.Main.SegHalt — halting segments (E2E M4c, CORE)

`seg_sound` covers a **cut** (`halted_out = 0`).  The last segment of a call ends in a terminal step:
`SEGB` receives the final STATE message `[pc_out, t_out + 1, S_out, halted, sb_out, cidf]` with the
public `halted = pub[8] ∈ {1, 2}` (1: the entry function returned, 2: a trap).  The honest prover
(`native/wasm-base/src/tracegen.rs`, the last `snap!` with `status` and `halt_pc`;
`src/seg.rs:build`) treats that boundary **exactly like a cut**: CUTO hashes the live non-memory
messages (`canon(c1)`: the operand stack — the results —, the remaining frames' locals and records,
globals, stack budget, registers), DROP drops the dead locals, MEMB consumes the touched memory,
SEGB consumes the gas register; `pubs_of(…, c1.halted, …)` publishes the status.  So every table
behaves as at a cut, and the statement below is satisfied by honest halting segments.

* `segCutSt` — the trace → `CutSeg` instantiation for **any** published status `st ≤ 2`
  (`segCut` is the case `st = 0`).
* **`seg_sound_halt`** — from `seg_sound`'s hypotheses with `halted_out = st ∈ {1, 2}`:
  `t_out = t_in + n`; for `st = 1`, `seg n s0 = .fin sN` (and `run`), no frame left, the gas
  equation at `S_out`, the final live list `finS` = the result stack ∪ the entry frame's locals ∪
  messages outside spaces 0/16, and **the space-0 part of CUTO's hashed list is exactly the result
  stack's view** (`fieldsOf` of `stackView sN.stack`); for `st = 2`, `seg n s0 = .abort sN e` (and
  `run`) with the gas equation; and in both cases the public `ctx_out` limbs are those of the
  SHA-384 digest of CUTO's hashed list (`ctx_out_sha`).
* `TombDead` is not a premise (`seg_tombDead` holds for every status).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- **The trace → `CutSeg` instantiation for the published status `st`** (`segCut` with
`st := 0` is the cut case). -/
def segCutSt (X : Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    {sg : Nat → Nat × Nat}
    (hrows : ∀ ρ ∈ actListM2 tr pub,
      RowFactsSegMap X (rowInM tr pub ρ) (rowOutM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ) sg)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub) (st : Nat) (hst2 : st ≤ 2)
    (hstN : pub.getD Boundary.pubStatus 0 = ((st : Nat) : F))
    (hinit : (initS tr pub).Nodup)
    (ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P)
    (hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.maxFee + 1) < P) :
    CutSeg X sg (Nat × Nat) where
  act := actListM2 tr pub
  inS := rowInM tr pub
  outS := rowOutM tr pub
  cons := consCHS tr pub
  prod := prodCHS tr pub
  init := initS tr pub
  fin := finS tr pub
  pcf := pub.getD pubPcOut 0
  N := pub.getD pubTOut 0 + 1
  Sf := pub.getD pubSOut 0
  sbf := pub.getD pubSbOut 0
  cidf := tr.cell 0 0 (ix Segb.cols "cidf")
  st := st
  t0 := (pub.getD pubTIn 0).toNat
  S0 := (pub.getD pubSIn 0).toNat
  m0 := segM0 tr pub
  hst2 := hst2
  hrows := hrows
  hst := by
    have h := seg_hst H
    rw [segMF_eq, hstN] at h
    exact h
  hch := seg_hch H X hb hg
  hinit := hinit
  hinitTp := fun x hx => Nat.le_of_eq (seg_initS_tp tr pub x hx)
  ht := ht
  hfee := hfee

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- **A low CUTO row** (consumed space `< 4`, or hashed space field `< 4`: operand stack, globals)
hashes its consumed message unchanged. -/
theorem cuto_low_fields (hl : CutoHiLimbs tr) {r : Nat} (hr : r < tr.height 31) (ha : rowNat tr 31 r 0 = 1)
    (h : (cutoMsg tr pub r).space < 4 ∨ cutoF tr r 0 < 4) :
    fieldsOf (cutoMsg tr pub r) = cutoRow tr r ∧ (cutoMsg tr pub r).space = cutoF tr r 0 := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6⟩ := cutoMsg_fields H hl hr ha
  obtain ⟨-, -, b53, -, -, b56, -⟩ := cuto_kinds H hr
  have ff := cuto_fieldfacts H hl hr ha
  have hL0 : rowNat tr 31 r 56 = 0 := by
    refine Classical.byContradiction fun hL => ?_
    obtain ⟨h47, -, hc⟩ := cuto_kL_lookup H hl hr ha (by omega)
    rcases hc with ⟨-, hc⟩ | ⟨r', -, -, -, -, hc⟩ <;> omega
  obtain ⟨e1, e2⟩ := ff.1 hL0
  have h40 : rowNat tr 31 r 53 = 0 := by omega
  refine ⟨?_, by rw [f0, e2]⟩
  rw [cutoRow_eq]
  simp only [fieldsOf]
  rw [f1, f2, f3, f4, f5, f6, e2, ff.2.2.1 h40, ff.2.2.2.2 h40, f0]

end

/-- **`seg_sound_halt`: segment soundness for a halting segment** (`halted_out = st ∈ {1, 2}`), from
`seg_sound`'s hypotheses (no `HostRely`: the final view is not identified with `cutView`; no
`TombDead`: a theorem). -/
theorem seg_sound_halt (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X.toCtx tr pub sg)
    (st : Nat) (hst12 : st = 1 ∨ st = 2) (hstN : pub.getD Boundary.pubStatus 0 = ((st : Nat) : F))
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (h0 : Bnd X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    (st = 1 → ∃ sN tps tpl locs, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .fin sN ∧
      run X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .fin sN ∧ sN.frames = [] ∧
      X.toCtx.R * ((pub.getD pubSOut 0).toNat - (sg ((pub.getD pubTOut 0).toNat + 1)).1) + sN.gas.g =
        (sg ((pub.getD pubTOut 0).toNat + 1)).2 ∧
      (∃ G : Msg → Prop, (∀ x, G x → x.space ≠ 0 ∧ x.space ≠ 16) ∧
        ∀ x, x ∈ finS tr pub ↔ x ∈ stackView sN.stack tps ∨ x ∈ localView 16 locs tpl ∨ G x) ∧
      ∀ y, (y ∈ cutoList tr ∧ y.head? = some 0) ↔ ∃ x ∈ stackView sN.stack tps, fieldsOf x = y) ∧
    (st = 2 → ∃ sN e, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .abort sN e ∧
      run X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .abort sN e ∧
      X.toCtx.R * ((pub.getD pubSOut 0).toNat - (sg ((pub.getD pubTOut 0).toNat + 1)).1) + sN.gas.g =
        (sg ((pub.getD pubTOut 0).toNat + 1)).2) ∧
    (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxOut = SegSha.limbsF d ∧
      SegSha.wbytes d = cutDigest (cutoList tr)) := by
  have hP := P_val
  have hst2 : st ≤ 2 := by omega
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfacts X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMap_seg X.toCtx hI hkeep hhold
  have hlenEq := seg_len H (fun ρ hρ => (hrows ρ hρ).tsOut) (by omega)
  have ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P := by omega
  have hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.toCtx.maxFee + 1) < P := by
    have e : (pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat = (actListM2 tr pub).length := by omega
    rw [e] at hfeeN; exact hfeeN
  have hT := seg_tombDead X H hcode hfunc hb hg hkeep hhold st hst2 hstN hlen htin hfeeN hstepgas hg64 hinit h0
  let c := segCutSt X.toCtx H hrows hb hg st hst2 hstN hinit ht hfee
  obtain ⟨-, -, hf, ha⟩ := exec_of_rows_cut X.toCtx c.act c.inS c.outS c.cons c.prod c.init c.fin c.pcf
    c.N c.Sf sg c.st c.hst2 c.hrows c.t0 c.S0 c.m0 c.sbf c.cidf c.hst c.hch c.hinit c.hinitTp
    c.ht c.hfee hstepgas hg64 h0
  have eT : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 = (pub.getD pubTOut 0).toNat + 1 := by
    omega
  refine ⟨hlenEq, fun h1 => ?_, fun h2 => ?_, ctx_out_sha H hC hl⟩
  · obtain ⟨sN, tps, tpl, locs, hs, hr, hfr, hgas, G, hG, hv⟩ := hf h1
    have hgas' := hgas
    simp only [c, segCutSt] at hgas' hs hr hv
    rw [eT] at hgas'
    refine ⟨sN, tps, tpl, locs, hs, hr, hfr, hgas', ⟨G, hG, hv⟩, fun y => ⟨?_, ?_⟩⟩
    · rintro ⟨hy, hy0⟩
      simp only [cutoList, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hy
      obtain ⟨r, ⟨hr', ha'⟩, rfl⟩ := hy
      have hF0 : cutoF tr r 0 = 0 := by
        rw [cutoRow_eq] at hy0; simpa using hy0
      obtain ⟨hfl, hsp⟩ := cuto_low_fields H hl hr' ha' (Or.inr (by omega))
      refine ⟨cutoMsg tr pub r, ?_, hfl⟩
      rcases (hv _).mp (seg_cuto_in_fin r hr' ha') with h | h | h
      · exact h
      · obtain ⟨j, -, he⟩ := mem_localView.mp h
        have := congrArg Msg.space he; rw [enc_space] at this; omega
      · exact absurd (by omega) (hG _ h).1
    · rintro ⟨x, hx, rfl⟩
      have hx0 : x.space = 0 := by obtain ⟨i, -, rfl⟩ := mem_stackView.mp hx; rfl
      rcases seg_finSplit H x ((hv x).mpr (Or.inl hx)) with ⟨r, hr', ha', rfl⟩ | h | h | ⟨r, hr', ha', hi', rfl⟩
      · obtain ⟨hfl, hsp⟩ := cuto_low_fields H hl hr' ha' (Or.inl (by omega))
        refine ⟨?_, ?_⟩
        · rw [hfl]
          simp only [cutoList, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
          exact ⟨r, ⟨hr', ha'⟩, rfl⟩
        · simp only [fieldsOf, List.head?_cons, hx0]
      · omega
      · omega
      · have := (drop_dead H hT hr' ha' hi').1; omega
  · obtain ⟨sN, e, hs, hr, hgas⟩ := ha h2
    have hgas' := hgas
    simp only [c, segCutSt] at hgas' hs hr
    rw [eT] at hgas'
    exact ⟨sN, e, hs, hr, hgas'⟩

#print axioms segCutSt
#print axioms cuto_low_fields
#print axioms seg_sound_halt

end WasmBase
