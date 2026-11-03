import WasmBase.Main.SegRegKeep
import WasmBase.Main.CtxNodup

/-!
# WasmBase.Main.SegSoundX — segment soundness from `HoldsX` (E2E M4b, S4)

**`seg_sound`** — the cut case of a segment, from `HoldsX (wasmBaseSegAir …)` with **no given
`CutSeg`**: the segment's `CutSeg` is built from the trace (`segCut`), and S3's `seg_sound_cut_pub`
applied to it.  Conclusion: `t_out = t_in + n`, `seg n s0 = .cont sN` (`run` continues from `sN`),
`BndC` at the out-boundary (SEGB's last STATE message `segFinM`, live list `finS`), CUTO's hashed list
`= cutView X sN`, the public `ctx_out` limbs are the SHA-384 digest of `cutDigest (cutView X sN)`, and
the view is `MsgWF`.

## What is now a theorem (was a premise of `seg_sound_cut_pub`)

* the whole `CutSeg`: rows (`rowFactsSegMap_seg`: instruction rows from `seg_rowfacts`,
  `Main/SegRowsX.lean`; HOST rows `HoldRowS`), STATE (`seg_hst`), CH (`seg_hch`), producer times of the
  in-boundary (`seg_initS_tp`), the time/fee bounds (from `hlen`, `htin` and the public `hfeeN`, via
  `seg_len`: the segment's length is `t_out − t_in`);
* `FinSplit`, `hin` (`seg_finSplit`, `seg_cuto_in_fin`, `Main/SegBus.lean`);
* the per-row clauses at **instruction rows**: the space clause (`seg_instr_rowQ_sp`: every CH space
  of an instruction table is `0, 2, 3, 4, 5`, `16 + ts` or `16 + cid` — `instr_spform`, by `decide` —,
  with `ts < 2^30` from the row's chain position `seg_row_lvl` and `cid < 2^28` from `RelW`), the
  "no space-6 message" half of the register clause (`seg_instr_rowQ_reg`), and `RegWF`
  (`rowQ_regWF_keep`), the latter two with **`InstrRegKeep`** (an instruction row's step keeps the
  register file), which is `seg_instr_regKeep` (`Main/SegRegKeep.lean`: the row's FETCH op is
  `< 0x1FF`, so its record is not a host call's).  So the three `RowQ` premises of
  `seg_sound_cut_pub` remain only at HOST rows (`HostRely`).

## Named premises of `seg_sound`

* `ChipIf compressW …`, `CutoHiLimbs` — the SHA-512 chip contract and its limb bound (S1/S2);
* `CodeOK`, `FuncOK` — the CODE/FUNC commitment bindings (as every `wasm_base_sound*`);
* `HostBLinked`, `RegCLinked`, `SegKeepM2`, `hstepgas`, `hg64` — as `wasm_base_sound_m2`;
* `HoldRowS` — the HOST rows' segment-aware row facts with the gas register fused in (M2's
  `HoldRowM2` + gas; host-chip contract);
* `HostRely` — the HOST rows' register (`HostRegRely`), space and `RegWF` clauses (host-chip contract,
  M6);
* `hst0` (`halted_out = 0`: the cut case), `hlen` (`n < 2^28`), `htin` (`t_in < 2^28`), `hfeeN`
  (`S_in + (t_out − t_in + 1)·(maxFee + 1) < p`);
* **`(initS tr pub).Nodup`** — the in-boundary messages are distinct (inside `CutSeg` before).  MEMB's
  bytes (distinct addresses, `memb_addr_inj`) and SEGB's single gas message are distinct by
  construction; CUTI has no range/order checks, so its part is the previous segment's view only up
  to SHA-384 (it does not follow "symmetrically" from CUTO);
* `TombDead tr pub (finS tr pub)` — taken RETs' activations are dead at the cut (S3; an execution
  fact);
* `h0 : BndC …` (the in-boundary relation for `s0` at `t_in`, SEGB's first message, live list
  `initS`) and `RegWF s0`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- **The active HOST rows' segment-aware row facts, segment form** (named premise, the host-chip
contract): as `HoldRowM2`, with the row's CH traffic fused with its call's `HOSTB` bytes, REG-C net
traffic **and its gas-register messages** (`consCHS`/`prodCHS`). -/
def HoldRowS (X : Ctx) (tr : Trace) (pub : List F) (sg : Nat → Nat × Nat) : Prop :=
  ∀ r, r < tr.height 22 → rowAct Host.table tr pub 22 r →
    RowFactsSeg X (rowInM tr pub (22, r)) (rowOutM tr pub (22, r))
      (consCHS tr pub (22, r)) (prodCHS tr pub (22, r))
      (sg (rowNat tr 22 r 1)) (sg (rowNat tr 22 r 1 + 1))

/-- The instruction-row facts of a segment trace (tables 1–14, IF, CONV, UNREACH): the conclusion of
`m2_rowfacts` for the segment AIR. -/
def SegInstrRows (X : Ctx) (tr : Trace) (pub : List F) : Prop :=
  ∀ t r, IsInstrM2 t → r < tr.height t → rowAct (chipM2 t) tr pub t r →
    RowFacts2 X (rowIn (chipM2 t) tr pub t r) (rowOut (chipM2 t) tr pub t r)
      (rowCons (chipM2 t) tr pub t r) (rowProd (chipM2 t) tr pub t r)

theorem gasH_nil_of_ne {tr : Trace} {pub : List F} {ρ : Nat × Nat} (h : ρ.1 ≠ 22) :
    consCHS tr pub ρ = consCHM2 tr pub ρ ∧ prodCHS tr pub ρ = prodCHM2 tr pub ρ := by
  simp [consCHS, prodCHS, gasConsH, gasProdH, h]

/-- **Assembling `hrows` for the segment AIR.**  Instruction rows: `SegInstrRows` (+ `SegKeepM2`);
HOST rows: `HoldRowS` verbatim. -/
theorem rowFactsSegMap_seg (X : Ctx) {tr : Trace} {pub : List F} (hI : SegInstrRows X tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X tr pub sg) :
    ∀ ρ ∈ actListM2 tr pub,
      RowFactsSegMap X (rowInM tr pub ρ) (rowOutM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ) sg := by
  intro ρ hρ
  obtain ⟨t, r⟩ := ρ
  rcases mem_actListM2 hρ with ⟨h22, hr, ha⟩ | ⟨htI, hr, ha⟩
  · simp only at h22 hr ha
    subst h22
    exact hhold r hr ha
  · simp only at htI hr ha
    have hne : t ≠ 22 := by rcases htI with ⟨_, h⟩ | h | h | h <;> omega
    have hRF := hI t r htI hr ha
    have ec : chipTM2 t = chipM2 t := by simp [chipTM2, hne]
    obtain ⟨eC, eP⟩ := gasH_nil_of_ne (tr := tr) (pub := pub) (ρ := (t, r)) hne
    have hC : consCHS tr pub (t, r) = rowCons (chipM2 t) tr pub t r := by
      rw [eC]; simp [consCHM2, rowConsM, hostbConsH, regConsH, hne, ec]
    have hP : prodCHS tr pub (t, r) = rowProd (chipM2 t) tr pub t r := by
      rw [eP]; simp [prodCHM2, rowProdM, hostbProdH, regProdH, hne, ec]
    have hI' : rowInM tr pub (t, r) = rowIn (chipM2 t) tr pub t r := by simp [rowInM, ec]
    have hO : rowOutM tr pub (t, r) = rowOut (chipM2 t) tr pub t r := by simp [rowOutM, ec]
    unfold RowFactsSegMap
    have hs := hkeep (t, r) hρ hne
    rw [hC, hP, hI', hO]
    rw [hI'] at hs
    rw [hs]
    exact hRF.toSeg

/-- The level of the last STATE message of a chain from `m0`. -/
theorem chain_lvl {ρ : Type} [DecidableEq ρ] (act : List ρ) (inS outS : ρ → List F) (m0 mf : List F)
    (hts : ∀ r ∈ act, lvl (outS r) = lvl (inS r) + 1)
    (hst : (m0 :: act.map outS).Perm (mf :: act.map inS)) (hlen : act.length < P) :
    lvl mf = lvl m0 + ((act.length : Nat) : F) := by
  let g : ρ → List F × List F := fun r => (inS r, outS r)
  have hE1 : (act.map g).map Prod.snd = act.map outS := by simp [g, List.map_map]
  have hE2 : (act.map g).map Prod.fst = act.map inS := by simp [g, List.map_map]
  have hstepE : ∀ e ∈ act.map g, lvl e.2 = lvl e.1 + 1 := by
    intro e he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    exact hts r hr
  obtain ⟨es, hes, hpath⟩ := chain (act.map g) m0 mf lvl (by rw [hE1, hE2]; exact hst) hstepE (by simpa using hlen)
  obtain ⟨-, lfin⟩ := path_levels lvl es _ _ hpath (fun e he => hstepE e (hes.subset he))
  have hl : es.length = act.length := by rw [hes.length_eq]; simp
  rw [lfin, hl]

/-! ## The segment of a `HoldsX` trace as a `CutSeg` -/

/-- The final STATE message of a cut segment (`halted = 0`). -/
def segFinM (tr : Trace) (pub : List F) : List F :=
  [pub.getD pubPcOut 0, pub.getD pubTOut 0 + 1, pub.getD pubSOut 0, ((0 : Nat) : F), pub.getD pubSbOut 0,
    tr.cell 0 0 (ix Segb.cols "cidf")]

/-- **The trace → `CutSeg` instantiation** for `wasmBaseSegAir`, cut case: the rows of `actListM2`,
STATE from `seg_hst`, CH from `seg_hch` with the boundary blocks `initS`/`finS`. -/
def segCut (X : Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    {sg : Nat → Nat × Nat}
    (hrows : ∀ ρ ∈ actListM2 tr pub,
      RowFactsSegMap X (rowInM tr pub ρ) (rowOutM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ) sg)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub) (hst0 : pub.getD Boundary.pubStatus 0 = 0)
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
  st := 0
  t0 := (pub.getD pubTIn 0).toNat
  S0 := (pub.getD pubSIn 0).toNat
  m0 := segM0 tr pub
  hst2 := by decide
  hrows := hrows
  hst := by
    have h := seg_hst H
    rw [segMF_eq, hst0] at h
    exact h
  hch := seg_hch H X hb hg
  hinit := hinit
  hinitTp := fun x hx => Nat.le_of_eq (seg_initS_tp tr pub x hx)
  ht := ht
  hfee := hfee

/-- The segment's length is `t_out − t_in` (the STATE chain from `t_in + 1` to `t_out + 1`). -/
theorem seg_len {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1)
    (hsz : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length < P) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length := by
  have h := chain_lvl _ _ _ _ _ hts (seg_hst H) (by omega)
  have e0 : lvl (segM0 tr pub) = pub.getD pubTIn 0 + 1 := by rw [segM0_eq]; rfl
  have e1 : lvl (segMF tr pub) = pub.getD pubTOut 0 + 1 := by rw [segMF_eq]; rfl
  rw [e0, e1] at h
  have h2 : pub.getD pubTOut 0 = (((pub.getD pubTIn 0).toNat + (actListM2 tr pub).length : Nat) : F) := by
    rw [Lean.Grind.Semiring.natCast_add, Fp.cast_toNat]
    grind
  rw [h2, Fp.toNat_cast_of_lt hsz]

/-- **Segment soundness (cut case) from `HoldsX`, instruction rows as a premise.**  The segment's
`CutSeg` is built from the trace (`segCut`); `FinSplit`/`hin` are theorems (`seg_finSplit`,
`seg_cuto_in_fin`); the segment's length is `t_out − t_in` (`seg_len`). -/
theorem seg_sound_rows (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hI : SegInstrRows X.toCtx tr pub)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X.toCtx tr pub sg)
    (hst0 : pub.getD Boundary.pubStatus 0 = 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    (hreg : ∀ ρ ∈ actListM2 tr pub,
      RowQ X.toCtx (fun s live => RegC live s) (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ))
    (hsp : ∀ ρ ∈ actListM2 tr pub,
      RowQ X.toCtx (fun _ live => SpC live) (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ))
    (hwf : ∀ ρ ∈ actListM2 tr pub,
      RowQ X.toCtx (fun s _ => RegWF s) (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ))
    (hT : TombDead tr pub (finS tr pub))
    {s0 : St} (h0 : BndC X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hw0 : RegWF s0) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    ∃ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN ∧
      (∀ m, run X.toCtx.cfg X.toCtx.p ((actListM2 tr pub).length + m) s0 = run X.toCtx.cfg X.toCtx.p m sN) ∧
      BndC X.toCtx sg sN (pub.getD pubTOut 0).toNat (pub.getD pubSOut 0).toNat (segFinM tr pub) (finS tr pub) ∧
      cutoList tr = cutView X.toCtx sN ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxOut = SegSha.limbsF d ∧
        SegSha.wbytes d = cutDigest (cutView X.toCtx sN)) ∧
      ∀ y ∈ cutView X.toCtx sN, MsgWF y := by
  have hP := P_val
  have hrows := rowFactsSegMap_seg X.toCtx hI hkeep hhold
  have hlenEq := seg_len H (fun ρ hρ => (hrows ρ hρ).tsOut) (by omega)
  have ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P := by omega
  have hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.toCtx.maxFee + 1) < P := by
    have e : (pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat = (actListM2 tr pub).length := by omega
    rw [e] at hfeeN; exact hfeeN
  obtain ⟨sN, h1, h2, h3, h4, h5, h6⟩ := seg_sound_cut_pub X.toCtx (M2Ctx.toCtx_fns_nodup X) H hC hl
    (segCut X.toCtx H hrows hb hg hst0 hinit ht hfee) rfl hstepgas hg64 hreg hsp hwf h0 hw0
    seg_cuto_in_fin (seg_finSplit H) hT
  refine ⟨hlenEq, sN, h1, h2, ?_, h4, h5, h6⟩
  rw [hlenEq]
  exact h3

#print axioms seg_sound_rows

/-! ## Channel spaces of the instruction rows

Every CH interaction of an instruction table (1–14, IF, CONV, UNREACH) has as space expression a
constant in `{0, 2, 3, 4, 5}`, `16 + ts` (CALL: the callee's locals, `ts` = the row's STATE time),
`16 + cid` (`cid` = the row's STATE activation id), or LOCAL's `(1 − isG)·(16 + cid) + 2·isG`.  So a
row's consumed/produced messages are in space `0, 2, 3, 4, 5` or `16 + x` with `x` its STATE time or
activation id (`instr_space`). -/

/-- The allowed space expressions of a table's CH interactions (`loc`: also LOCAL's form). -/
def spAllowed (T : Table) (loc : Bool) (e : Option Expr) : Bool :=
  decide (e = some (.c 0)) || decide (e = some (.c 2)) || decide (e = some (.c 3)) ||
  decide (e = some (.c 4)) || decide (e = some (.c 5)) || decide (e = some (.add (.c 16) (stE T 1))) ||
  decide (e = some (.add (.c 16) (stE T 5))) || (loc && decide (e = some Local.space))

def SpForm (T : Table) (loc : Bool) : Bool :=
  T.inters.all fun i => decide (i.bus ≠ busStk) || spAllowed T loc i.msg.head?

theorem instr_spform : ∀ t, IsInstrM2 t → SpForm (chipM2 t) (decide (t = 9)) = true := by
  intro t ht
  rcases ht with ⟨h1, h14⟩ | rfl | rfl | rfl
  · rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨
      t = 12 ∨ t = 13 ∨ t = 14 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  all_goals decide +kernel

/-- The space of a consumed/produced message of an instruction row: `0, 2, 3, 4, 5`, or `16 + ts`,
`16 + cid` (field arithmetic) for the row's STATE time / activation id. -/
def SpaceIn (inS : List F) (x : Msg) : Prop :=
  x.space = 0 ∨ x.space = 2 ∨ x.space = 3 ∨ x.space = 4 ∨ x.space = 5 ∨
    x.space = ((16 : F) + inS.getD 1 0).toNat ∨ x.space = ((16 : F) + inS.getD 5 0).toNat

theorem spaceIn_of {T : Table} {loc : Bool} (hS : SpForm T loc = true) {tr : Trace} {pub : List F} {t r : Nat}
    (hloc : loc = true → (Local.isG.eval (tr.row pub t r) = 0 ∨ Local.isG.eval (tr.row pub t r) = 1) ∧
      (v Local.kCid).eval (tr.row pub t r) = (rowIn T tr pub t r).getD 5 0)
    {s : Bool} {m : List F} (hm : m ∈ rowMsgs T tr pub t r busStk s) :
    SpaceIn (rowIn T tr pub t r) (decMsg m) := by
  obtain ⟨i, hi, rfl⟩ := mem_rowMsgs hm
  have hb := (List.mem_filter.mp hi).2
  simp only [decide_eq_true_eq] at hb
  have hc := List.all_eq_true.mp hS i (List.mem_filter.mp hi).1
  simp only [Bool.or_eq_true, decide_eq_true_eq, hb.1, ne_eq, not_true_eq_false, false_or] at hc
  have hP := P_val
  have sp : (decMsg (i.msg.map (·.eval (tr.row pub t r)))).space =
      (match i.msg.head? with | some e => e.eval (tr.row pub t r) | none => 0).toNat := by
    cases hmsg : i.msg <;> simp [decMsg, hmsg]
  simp only [SpaceIn]; rw [sp]
  simp only [spAllowed, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ((((((h | h) | h) | h) | h) | h) | h) | ⟨hl, h⟩ <;> rw [h]
  · left; rfl
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; left; rfl
  · right; right; right; right; left; rfl
  · right; right; right; right; right; left; simp only [Expr.eval, stE_eval]; rfl
  · right; right; right; right; right; right; simp only [Expr.eval, stE_eval]; rfl
  · obtain ⟨hg, hk⟩ := hloc hl
    have e : Local.space = (1 - Local.isG) * (16 + v Local.kCid) + 2 * Local.isG := rfl
    rw [e]
    simp only [Expr.eval_add', Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', hk]
    rcases hg with hg | hg <;> rw [hg]
    · right; right; right; right; right; right
      congr 1; rw [show ((1 : Nat) : F) = 1 from rfl, show ((2 : Nat) : F) * 0 = 0 by grind]; grind
    · right; left
      have : (((1 : Nat) : F) - 1) * (((16 : Nat) : F) + (rowIn T tr pub t r).getD 5 0) + ((2 : Nat) : F) * 1 =
          ((2 : Nat) : F) := by rw [show ((1 : Nat) : F) = 1 from rfl]; grind
      rw [this]; rfl

/-- On an active instruction row of a segment trace, every consumed/produced message is `SpaceIn`. -/
theorem seg_instr_spaceIn {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    {t r : Nat} (htI : IsInstrM2 t) (hr : r < tr.height t) {s : Bool} {m : List F}
    (hm : m ∈ rowMsgs (chipM2 t) tr pub t r busStk s) :
    SpaceIn (rowIn (chipM2 t) tr pub t r) (decMsg m) := by
  refine spaceIn_of (instr_spform t htI) (fun hl => ?_) hm
  have h9 : t = 9 := by simpa using hl
  subst h9
  have hT : (wasmBaseSegAir nloc ngl).tables[9]'(by simp [seg_air_len]) = Local.table := seg_chipT nloc ngl 9 (by omega) (by omega)
  have hcon := table_constr_eqX H (by simp [seg_air_len]) Local.table hT hr
  obtain ⟨hsum, -⟩ := local_count_vals_of hcon
  have e9 : chipM2 9 = Local.table := rfl
  rw [e9]
  refine ⟨?_, ?_⟩
  · have hP := P_val
    have ev : Local.isG.eval (tr.row pub 9 r) = ((rowNat tr 9 r 26 + rowNat tr 9 r 27 : Nat) : F) := by
      simp only [Local.isG, Local.fGGet, Local.fGSet, v, Expr.eval, Trace.row, rowNat, Fp.cast_toNat,
        Lean.Grind.Semiring.natCast_add]
    rw [ev]
    rcases (by omega : rowNat tr 9 r 26 + rowNat tr 9 r 27 = 0 ∨ rowNat tr 9 r 26 + rowNat tr 9 r 27 = 1) with h | h <;>
      rw [h]
    · left; rfl
    · right; rfl
  · rw [← stE_eval]; rfl

/-- The chain position of every action row: its STATE time is in `t_in + 1 … t_in + n`. -/
theorem seg_row_lvl {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1)
    (hsz : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 < P) :
    ∀ ρ ∈ actListM2 tr pub, (lvl (rowInM tr pub ρ)).toNat ≤ (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length := by
  intro ρ hρ
  let act := actListM2 tr pub
  let g : Nat × Nat → List F × List F := fun r => (rowInM tr pub r, rowOutM tr pub r)
  have hE1 : (act.map g).map Prod.snd = act.map (rowOutM tr pub) := by simp [g, List.map_map]
  have hE2 : (act.map g).map Prod.fst = act.map (rowInM tr pub) := by simp [g, List.map_map]
  have hstepE : ∀ e ∈ act.map g, lvl e.2 = lvl e.1 + 1 := by
    intro e he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    exact hts r hr
  obtain ⟨es, hes, hpath⟩ := chain (act.map g) (segM0 tr pub) (segMF tr pub) lvl
    (by rw [hE1, hE2]; exact seg_hst H) hstepE (by simp [act]; omega)
  obtain ⟨lk, -⟩ := path_levels lvl es _ _ hpath (fun e he => hstepE e (hes.subset he))
  have hl : es.length = act.length := by rw [hes.length_eq]; simp
  have hal : act.length = (actListM2 tr pub).length := rfl
  have hmem : g ρ ∈ es := hes.symm.subset (List.mem_map_of_mem hρ)
  obtain ⟨k, hk, hek⟩ := List.getElem_of_mem hmem
  have e := lk k hk
  rw [hek] at e
  have e0 : lvl (segM0 tr pub) = pub.getD pubTIn 0 + 1 := by rw [segM0_eq]; rfl
  rw [e0] at e
  have e' : lvl (rowInM tr pub ρ) = (((pub.getD pubTIn 0).toNat + 1 + k : Nat) : F) := by
    rw [show (g ρ).1 = rowInM tr pub ρ from rfl] at e
    rw [e, Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_add, Fp.cast_toNat]; rfl
  rw [e', Fp.toNat_cast_of_lt (by omega)]
  omega

theorem consProd_instr {tr : Trace} {pub : List F} {t r : Nat} (hne : t ≠ 22) :
    consCHS tr pub (t, r) = rowCons (chipM2 t) tr pub t r ∧ prodCHS tr pub (t, r) = rowProd (chipM2 t) tr pub t r ∧
      rowInM tr pub (t, r) = rowIn (chipM2 t) tr pub t r := by
  have ec : chipTM2 t = chipM2 t := by simp [chipTM2, hne]
  obtain ⟨eC, eP⟩ := gasH_nil_of_ne (tr := tr) (pub := pub) (ρ := (t, r)) hne
  refine ⟨?_, ?_, by simp [rowInM, ec]⟩
  · rw [eC]; simp [consCHM2, rowConsM, hostbConsH, regConsH, hne, ec]
  · rw [eP]; simp [prodCHM2, rowProdM, hostbProdH, regProdH, hne, ec]

/-- A `SpaceIn` message of a row whose STATE time is below `2^30`, at a related state, is in an allowed
space and not in the register space 6. -/
theorem spaceIn_ok {inS : List F} {x : Msg} (hx : SpaceIn inS x) (hlv : (lvl inS).toNat < 2 ^ 30)
    {pcN t S sb cid : Nat} (hin : inS = stMsg pcN t S 0 sb cid) (hcid : cid < 2 ^ 28) :
    SpaceOK x ∧ x.space ≠ 6 := by
  have hP := P_val
  have h5 : inS.getD 5 0 = ((cid : Nat) : F) := by rw [hin]; rfl
  have h1 : inS.getD 1 0 = lvl inS := rfl
  have c16 : ∀ n, n + 16 < P → ((16 : F) + ((n : Nat) : F)).toNat = 16 + n := by
    intro n hn
    rw [show (16 : F) = ((16 : Nat) : F) from rfl, ← Lean.Grind.Semiring.natCast_add, Fp.toNat_cast_of_lt (by omega)]
  have l16 : ((16 : F) + lvl inS).toNat = 16 + (lvl inS).toNat := by
    conv => lhs; rw [← Fp.cast_toNat (lvl inS)]
    exact c16 _ (by omega)
  unfold SpaceIn at hx
  rw [h5, h1, l16, c16 cid (by omega)] at hx
  unfold SpaceOK
  omega

/-- **The space clause at an instruction row** (`RowQ` for `SpC`), from the trace: an instruction
row produces messages in allowed spaces only. -/
theorem seg_instr_rowQ_sp {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {ρ : Nat × Nat} (hρ : ρ ∈ actListM2 tr pub) (hne : ρ.1 ≠ 22)
    (hlv : (lvl (rowInM tr pub ρ)).toNat < 2 ^ 30) :
    RowQ X (fun _ live => SpC live) (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ) := by
  obtain ⟨t, r⟩ := ρ
  simp only at hne
  rcases mem_actListM2 hρ with ⟨h22, -, -⟩ | ⟨htI, hr, -⟩
  · exact absurd h22 hne
  obtain ⟨-, eP, eI⟩ := consProd_instr (tr := tr) (pub := pub) (r := r) hne
  refine rowQ_space fun E s f tps tpl tt pc S live a b R hin x hx => ?_
  rw [eP] at hx
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  rw [eI] at hin hlv
  exact (spaceIn_ok (seg_instr_spaceIn H htI hr hm) hlv hin R.cidLt).1

/-- **The register and well-formedness clauses at an instruction row** (`RowQ` for `RegC`, `RegWF`),
from the trace and `RegKeep` (the row's step keeps the register file): an instruction row neither
consumes nor produces a space-6 message. -/
theorem seg_instr_rowQ_reg {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {ρ : Nat × Nat} (hρ : ρ ∈ actListM2 tr pub) (hne : ρ.1 ≠ 22)
    (hlv : (lvl (rowInM tr pub ρ)).toNat < 2 ^ 30) (hk : RegKeep X (rowInM tr pub ρ)) :
    RowQ X (fun s live => RegC live s) (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ) := by
  obtain ⟨t, r⟩ := ρ
  simp only at hne
  rcases mem_actListM2 hρ with ⟨h22, -, -⟩ | ⟨htI, hr, -⟩
  · exact absurd h22 hne
  obtain ⟨eC, eP, eI⟩ := consProd_instr (tr := tr) (pub := pub) (r := r) hne
  intro E s f tps tpl tt pc S live a b s' R hin hl hs hQ
  have six : ∀ (sd : Bool) (m : List F), m ∈ rowMsgs (chipM2 t) tr pub t r busStk sd → (decMsg m).space ≠ 6 := by
    intro sd m hm
    have hin' := hin; rw [eI] at hin'
    have hlv' := hlv; rw [eI] at hlv'
    exact (spaceIn_ok (seg_instr_spaceIn H htI hr hm) hlv' hin' R.cidLt).2
  refine rowQ_reg_keep (fun x hx => ?_) (fun x hx => ?_) hk E s f tps tpl tt pc S live a b s' R hin hl hs hQ
  · rw [eC] at hx; obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx; exact six false m hm
  · rw [eP] at hx; obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx; exact six true m hm

/-! ## The segment soundness theorem -/

/-- The register-keep premise of the instruction rows: an instruction row's step keeps the register
file (its instruction is not a call of an import nor `call_indirect`, `StepRegs.NonHostI`;
`regKeep_of_code`). -/
def InstrRegKeep (X : Ctx) (tr : Trace) (pub : List F) : Prop :=
  ∀ ρ ∈ actListM2 tr pub, ρ.1 ≠ 22 → RegKeep X (rowInM tr pub ρ)

/-- The HOST rows' clause relies (host-chip contract, M6): the register clause (`HostRegRely`), the
space clause and the register-file well-formedness. -/
structure HostRely (X : Ctx) (tr : Trace) (pub : List F) : Prop where
  reg : ∀ ρ ∈ actListM2 tr pub, ρ.1 = 22 → HostRegRely X (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ)
  sp : ∀ ρ ∈ actListM2 tr pub, ρ.1 = 22 →
    RowQ X (fun _ live => SpC live) (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ)
  wf : ∀ ρ ∈ actListM2 tr pub, ρ.1 = 22 →
    RowQ X (fun s _ => RegWF s) (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ)

/-- **`seg_sound`: segment soundness (cut case) from `HoldsX`.**

For a satisfied segment trace (`HoldsX (wasmBaseSegAir …)`, bus 103 left to the SHA chip), the
SHA-512 chip contract `ChipIf compressW …` with its limb bound `CutoHiLimbs`, an M2-checked module
`X` with the CODE/FUNC commitment bindings, and a spec state `s0` related by `BndC` to the
in-boundary (`t_in`, `S_in`, SEGB's first STATE message, the live list `initS` = CUTI ∪ MEMB ∪ gas
register) with a well-formed register file, on a cut (`halted_out = 0`):

* `t_out = t_in + n` (`n` = number of action rows);
* `seg n s0 = .cont sN`, and `run` continues from `sN`;
* `BndC` at the out-boundary (`t_out`, `S_out`, SEGB's last STATE message, the live list `finS` =
  CUTO ∪ MEMB ∪ gas register ∪ DROP consumptions);
* CUTO's hashed list is `cutView X sN`, the public `ctx_out` limbs are those of the SHA-384 digest `d`
  with `wbytes d = cutDigest (cutView X sN)`, and every view entry is `MsgWF`.

The trace → `CutSeg` instantiation (`segCut`: rows `seg_rowfacts` + `HoldRowS`, STATE `seg_hst`,
CH `seg_hch`), `FinSplit`/`hin` (`seg_finSplit`, `seg_cuto_in_fin`), the instruction rows' space
clause (`seg_instr_rowQ_sp`) and their register / `RegWF` clauses (`InstrRegKeep` = `seg_instr_regKeep`,
`seg_instr_rowQ_reg`, `rowQ_regWF_keep`) are theorems.  Named premises: see the module header. -/
theorem seg_sound (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
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
    (hT : TombDead tr pub (finS tr pub))
    {s0 : St} (h0 : BndC X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hw0 : RegWF s0) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    ∃ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN ∧
      (∀ m, run X.toCtx.cfg X.toCtx.p ((actListM2 tr pub).length + m) s0 = run X.toCtx.cfg X.toCtx.p m sN) ∧
      BndC X.toCtx sg sN (pub.getD pubTOut 0).toNat (pub.getD pubSOut 0).toNat (segFinM tr pub) (finS tr pub) ∧
      cutoList tr = cutView X.toCtx sN ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxOut = SegSha.limbsF d ∧
        SegSha.wbytes d = cutDigest (cutView X.toCtx sN)) ∧
      ∀ y ∈ cutView X.toCtx sN, MsgWF y := by
  have hP := P_val
  have hrk : InstrRegKeep X.toCtx tr pub := seg_instr_regKeep X H hcode
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfacts X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMap_seg X.toCtx hI hkeep hhold
  have hlv : ∀ ρ ∈ actListM2 tr pub, (lvl (rowInM tr pub ρ)).toNat < 2 ^ 30 := by
    intro ρ hρ
    have := seg_row_lvl H (fun ρ hρ => (hrows ρ hρ).tsOut) (by omega) ρ hρ
    omega
  refine seg_sound_rows X H hC hl hI hb hg hkeep hhold hst0 hlen htin hfeeN hstepgas hg64 hinit
    (fun ρ hρ => ?_) (fun ρ hρ => ?_) (fun ρ hρ => ?_) hT h0 hw0
  · by_cases h22 : ρ.1 = 22
    · exact hrely.reg ρ hρ h22
    · exact seg_instr_rowQ_reg H hρ h22 (hlv ρ hρ) (hrk ρ hρ h22)
  · by_cases h22 : ρ.1 = 22
    · exact hrely.sp ρ hρ h22
    · exact seg_instr_rowQ_sp H hρ h22 (hlv ρ hρ)
  · by_cases h22 : ρ.1 = 22
    · exact hrely.wf ρ hρ h22
    · exact rowQ_regWF_keep (hrk ρ hρ h22)

#print axioms rowFactsSegMap_seg
#print axioms seg_len
#print axioms seg_row_lvl
#print axioms seg_instr_rowQ_sp
#print axioms seg_instr_rowQ_reg
#print axioms seg_sound

end WasmBase
