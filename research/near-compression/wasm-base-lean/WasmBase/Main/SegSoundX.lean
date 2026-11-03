import WasmBase.Main.SegRowsX
import WasmBase.Main.CtxNodup

/-!
# WasmBase.Main.SegSoundX — segment soundness from `HoldsX` (E2E M4b, S4)

WIP
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

/-- The `k`-th field expression of a table's STATE receive. -/
def stE (T : Table) (k : Nat) : Expr := (T.inters.getD 0 default).msg.getD k 0

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

theorem stE_eval (T : Table) (tr : Trace) (pub : List F) (t r k : Nat) :
    (stE T k).eval (tr.row pub t r) = (rowIn T tr pub t r).getD k 0 := by
  simp only [stE, rowIn, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : (T.inters[0]?.getD default).msg[k]? <;> simp [h] <;> rfl

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

end WasmBase
