import WasmBase.Main.SegSoundX
import WasmBase.Main.SegS.SegRegKeep
/-!
# WasmBase.Main.SegS.SegSoundX — `SegSoundX`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegSoundX.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- **The trace → `CutSeg` instantiation** for `wasmBaseSegAir`, cut case: the rows of `actListM2`,
STATE from `seg_hstS`, CH from `seg_hchS` with the boundary blocks `initS`/`finS`. -/
def segCutS (X : Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
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
    have h := seg_hstS H
    rw [segMF_eq, hst0] at h
    exact h
  hch := seg_hchS H X hb hg
  hinit := hinit
  hinitTp := fun x hx => Nat.le_of_eq (seg_initS_tp tr pub x hx)
  ht := ht
  hfee := hfee

/-- The segment's length is `t_out − t_in` (the STATE chain from `t_in + 1` to `t_out + 1`). -/
theorem seg_lenS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    (hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1)
    (hsz : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length < P) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length := by
  have h := chain_lvl _ _ _ _ _ hts (seg_hstS H) (by omega)
  have e0 : lvl (segM0 tr pub) = pub.getD pubTIn 0 + 1 := by rw [segM0_eq]; rfl
  have e1 : lvl (segMF tr pub) = pub.getD pubTOut 0 + 1 := by rw [segMF_eq]; rfl
  rw [e0, e1] at h
  have h2 : pub.getD pubTOut 0 = (((pub.getD pubTIn 0).toNat + (actListM2 tr pub).length : Nat) : F) := by
    rw [Lean.Grind.Semiring.natCast_add, Fp.cast_toNat]
    grind
  rw [h2, Fp.toNat_cast_of_lt hsz]

/-- **Segment soundness (cut case) from `HoldsX`, instruction rows as a premise.**  The segment's
`CutSeg` is built from the trace (`segCutS`); `FinSplit`/`hin` are theorems (`seg_finSplitS`,
`seg_cuto_in_fin`); the segment's length is `t_out − t_in` (`seg_lenS`). -/
theorem seg_sound_rowsS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIfS SegSha.compressW nloc ngl pub tr chip) (hl : CutoHiLimbs tr)
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
  have hlenEq := seg_lenS H (fun ρ hρ => (hrows ρ hρ).tsOut) (by omega)
  have ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P := by omega
  have hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.toCtx.maxFee + 1) < P := by
    have e : (pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat = (actListM2 tr pub).length := by omega
    rw [e] at hfeeN; exact hfeeN
  obtain ⟨sN, h1, h2, h3, h4, h5, h6⟩ := seg_sound_cut_pubS X.toCtx (M2Ctx.toCtx_fns_nodup X) H hC hl
    (segCutS X.toCtx H hrows hb hg hst0 hinit ht hfee) rfl hstepgas hg64 hreg hsp hwf h0 hw0
    seg_cuto_in_fin (seg_finSplitS H) hT
  refine ⟨hlenEq, sN, h1, h2, ?_, h4, h5, h6⟩
  rw [hlenEq]
  exact h3

/-- On an active instruction row of a segment trace, every consumed/produced message is `SpaceIn`. -/
theorem seg_instr_spaceInS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    {t r : Nat} (htI : IsInstrM2 t) (hr : r < tr.height t) {s : Bool} {m : List F}
    (hm : m ∈ rowMsgs (chipM2 t) tr pub t r busStk s) :
    SpaceIn (rowIn (chipM2 t) tr pub t r) (decMsg m) := by
  refine spaceIn_of (instr_spform t htI) (fun hl => ?_) hm
  have h9 : t = 9 := by simpa using hl
  subst h9
  have hT : (wasmBaseSegAir nloc ngl).tables[9]'(by simp [seg_air_len]) = Local.table := seg_chipT nloc ngl 9 (by omega) (by omega)
  have hcon := table_constr_eqXS H (by simp [seg_air_len]) Local.table hT hr
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
theorem seg_row_lvlS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
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
    (by rw [hE1, hE2]; exact seg_hstS H) hstepE (by simp [act]; omega)
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

/-- **The space clause at an instruction row** (`RowQ` for `SpC`), from the trace: an instruction
row produces messages in allowed spaces only. -/
theorem seg_instr_rowQ_spS {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) {ρ : Nat × Nat} (hρ : ρ ∈ actListM2 tr pub) (hne : ρ.1 ≠ 22)
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
  exact (spaceIn_ok (seg_instr_spaceInS H htI hr hm) hlv hin R.cidLt).1

/-- **The register and well-formedness clauses at an instruction row** (`RowQ` for `RegC`, `RegWF`),
from the trace and `RegKeep` (the row's step keeps the register file): an instruction row neither
consumes nor produces a space-6 message. -/
theorem seg_instr_rowQ_regS {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) {ρ : Nat × Nat} (hρ : ρ ∈ actListM2 tr pub) (hne : ρ.1 ≠ 22)
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
    exact (spaceIn_ok (seg_instr_spaceInS H htI hr hm) hlv' hin' R.cidLt).2
  refine rowQ_reg_keep (fun x hx => ?_) (fun x hx => ?_) hk E s f tps tpl tt pc S live a b s' R hin hl hs hQ
  · rw [eC] at hx; obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx; exact six false m hm
  · rw [eP] at hx; obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx; exact six true m hm

/-- **`seg_soundS`: segment soundness (cut case) from `HoldsX`.**

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

The trace → `CutSeg` instantiation (`segCutS`: rows `seg_rowfactsS` + `HoldRowS`, STATE `seg_hstS`,
CH `seg_hchS`), `FinSplit`/`hin` (`seg_finSplitS`, `seg_cuto_in_fin`), the instruction rows' space
clause (`seg_instr_rowQ_spS`) and their register / `RegWF` clauses (`InstrRegKeep` = `seg_instr_regKeepS`,
`seg_instr_rowQ_regS`, `rowQ_regWF_keep`) are theorems.  Named premises: see the module header. -/
theorem seg_soundS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIfS SegSha.compressW nloc ngl pub tr chip) (hl : CutoHiLimbs tr)
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
  have hrk : InstrRegKeep X.toCtx tr pub := seg_instr_regKeepS X H hcode
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfactsS X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMap_seg X.toCtx hI hkeep hhold
  have hlv : ∀ ρ ∈ actListM2 tr pub, (lvl (rowInM tr pub ρ)).toNat < 2 ^ 30 := by
    intro ρ hρ
    have := seg_row_lvlS H (fun ρ hρ => (hrows ρ hρ).tsOut) (by omega) ρ hρ
    omega
  refine seg_sound_rowsS X H hC hl hI hb hg hkeep hhold hst0 hlen htin hfeeN hstepgas hg64 hinit
    (fun ρ hρ => ?_) (fun ρ hρ => ?_) (fun ρ hρ => ?_) hT h0 hw0
  · by_cases h22 : ρ.1 = 22
    · exact hrely.reg ρ hρ h22
    · exact seg_instr_rowQ_regS H hρ h22 (hlv ρ hρ) (hrk ρ hρ h22)
  · by_cases h22 : ρ.1 = 22
    · exact hrely.sp ρ hρ h22
    · exact seg_instr_rowQ_spS H hρ h22 (hlv ρ hρ)
  · by_cases h22 : ρ.1 = 22
    · exact hrely.wf ρ hρ h22
    · exact rowQ_regWF_keep (hrk ρ hρ h22)

end WasmBase
