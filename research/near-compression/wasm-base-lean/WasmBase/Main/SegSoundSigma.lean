import WasmBase.Main.SegSigma
import WasmBase.Main.SegSoundX

/-!
# WasmBase.Main.SegSoundSigma — segment soundness with the host side pinned (E2E M6, σ-thread)

`seg_sound` (`Main/SegSoundX.lean`, kept unchanged) is **vacuous on every trace with a continuing
host call**: its HOST-row premises `HoldRowS`, `HostRely.reg`, `HostRely.wf` quantify over every
related pre-state, i.e. every host side `σ` (`Main/HostVacuity.lean`: `not_holdRowS_of_sigma`,
`Vacuity.vacuity_witness`).  **`seg_sound_σ`** is its restatement with a ghost σ-thread
`σ : Nat → St` (indexed by STATE time, like the gas segments `sg`):

* `HoldRowSσ` — a HOST row's `RowFactsSegJ` for `J = SigJ σ`: only from related pre-states whose host
  side (`sideR`: `StepSide.sideG`, gas register blanked, plus the register file) is `σ t`, and the continuing post-state has host side
  `σ (t + 1)`;
* `HostRelyσ` — the HOST rows' register and `RegWF` clauses as `RowQJ` (restricted the same way);
  the space clause needs no premise (`hostRely_sp`);
* `SigKeep` — `σ (t + 1) = σ t` at every instruction row's time (as `SegKeepM2` for `sg`);
* the in-boundary pins `sideR s0 = σ (t_in + 1)`; the conclusion adds `sideR sN = σ (t_out + 1)` and
  `RegWF sN`.

Instruction rows keep `sideR` (`StepSide.step_sideG`, `StepRegs.step_registers`), their instruction being non-host
(`seg_instr_codeNonHost`, the FETCH-op argument of `seg_instr_regKeep`), so with `SigKeep` they keep
the thread (`rowJKeep_sig`).

## Why an honest run satisfies the new premises

Let `s_k` be the honest state before the `k`-th row (STATE time `t_in + 1 + k`) and put
`σ (t_in + 1 + k) := sideR s_k` (constant after the last row).
* `hσ0` is `rfl`; `SigKeep`: an instruction row's step is non-host, so `sideR s_{k+1} = sideR s_k`
  (`sideR_keep_of_code`).
* `HoldRowSσ` at a HOST row of time `t`: the premise only ranges over related pre-states `s` with
  `sideR s = sideR s_k` (host side, gas accounting except `g`, context, storage, logs, promises, the
  register file all equal the honest ones) and `gas.g` fixed by `RelW.gas`.  Such an `s` can differ
  from `s_k` only in Wasm-visible parts: the operand stack below the popped arguments and the
  caller frames (the arguments themselves are pinned by the row's consumed STATE/CH messages via
  `RelW.live`), memory bytes the call does not read (those it reads are pinned by the HOSTB
  consumptions via `HeapOK`), globals, and the static `table`/`elems`/`datas`.  A host function
  reads none of these (M6.1 footprint: it acts on `σ`, its popped arguments, the bytes it reads and
  the registers), so `callHost` from `s` gives the honest response, pushed values, bytes written and
  host side `sideR s_{k+1} = σ (t + 1)`, and the post-state is related exactly as the honest one
  (`host_rel_restart`).  The two states that refuted the unrestricted premise
  (`not_rowSpecSeg_of_sigma`) differ in `σ`; on one thread they coincide (`sigJ_unique`).
  **Formally open**: the relational footprint lemma for `callHost` (per arm, the two-run analogue of
  `HostArms.callHost_inv`), which turns this argument into `HostIf → HoldRowSσ` (m6 README §3, M6.2).
* `HostRelyσ`: the same argument for the register clause; `RegWF` as `hostRely_of`
  (`HostRegWF.lean`: distinct ids a theorem, the size cap `HostRegCap`).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
open HostFoot StepSide
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. The trace premises -/

/-- **The active HOST rows' segment-aware row facts, σ-pinned** (named premise, the host-chip
contract): `HoldRowS` with the spec restricted to pre-states whose host side is `σ` at the row's
time (`RowFactsSegJ … (SigJ σ)`). -/
def HoldRowSσ (X : Ctx) (tr : Trace) (pub : List F) (sg : Nat → Nat × Nat) (σ : Nat → St) : Prop :=
  ∀ r, r < tr.height 22 → rowAct Host.table tr pub 22 r →
    RowFactsSegJ X (SigJ σ) (rowInM tr pub (22, r)) (rowOutM tr pub (22, r))
      (consCHS tr pub (22, r)) (prodCHS tr pub (22, r))
      (sg (rowNat tr 22 r 1)) (sg (rowNat tr 22 r 1 + 1))

/-- **The HOST rows' clause relies, σ-pinned** (named, M6): the register clause and `RegWF`, from
related pre-states with host side `σ t` only.  (The space clause is `hostRely_sp`.) -/
structure HostRelyσ (X : Ctx) (tr : Trace) (pub : List F) (σ : Nat → St) : Prop where
  reg : ∀ ρ ∈ actListM2 tr pub, ρ.1 = 22 →
    RowQJ X (SigJ σ) (fun s live => RegC live s) (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ)
  wf : ∀ ρ ∈ actListM2 tr pub, ρ.1 = 22 →
    RowQJ X (SigJ σ) (fun s _ => RegWF s) (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ)

/-- The old (unrestricted) relies give the σ-pinned ones (for any `σ`). -/
theorem HostRely.toσ {X : Ctx} {tr : Trace} {pub : List F} (h : HostRely X tr pub) (σ : Nat → St) :
    HostRelyσ X tr pub σ :=
  ⟨fun ρ hρ h22 => RowQ.toJ (h.reg ρ hρ h22), fun ρ hρ h22 => RowQ.toJ (h.wf ρ hρ h22)⟩

/-- **The σ-thread does not move at instruction rows** (the analogue of `SegKeepM2`). -/
def SigKeep (tr : Trace) (pub : List F) (σ : Nat → St) : Prop :=
  ∀ ρ ∈ actListM2 tr pub, ρ.1 ≠ 22 →
    σ ((lvl (rowInM tr pub ρ)).toNat + 1) = σ (lvl (rowInM tr pub ρ)).toNat

/-! ## 2. Instruction rows: non-host code, hence they keep the thread -/

/-- **Every active instruction row executes a non-host instruction** (at every related state): the
argument of `seg_instr_regKeep` (FETCH op `< 0x1FF`, `recordAtM2_nonHost`), stopped before
`regKeep_of_code`. -/
theorem seg_instr_codeNonHost (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hcode : CodeOK X.toCtx tr) :
    ∀ ρ ∈ actListM2 tr pub, ρ.1 ≠ 22 → CodeNonHost X.toCtx (rowInM tr pub ρ) := by
  intro ρ hρ hne
  have hP := P_val
  obtain ⟨t, r⟩ := ρ
  simp only at hne
  rcases mem_actListM2 hρ with ⟨h22, -, -⟩ | ⟨htI, hr, ha⟩
  · exact absurd h22 hne
  obtain ⟨ht, hcon, hint⟩ := seg_instr_tab nloc ngl t htI
  have hbit : ∀ i ∈ bcOf (chipM2 t), (tr.cell t r i).toNat ≤ 1 := by
    intro i hi
    have h := H.constr t ht r hr _ (by rw [hcon]; exact bcOf_mem hi)
    simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', Trace.row] at h
    have h' : ((rowNat tr t r i : Nat) : F) * (((rowNat tr t r i : Nat) : F) - ((1 : Nat) : F)) = 0 := by
      simp only [rowNat, Fp.cast_toNat]; exact h
    rcases bool_nat (rowNat_lt tr t r i) h' with h0 | h1 <;> (show rowNat tr t r i ≤ 1; omega)
  obtain ⟨i, hi, hb, hs, hc1, hpc, hop⟩ := fetch_op_lt (instr_fetchOpOk t htI) hbit ha
  have ho := row_occ (pub := pub) ht hr (hint i hi)
  obtain ⟨j, hj, hm⟩ := seg_fetchM2 H X hcode (o := (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)),
    (i.count.eval (tr.row pub t r)).toNat)) ho hb hs hc1
  simp only at hm
  have eI : rowInM tr pub (t, r) = rowIn (chipM2 t) tr pub t r := by
    have ec : chipTM2 t = chipM2 t := by simp [chipTM2, hne]
    simp [rowInM, ec]
  rw [eI]
  intro E s f tps tpl tt pc S live a b R hin ins hins
  -- the record of `j` is `recordAtM2` at a location `(k, l)`
  obtain ⟨k, l, hk, hl, hoff, hrj⟩ := X.recG hj
  have hrec := X.rec_at hk hl
  have hsz : l < (X.ckOf k).records.size := by rw [(X.factsOf hk).records]; exact hl
  rw [Array.getElem?_eq_getElem hsz] at hrec
  simp only [codeRecM2, hrj, Option.getD_some, Array.getElem?_eq_getElem hsz] at hm
  generalize (X.ckOf k).records[l] = rec at hrec hm
  -- its pc is the row's pc
  have hpc0 := recordAtM2_pc hrec
  have hop1 := recordAtM2_op_lt hrec
  have htot : X.M.codeSize < 2 ^ 20 := X.mf.total
  have hkE := R.kLt
  have hpcE := R.pcLt
  simp only [toCtx_nf, toCtx_pfOf] at hkE hpcE
  have hoffE := X.off_bound hkE
  have hoffk := X.off_bound hk
  have h0 := congrArg (fun m => m.getD 0 0) hm
  have h1 := congrArg (fun m => m.getD 1 0) hm
  simp only [getD_map_cast] at h0 h1
  rw [hpc, hin, hpc0] at h0
  have e0 : X.offOf k + l = X.offOf E.k + pc :=
    natEq (by simpa [stMsg] using h0.symm) (by omega) (by omega)
  obtain ⟨rfl, rfl⟩ := X.loc_unique hk hl hkE hpcE e0
  have hopN : rec.getD 1 0 < 0x1FF := by
    rw [h1, Fp.toNat_cast_of_lt (by omega)] at hop
    exact hop
  exact recordAtM2_nonHost hrec (by simpa using hins) hopN

/-- An instruction row's unrestricted segment facts (the instruction branch of
`rowFactsSegMap_seg`). -/
theorem rowFactsSegMap_instr (X : Ctx) {tr : Trace} {pub : List F} (hI : SegInstrRows X tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) {ρ : Nat × Nat} (hρ : ρ ∈ actListM2 tr pub)
    (hne : ρ.1 ≠ 22) :
    RowFactsSegMap X (rowInM tr pub ρ) (rowOutM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ) sg := by
  obtain ⟨t, r⟩ := ρ
  rcases mem_actListM2 hρ with ⟨h22, -, -⟩ | ⟨htI, hr, ha⟩
  · exact absurd h22 hne
  simp only at htI hr ha hne
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

/-- **Assembling the σ-pinned row facts.**  Instruction rows: `SegInstrRows` (+ `SegKeepM2`),
restricted by `rowJKeep_sig` (non-host code + `SigKeep`); HOST rows: `HoldRowSσ` verbatim. -/
theorem rowFactsSegMapJ_seg (X : M2Ctx) {nloc ngl : Nat} {tr : Trace} {pub : List F}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hcode : CodeOK X.toCtx tr)
    (hI : SegInstrRows X.toCtx tr pub) {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {σ : Nat → St} (hsk : SigKeep tr pub σ) (hhold : HoldRowSσ X.toCtx tr pub sg σ) :
    ∀ ρ ∈ actListM2 tr pub, RowFactsSegMapJ X.toCtx (SigJ σ) (rowInM tr pub ρ) (rowOutM tr pub ρ)
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
      (rowJKeep_sig (seg_instr_codeNonHost X H hcode ρ hρ h22) (hsk ρ hρ h22))

/-! ## 3. The segment soundness theorem, σ-pinned -/

/-- **`seg_sound_σ`: segment soundness (cut case) from `HoldsX`, host side pinned.**

As `seg_sound`, with the HOST-row premises `HoldRowS`/`HostRely` replaced by their σ-pinned forms
`HoldRowSσ`/`HostRelyσ` (satisfiable by honest runs), plus `SigKeep` and the in-boundary pin
`sideR s0 = σ (t_in + 1)`; the conclusion adds `sideR sN = σ (t_out + 1)` and `RegWF sN`. -/
theorem seg_sound_σ (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {σ : Nat → St} (hsk : SigKeep tr pub σ) (hhold : HoldRowSσ X.toCtx tr pub sg σ)
    (hrely : HostRelyσ X.toCtx tr pub σ)
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
      (initS tr pub)) (hw0 : RegWF s0) (hσ0 : sideR s0 = σ ((pub.getD pubTIn 0).toNat + 1)) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    ∃ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN ∧
      (∀ m, run X.toCtx.cfg X.toCtx.p ((actListM2 tr pub).length + m) s0 = run X.toCtx.cfg X.toCtx.p m sN) ∧
      BndC X.toCtx sg sN (pub.getD pubTOut 0).toNat (pub.getD pubSOut 0).toNat (segFinM tr pub) (finS tr pub) ∧
      cutoList tr = cutView X.toCtx sN ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxOut = SegSha.limbsF d ∧
        SegSha.wbytes d = cutDigest (cutView X.toCtx sN)) ∧
      (∀ y ∈ cutView X.toCtx sN, MsgWF y) ∧
      RegWF sN ∧ sideR sN = σ ((pub.getD pubTOut 0).toNat + 1) := by
  have hP := P_val
  have hrk : InstrRegKeep X.toCtx tr pub := seg_instr_regKeep X H hcode
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfacts X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMapJ_seg X H hcode hI hkeep hsk hhold
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
  have hQ : ∀ ρ ∈ actListM2 tr pub, RowQJ X.toCtx (SigJ σ)
      (fun s live => (RegC live s ∧ SpC live) ∧ RegWF s) (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ) := by
    intro ρ hρ
    by_cases h22 : ρ.1 = 22
    · exact rowQJ_and (rowQJ_and (hrely.reg ρ hρ h22) (RowQ.toJ (hostRely_sp X.toCtx tr pub ρ hρ h22)))
        (hrely.wf ρ hρ h22)
    · exact RowQ.toJ (rowQ_and (rowQ_and (seg_instr_rowQ_reg H hρ h22 (hlv ρ hρ) (hrk ρ hρ h22))
        (seg_instr_rowQ_sp H hρ h22 (hlv ρ hρ))) (rowQ_regWF_keep (hrk ρ hρ h22)))
  obtain ⟨-, hcut, -⟩ := exec_rowsJ X.toCtx (actListM2 tr pub) (rowInM tr pub) (rowOutM tr pub) (consCHS tr pub)
    (prodCHS tr pub) (initS tr pub) (finS tr pub) (pub.getD pubPcOut 0) (pub.getD pubTOut 0 + 1)
    (pub.getD pubSOut 0) sg 0 (by decide) (SigJ σ) hrows (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat
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

#print axioms seg_instr_codeNonHost
#print axioms rowFactsSegMapJ_seg
#print axioms seg_sound_σ

end WasmBase
