import WasmBase.Main.SegSoundSigma
import WasmBase.Main.SegSoundMP

/-!
# WasmBase.Main.SegSoundSigmaMP — `seg_sound_σ` from `HoldsXS`, and for the multiproof AIR

`seg_sound_σS` is `seg_sound_σ` (`Main/SegSoundSigma.lean`) with `HoldsX (wasmBaseSegAir …)` replaced
by `HoldsXS` (`Main/SegHoldsS.lean`), the proof's trace lemmas by their `…S` copies
(`Main/SegS/*`).  **`seg_sound_σ_mp`**: the multiproof segment AIR `wasmBaseSegAirMP` through
`HoldsX.toSMP` / `ChipIf.toSMP` (as `seg_sound_mp`).  Same σ-pinned premises (`HoldRowSσ`,
`HostRelyσ`, `SigKeep`, the in-pin) and the same conclusion (`sideR sN = σ (t_out + 1)`, `RegWF sN`).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
open HostFoot StepSide
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- `seg_instr_codeNonHost` from `HoldsXS` (the argument of `seg_instr_regKeepS`). -/
theorem seg_instr_codeNonHostS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) (hcode : CodeOK X.toCtx tr) :
    ∀ ρ ∈ actListM2 tr pub, ρ.1 ≠ 22 → CodeNonHost X.toCtx (rowInM tr pub ρ) := by
  intro ρ hρ hne
  have hP := P_val
  obtain ⟨t, r⟩ := ρ
  simp only at hne
  rcases mem_actListM2 hρ with ⟨h22, -, -⟩ | ⟨htI, hr, ha⟩
  · exact absurd h22 hne
  obtain ⟨ht, hcon, hint⟩ := seg_instr_tab nloc ngl t htI
  have : SegT t := instr_segT htI
  have hbit : ∀ i ∈ bcOf (chipM2 t), (tr.cell t r i).toNat ≤ 1 := by
    intro i hi
    have h := H.constr t ht r hr _ (by rw [hcon]; exact bcOf_mem hi)
    simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', Trace.row] at h
    have h' : ((rowNat tr t r i : Nat) : F) * (((rowNat tr t r i : Nat) : F) - ((1 : Nat) : F)) = 0 := by
      simp only [rowNat, Fp.cast_toNat]; exact h
    rcases bool_nat (rowNat_lt tr t r i) h' with h0 | h1 <;> (show rowNat tr t r i ≤ 1; omega)
  obtain ⟨i, hi, hb, hs, hc1, hpc, hop⟩ := fetch_op_lt (instr_fetchOpOk t htI) hbit ha
  have ho := row_occ (pub := pub) ht hr (hint i hi)
  obtain ⟨j, hj, hm⟩ := seg_fetchM2S H X hcode (o := (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)),
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

/-- **Assembling the σ-pinned row facts** (`rowFactsSegMapJ_seg`, with the non-host code of the
instruction rows as a hypothesis). -/
theorem rowFactsSegMapJ_of (X : Ctx) {tr : Trace} {pub : List F}
    (hnh : ∀ ρ ∈ actListM2 tr pub, ρ.1 ≠ 22 → CodeNonHost X (rowInM tr pub ρ))
    (hI : SegInstrRows X tr pub) {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {σ : Nat → St} (hsk : SigKeep tr pub σ) (hhold : HoldRowSσ X tr pub sg σ) :
    ∀ ρ ∈ actListM2 tr pub, RowFactsSegMapJ X (SigJ σ) (rowInM tr pub ρ) (rowOutM tr pub ρ)
      (consCHS tr pub ρ) (prodCHS tr pub ρ) sg := by
  intro ρ hρ
  by_cases h22 : ρ.1 = 22
  · obtain ⟨t, r⟩ := ρ
    simp only at h22
    subst h22
    rcases mem_actListM2 hρ with ⟨-, hr, ha⟩ | ⟨htI, -, -⟩
    · exact hhold r hr ha
    · exfalso; rcases htI with ⟨_, h⟩ | h | h | h <;> simp_all
  · exact RowFactsSeg.toJ (rowFactsSegMap_instr X hI hkeep hρ h22)
      (rowJKeep_sig (hnh ρ hρ h22) (hsk ρ hρ h22))

/-- **`seg_sound_σS`**: `seg_sound_σ` from `HoldsXS`. -/
theorem seg_sound_σS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIfS SegSha.compressW nloc ngl pub tr chip) (hl : CutoHiLimbs tr)
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
  have hrk : InstrRegKeep X.toCtx tr pub := seg_instr_regKeepS X H hcode
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfactsS X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMapJ_of X.toCtx (seg_instr_codeNonHostS X H hcode) hI hkeep hsk hhold
  have hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1 :=
    fun ρ hρ => (hrows ρ hρ).flat.tsOut
  have hlenEq := seg_lenS H hts (by omega)
  have hlv : ∀ ρ ∈ actListM2 tr pub, (lvl (rowInM tr pub ρ)).toNat < 2 ^ 30 := by
    intro ρ hρ
    have := seg_row_lvlS H hts (by omega) ρ hρ
    omega
  have ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P := by omega
  have hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.toCtx.maxFee + 1) < P := by
    have e : (pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat = (actListM2 tr pub).length := by omega
    rw [e] at hfeeN; exact hfeeN
  have hst := seg_hstS H
  rw [segMF_eq, hst0] at hst
  have hQ : ∀ ρ ∈ actListM2 tr pub, RowQJ X.toCtx (SigJ σ)
      (fun s live => (RegC live s ∧ SpC live) ∧ RegWF s) (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ) := by
    intro ρ hρ
    by_cases h22 : ρ.1 = 22
    · exact rowQJ_and (rowQJ_and (hrely.reg ρ hρ h22) (RowQ.toJ (hostRely_sp X.toCtx tr pub ρ hρ h22)))
        (hrely.wf ρ hρ h22)
    · exact RowQ.toJ (rowQ_and (rowQ_and (seg_instr_rowQ_regS H hρ h22 (hlv ρ hρ) (hrk ρ hρ h22))
        (seg_instr_rowQ_spS H hρ h22 (hlv ρ hρ))) (rowQ_regWF_keep (hrk ρ hρ h22)))
  obtain ⟨-, hcut, -⟩ := exec_rowsJ X.toCtx (actListM2 tr pub) (rowInM tr pub) (rowOutM tr pub) (consCHS tr pub)
    (prodCHS tr pub) (initS tr pub) (finS tr pub) (pub.getD pubPcOut 0) (pub.getD pubTOut 0 + 1)
    (pub.getD pubSOut 0) sg 0 (by decide) (SigJ σ) hrows (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat
    (segM0 tr pub) (pub.getD pubSbOut 0) (tr.cell 0 0 (ix Segb.cols "cidf")) hst (seg_hchS H X.toCtx hb hg) hinit
    (fun x hx => Nat.le_of_eq (seg_initS_tp tr pub x hx)) ht hfee hstepgas hg64 h0.1 _ hQ ⟨⟨h0.2.1, h0.2.2⟩, hw0⟩
    hσ0
  obtain ⟨sN, h1, h2, h3, ⟨⟨h4, h5⟩, h6⟩, hJ⟩ := hcut rfl
  have hB : BndC X.toCtx sg sN ((pub.getD pubTIn 0).toNat + (actListM2 tr pub).length) (pub.getD pubSOut 0).toNat
      (segFinM tr pub) (finS tr pub) := ⟨h3, h4, h5⟩
  obtain ⟨σ', A, hIds, -, hv⟩ := cutView_eqL (M2Ctx.toCtx_fns_nodup X) hB
  have hset : ∀ y, y ∈ cutoList tr ↔ y ∈ cutView X.toCtx sN :=
    fun y => (cuto_linkS H hl hIds seg_cuto_in_fin (seg_finSplitS H) hT y).trans (hv y)
  have e := ctx_out_eq (cuto_sortedS H hl) hset (cutView_nodup X.toCtx h6)
  obtain ⟨d, hd6, hW, hpub, hsha⟩ := ctx_out_shaS H hC hl
  refine ⟨hlenEq, sN, h1, h2, by rw [hlenEq]; exact hB, e, ⟨d, hd6, hW, hpub, by rw [hsha, e]⟩,
    cutView_wf (cuto_wfS H hl) hset, h6, ?_⟩
  rw [hlenEq]; exact hJ

/-- **`seg_sound_σ_mp`: `seg_sound_σ` for the multiproof segment AIR `wasmBaseSegAirMP`.** -/
theorem seg_sound_σ_mp (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAirMP nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
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
      RegWF sN ∧ sideR sN = σ ((pub.getD pubTOut 0).toNat + 1) :=
  seg_sound_σS X H.toSMP (SegSha.ChipIf.toSMP H hC) hl hcode hfunc hb hg hkeep hsk hhold hrely hst0 hlen htin
    hfeeN hstepgas hg64 hinit hT h0 hw0 hσ0

#print axioms seg_instr_codeNonHostS
#print axioms seg_sound_σS
#print axioms seg_sound_σ_mp

end WasmBase
