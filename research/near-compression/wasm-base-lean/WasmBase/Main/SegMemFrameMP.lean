import WasmBase.Main.SegMemFrame
import WasmBase.Main.SegSoundMP

/-!
# WasmBase.Main.SegMemFrameMP — the memory frame for the multiproof AIR (E2E M4c, MEM)

`seg_instr_pagesKeepS`, `seg_mem_frameS`: `SegMemFrame`'s `seg_instr_pagesKeep` / `seg_mem_frame` over
`HoldsXS` (`Main/SegHoldsS.lean`: the segment relation without table 20 and the buses 15/16/17/103),
with the `HoldsXS` copies of the lemmas they use (`Main/SegS/*`).  **`seg_mem_frame_mp`**: the same
for `wasmBaseSegAirMP`, via `HoldsX.toSMP`.  Named premise as before: `HostPagesRely` (M6).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

theorem seg_instr_pagesKeepS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) (hcode : CodeOK X.toCtx tr) :
    ∀ ρ ∈ actListM2 tr pub, ρ.1 ≠ 22 → PagesKeep X.toCtx (rowInM tr pub ρ) := by
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
  refine pagesKeep_of_code fun E s f tps tpl tt pc S live a b R hin ins hins => ?_
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
  exact ⟨recordAtM2_nonHost hrec (by simpa using hins) hopN, recordAtM2_noGrow hrec (by simpa using hins) hopN⟩



theorem seg_mem_frameS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X.toCtx tr pub sg)
    (hpr : HostPagesRely X.toCtx tr pub)
    (hst0 : pub.getD Boundary.pubStatus 0 = 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (h0 : Bnd X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) :
    ∀ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN →
      sN.pages.size = s0.pages.size ∧
      ∀ a, (∀ x ∈ initS tr pub, x.space = 3 → x.slot ≠ a) → readByte sN a = readByte s0 a := by
  intro sN hseg
  have hP := P_val
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfactsS X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMap_seg X.toCtx hI hkeep hhold
  have hlenEq := seg_lenS H (fun ρ hρ => (hrows ρ hρ).tsOut) (by omega)
  have ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P := by omega
  have hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.toCtx.maxFee + 1) < P := by
    have e : (pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat = (actListM2 tr pub).length := by omega
    rw [e] at hfeeN; exact hfeeN
  let c := segCutS X.toCtx H hrows hb hg hst0 hinit ht hfee
  have hpk : ∀ r ∈ c.act, PagesKeep X.toCtx (c.inS r) := by
    intro ρ hρ
    by_cases h22 : ρ.1 = 22
    · exact hpr ρ hρ h22
    · exact seg_instr_pagesKeepS X H hcode ρ hρ h22
  have hsz := c.pages rfl hstepgas hg64 h0 hpk hseg
  refine ⟨hsz, fun a ha => ?_⟩
  by_cases hlt : a < memBytes s0
  · exact (c.frame rfl hstepgas hg64 h0 hlt (fun y hy h3 => ha y hy h3) hseg).1
  · have hm : memBytes sN = memBytes s0 := by unfold memBytes; rw [hsz]
    rw [readByte_oob (by omega), readByte_oob (by omega)]


/-- `seg_mem_frame` for the multiproof AIR `wasmBaseSegAirMP`. -/
theorem seg_mem_frame_mp (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X.toCtx tr pub sg)
    (hpr : HostPagesRely X.toCtx tr pub)
    (hst0 : pub.getD Boundary.pubStatus 0 = 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (h0 : Bnd X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) :
    ∀ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN →
      sN.pages.size = s0.pages.size ∧
      ∀ a, (∀ x ∈ initS tr pub, x.space = 3 → x.slot ≠ a) → readByte sN a = readByte s0 a :=
  seg_mem_frameS X H.toSMP hcode hfunc hb hg hkeep hhold hpr hst0 hlen htin hfeeN hstepgas hg64 hinit h0

#print axioms seg_instr_pagesKeepS
#print axioms seg_mem_frameS
#print axioms seg_mem_frame_mp

end WasmBase
