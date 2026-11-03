import WasmBase.Main.SegRegKeep
import WasmBase.Main.SegS.SegRowsX
/-!
# WasmBase.Main.SegS.SegRegKeep — `SegRegKeep`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegRegKeep.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- An instruction table is not table 20. -/
theorem instr_segT {t : Nat} (h : IsInstrM2 t) : SegT t :=
  ⟨by rcases h with ⟨_, _⟩ | rfl | rfl | rfl <;> first | omega | decide⟩

/-- **Instruction rows keep the register file** (`InstrRegKeep`): the instruction an active instruction
row executes is `NonHostI`. -/
theorem seg_instr_regKeepS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) (hcode : CodeOK X.toCtx tr) :
    ∀ ρ ∈ actListM2 tr pub, ρ.1 ≠ 22 → RegKeep X.toCtx (rowInM tr pub ρ) := by
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
  refine regKeep_of_code fun E s f tps tpl tt pc S live a b R hin ins hins => ?_
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

end WasmBase
