import WasmBase.Main.SegTomb
import WasmBase.Main.SegS.SegSoundX
/-!
# WasmBase.Main.SegS.SegTomb — `SegTomb`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegTomb.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- **An instruction row's space-4 production is CALL's record.** -/
theorem instr_send4S {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    {t r : Nat} (htI : IsInstrM2 t) (hr : r < tr.height t) {m : List F}
    (hm : m ∈ rowMsgs (chipM2 t) tr pub t r busStk true)
    (hl : (lvl (rowIn (chipM2 t) tr pub t r)).toNat + 16 < P)
    (hc : ((rowIn (chipM2 t) tr pub t r).getD 5 0).toNat + 16 < P)
    (h4 : (decMsg m).space = 4) : t = 13 ∧ decMsg m = callRecMsg tr pub r := by
  obtain ⟨i, hi, rfl⟩ := mem_rowMsgs hm
  have hb := (List.mem_filter.mp hi).2
  simp only [decide_eq_true_eq] at hb
  have hR := List.all_eq_true.mp (instr_rec4 t htI) i (List.mem_filter.mp hi).1
  by_cases hh : i.msg.head? = some (.c 4)
  · simp only [hb.1, hb.2, hh, decide_true, Bool.and_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq] at hR
    obtain ⟨rfl, rfl⟩ := hR
    exact ⟨rfl, rfl⟩
  · exfalso
    have hS := List.all_eq_true.mp (instr_spform t htI) i (List.mem_filter.mp hi).1
    simp only [Bool.or_eq_true, decide_eq_true_eq, hb.1, ne_eq, not_true_eq_false, false_or] at hS
    refine space_ne4_of (fun hl' => ?_) hl hc (spAllowedNo4_of hS hh) h4
    -- LOCAL: `isG` is a bit and `kCid` is the STATE activation id
    have h9 : t = 9 := by simpa using hl'
    subst h9
    have hT : (wasmBaseSegAir nloc ngl).tables[9]'(by simp [seg_air_len]) = Local.table :=
      seg_chipT nloc ngl 9 (by omega) (by omega)
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

/-- **`TombDead` from the trace** (core form): from `HoldsX`, the row facts of every action row, the
CH fold premises, the in-boundary relation `h0` and the size bounds, for any final status `st ≤ 2`. -/
theorem seg_tombDead_rowsS (X : Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat}
    (hrows : ∀ ρ ∈ actListM2 tr pub,
      RowFactsSegMap X (rowInM tr pub ρ) (rowOutM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ) sg)
    (st : Nat) (hst2 : st ≤ 2) (hstN : pub.getD Boundary.pubStatus 0 = ((st : Nat) : F))
    (hinit : (initS tr pub).Nodup)
    (ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P)
    (hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64)
    {s0 : St} (h0 : Bnd X sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) :
    TombDead tr pub (finS tr pub) := by
  have hP := P_val
  have hch := seg_hchS H X hb hg
  have hst : (segM0 tr pub :: (actListM2 tr pub).map (rowOutM tr pub)).Perm
      ([pub.getD pubPcOut 0, pub.getD pubTOut 0 + 1, pub.getD pubSOut 0, ((st : Nat) : F), pub.getD pubSbOut 0,
        tr.cell 0 0 (ix Segb.cols "cidf")] :: (actListM2 tr pub).map (rowInM tr pub)) := by
    have h := seg_hstS H
    rw [segMF_eq, hstN] at h
    exact h
  obtain ⟨hnd, hinj, hrel⟩ := exec_rows_rel (X := X) (act := actListM2 tr pub) (inS := rowInM tr pub)
    (outS := rowOutM tr pub) (cons := consCHS tr pub) (prod := prodCHS tr pub) (init := initS tr pub)
    (fin := finS tr pub) (pcf := _) (N := _) (Sf := _) sg st hst2 hrows _ _ _ _ _ hst hch hinit
    (fun x hx => Nat.le_of_eq (seg_initS_tp tr pub x hx)) ht hfee hstepgas hg64 h0
    (fun _ _ => True) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) trivial
  -- every row: its time is `t0 + k + 1` and its activation id is `< 2^28`
  have hrow : ∀ ρ ∈ actListM2 tr pub, ∃ k, k < (actListM2 tr pub).length ∧
      (lvl (rowInM tr pub ρ)).toNat = (pub.getD pubTIn 0).toNat + k + 1 ∧ ((rowInM tr pub ρ).getD 5 0).toNat < 2 ^ 28 := by
    intro ρ hρ
    obtain ⟨k, hk, s, q, pc, S, sb, cid, live, hin, -, ⟨E, f, tps, tpl, -, hcid, -, R⟩, -, -⟩ := hrel ρ hρ
    refine ⟨k, hk, ?_, ?_⟩
    · rw [hin]; exact Fp.toNat_cast_of_lt (by omega)
    · rw [hin]
      have := R.cidLt
      show ((cid : Nat) : F).toNat < 2 ^ 28
      rw [Fp.toNat_cast_of_lt (by omega)]; omega
  -- a row's space-4 production is CALL's record, of slot = the row's time
  have hprod : ∀ ρ ∈ actListM2 tr pub, ∀ x ∈ prodCHS tr pub ρ, x.space = 4 →
      ρ.1 = 13 ∧ x = callRecMsg tr pub ρ.2 ∧ x.slot = (lvl (rowInM tr pub ρ)).toNat := by
    intro ρ hρ x hx h4
    obtain ⟨t, r⟩ := ρ
    rcases mem_actListM2 hρ with ⟨h22, -, -⟩ | ⟨htI, hr, -⟩
    · simp only at h22; subst h22; exact absurd h4 (host_send_no4 hx)
    · simp only at htI hr ⊢
      have hne : t ≠ 22 := by rcases htI with ⟨_, h⟩ | h | h | h <;> omega
      obtain ⟨-, eP, eI⟩ := consProd_instr (tr := tr) (pub := pub) (r := r) hne
      obtain ⟨k, hk, hl, hc⟩ := hrow (t, r) hρ
      rw [eP] at hx
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      rw [eI] at hl hc
      obtain ⟨rfl, e⟩ := instr_send4S H htI hr hm (by omega) (by omega) h4
      refine ⟨rfl, e, ?_⟩
      rw [e, callRecMsg_slot, eI]
  intro r hr htk
  have hcon := table_constr_eqXS H (by simp [seg_air_len]) RetT.table (seg_t14' nloc ngl) hr
  obtain ⟨hs, ha, -, htk1⟩ := ret_count_vals_of hcon
  obtain ⟨-, -, -, -, hc0, -, -⟩ := ret_sound (rowNat tr 14 r) (tr.row pub 14 r) (rowNat_lt tr 14 r) hcon
  have htk' : (Ret.tk.eval (tr.row pub 14 r)).toNat = 1 := by omega
  have hmem : (14, r) ∈ actListM2 tr pub := ret_mem_actListM2 hr (by omega)
  -- the activation id is the row's STATE `cid`, `< 2^28`
  have eC : (rowInM tr pub (14, r)).getD 5 0 = tr.cell 14 r Ret.kCid := by
    rw [show rowInM tr pub (14, r) = rowIn Ret.table tr pub 14 r from rfl, ← stE_eval]; rfl
  obtain ⟨-, -, -, hcl⟩ := hrow (14, r) hmem
  rw [eC] at hcl
  refine ⟨hcl, hc0 (by omega), fun x hx h4 hxs => ?_⟩
  -- the count
  let c := rowNat tr 14 r Ret.kCid
  let p : Msg → Bool := fun x => decide (x.space = 4 ∧ x.slot = c)
  have hcnt := hch.countP_eq p
  have e2 : (finS tr pub ++ (actListM2 tr pub).flatMap (consCHS tr pub)).countP p =
      (finS tr pub).countP p + ((actListM2 tr pub).flatMap (consCHS tr pub)).countP p := by
    rw [List.countP_append]
  have hL : (initS tr pub ++ (actListM2 tr pub).flatMap (prodCHS tr pub)).countP p ≤ 1 := by
    refine countP_le_one_of hnd fun x hx y hy px py => ?_
    simp only [p, decide_eq_true_eq] at px py
    have side : ∀ a ∈ initS tr pub, ∀ b ∈ (actListM2 tr pub).flatMap (prodCHS tr pub),
        a.space = 4 → b.space = 4 → a.slot = b.slot → False := by
      intro a ha b hb ha4 hb4 hab
      obtain ⟨ρ, hρ, hbρ⟩ := List.mem_flatMap.mp hb
      obtain ⟨-, -, e⟩ := hprod ρ hρ b hbρ hb4
      obtain ⟨k, -, hl, -⟩ := hrow ρ hρ
      have := (bnd_rec4 h0 a ha ha4).2.1
      omega
    rcases List.mem_append.mp hx with hx | hx <;> rcases List.mem_append.mp hy with hy | hy
    · exact ((bnd_rec4 h0 x hx px.1).2.2.2 y hy py.1 (py.2.trans px.2.symm)).symm
    · exact (side x hx y hy px.1 py.1 (px.2.trans py.2.symm)).elim
    · exact (side y hy x hx py.1 px.1 (py.2.trans px.2.symm)).elim
    · obtain ⟨ρ, hρ, hxρ⟩ := List.mem_flatMap.mp hx
      obtain ⟨ρ', hρ', hyρ'⟩ := List.mem_flatMap.mp hy
      obtain ⟨-, ex, sx⟩ := hprod ρ hρ x hxρ px.1
      obtain ⟨-, ey, sy⟩ := hprod ρ' hρ' y hyρ' py.1
      have hl : lvl (rowInM tr pub ρ) = lvl (rowInM tr pub ρ') := by
        rw [← Fp.cast_toNat (lvl (rowInM tr pub ρ)), ← Fp.cast_toNat (lvl (rowInM tr pub ρ')), ← sx, ← sy,
          px.2, py.2]
      have := hinj ρ hρ ρ' hρ' hl
      subst this
      rw [ex, ey]
  have hC : 1 ≤ ((actListM2 tr pub).flatMap (consCHS tr pub)).countP p := by
    refine List.countP_pos_iff.mpr ⟨decMsg (retRec.msg.map (·.eval (tr.row pub 14 r))),
      List.mem_flatMap.mpr ⟨(14, r), hmem, ?_⟩, ?_⟩
    · obtain ⟨eC', -, -⟩ := consProd_instr (tr := tr) (pub := pub) (r := r) (t := 14) (by omega)
      rw [eC']
      exact List.mem_map_of_mem (mem_rowMsgs_of retRec_mem rfl rfl htk')
    · simp only [p, decide_eq_true_eq]
      refine ⟨?_, rfl⟩
      simp only [retRec, chRecv, decMsg, List.cons_append, List.map_cons, List.getD_cons_zero, Expr.eval]
      exact Fp.toNat_cast_of_lt (by omega)
  have hF : (finS tr pub).countP p = 0 := by omega
  exact List.countP_eq_zero.mp hF x hx (by simp only [p, decide_eq_true_eq]; exact ⟨h4, hxs⟩)

/-- **`seg_tombDeadS`: `TombDead` at the out-boundary, from `seg_soundS`'s own hypotheses** (any final
status `st ≤ 2`, so also for halting segments): the instruction rows' facts from `seg_rowfactsS`
(`CodeOK`/`FuncOK`), the HOST rows' `HoldRowS`, the CH fold (`HostBLinked`, `RegCLinked`), the size
bounds, `initS` Nodup and the in-boundary relation `h0`. -/
theorem seg_tombDeadS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X.toCtx tr pub sg)
    (st : Nat) (hst2 : st ≤ 2) (hstN : pub.getD Boundary.pubStatus 0 = ((st : Nat) : F))
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (h0 : Bnd X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) :
    TombDead tr pub (finS tr pub) := by
  have hP := P_val
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfactsS X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMap_seg X.toCtx hI hkeep hhold
  have hlenEq := seg_lenS H (fun ρ hρ => (hrows ρ hρ).tsOut) (by omega)
  have ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P := by omega
  have hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.toCtx.maxFee + 1) < P := by
    have e : (pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat = (actListM2 tr pub).length := by omega
    rw [e] at hfeeN; exact hfeeN
  exact seg_tombDead_rowsS X.toCtx H hb hg hrows st hst2 hstN hinit ht hfee hstepgas hg64 h0

end WasmBase
