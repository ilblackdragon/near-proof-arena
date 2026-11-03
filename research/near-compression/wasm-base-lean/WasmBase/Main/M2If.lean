import WasmBase.Main.M2Looks
import WasmBase.Main.RowIf
/-!
# WasmBase.Main.M2If — `RowFacts` of the `IF` rows (table 26) of a `wasmBaseM2Air` trace

`Main/RowIf.lean`'s `if_rowfacts` (now for any table index) needs `IfRowData`: the checker's data
for the row's pc.  For the M2 context it is **derived**, not assumed:

* the FETCH answer with opcode `opIf` is an `if` record (`recordAtM2_if_op`), which pins the
  instruction `.if_ bt`, its `endOf`/`elseOf`, the fee, the height and the false target;
* the two successors are `verifyAtM2`'s (`M2Ctx.if_succ`, unfolded by `ifStepM2_spec`);
* the condition's producer-time bound is the R16 time check (`m2_time_chk`).

Result: `if_rowfacts_m2` — `RowFacts X.toCtx …` for every active IF row (`if` with or without a
result).
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-- A record of an M2-checked pc with opcode `opIf` is that pc's `if` record. -/
theorem recordAtM2_if_op {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)}
    {H : Array Nat} {off pc : Nat} {cinfo : Nat → Option Nat} {rec : List Nat}
    (hr : recordAtM2 cfg p pf L H off cinfo pc = some rec) (hop : rec.getD 1 0 = IfC.opIf) :
    ∃ bt e el fee, pf.code[pc]? = some (.if_ bt) ∧ pf.endOf[pc]? = some e ∧
      pf.elseOf[pc]? = some el ∧ feeUnits cfg pf.gas[pc]? = some fee ∧
      rec = [off + pc, IfC.opIf, H[pc]?.getD 0, fee, el + 1 + off, 0, 0, 0] := by
  unfold recordAtM2 at hr
  repeat' split at hr
  all_goals first
    | (exact absurd hop (recordOf_ne_opIf hr))
    | (simp at hr; done)
    | (simp only [Option.some.injEq] at hr; subst hr
       exact ⟨_, _, _, _, by assumption, by assumption, by assumption, by assumption, rfl⟩)
    | (simp only [Option.some.injEq] at hr; subst hr
       simp [IfC.opIf, Ctrl.opJump, Chips.opHost, opHostX, opUnreach, opMemGrowX, opMemSizeX] at hop; done)
    | (simp only [Option.some.injEq] at hr; subst hr
       simp only [List.getD_cons_succ, List.getD_cons_zero] at hop
       subst hop; simp_all [isConvOp, IfC.opIf])

/-- `ifStepM2`, unfolded: the pushed label, the post-pop height and both successors. -/
theorem ifStepM2_spec {pf : PFunc} {ls : List Label} {h pc : Nat} {bt : BT}
    {lsT lsF : List Label} {hT ftgt hF e el : Nat}
    (he : pf.endOf[pc]? = some e) (hel : pf.elseOf[pc]? = some el)
    (hs : ifStepM2 pf ls h pc bt = some (lsT, hT, ftgt, lsF, hF)) :
    1 ≤ h ∧ hT = h - 1 ∧ lsT = mkIfLabel bt e (h - 1) :: ls ∧ ftgt = el + 1 ∧
      lsF = (if el = e then ls else mkIfLabel bt e (h - 1) :: ls) ∧ hF = h - 1 := by
  unfold ifStepM2 at hs
  rw [he, hel] at hs
  simp only at hs
  split at hs
  · split at hs
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨h1, h2, h3, h4, h5⟩ := hs
      exact ⟨hc.1, h2.symm, h1.symm, h3.symm, h4.symm, h5.symm⟩
    · simp at hs
  · simp at hs

theorem m2_t26 (nloc ngl : Nat) :
    (wasmBaseM2Air nloc ngl).tables[26]'(by rw [m2_air_len]; decide) = IfC.table := by
  simp [wasmBaseM2Air, wasmBaseAir]

/-- **`RowFacts` of an active IF row** of a `Holds (wasmBaseM2Air …)` trace, for the M2 context. -/
theorem if_rowfacts_m2 (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hpub : PubOK X.toCtx nloc ngl pub)
    (hcode : CodeOK X.toCtx tr)
    {r : Nat} (hr : r < tr.height 26) (hact : rowAct IfC.table tr pub 26 r) :
    RowFacts X.toCtx (rowIn IfC.table tr pub 26 r) (rowOut IfC.table tr pub 26 r)
      (rowCons IfC.table tr pub 26 r) (rowProd IfC.table tr pub 26 r) := by
  have hP' := P_val
  have hcP := rowNat_lt tr 26 r
  have ht : 26 < (wasmBaseM2Air nloc ngl).tables.length := by rw [m2_air_len]; decide
  have hT := m2_t26 nloc ngl
  have hcon : ∀ e ∈ IfC.constraints, e.eval (natRow (rowNat tr 26 r) (tr.row pub 26 r)) = 0 :=
    table_constr_eq H ht IfC.table hT hr
  have hact' : (((rowNat tr 26 r IfC.fIf : Nat) : F)).toNat = 1 := by
    rw [Fp.toNat_cast_of_lt (hcP _)]; exact hact
  have occ : ∀ i ∈ IfC.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 26 r)),
      (i.count.eval (tr.row pub 26 r)).toNat) ∈ occs (wasmBaseM2Air nloc ngl) tr pub := by
    intro i hi
    refine row_occ ht hr ?_
    rw [hT]; exact hi
  -- the FETCH pin
  have hfo := occ (fetch (v cPc) (Expr.c IfC.opIf) (v cH) (v cFee) [v IfC.tgt, 0, 0, 0] IfC.act)
    (by simp [IfC.inters])
  simp only [fetch, List.cons_append, List.nil_append, List.map_cons, List.map_nil, IfC.act,
    Expr.eval_ofNat', Expr.eval_c, conv_col_eval, hact'] at hfo
  obtain ⟨j, hj, hm⟩ := m2_fetch X H hcode (m2_hsend_fetch H hpub) hfo rfl rfl rfl
  simp only [codeRecM2] at hm
  obtain ⟨k, l, hk, hl, hoff, hrj⟩ := X.recG hj
  have hrec := X.rec_at hk hl
  have hsz : l < (X.ckOf k).records.size := by rw [(X.factsOf hk).records]; exact hl
  rw [Array.getElem?_eq_getElem hsz] at hrec
  have hopl := X.recOp_lt hj
  rw [hrj, Option.getD_some, Array.getElem?_eq_getElem hsz, Option.getD_some] at hm hopl
  obtain ⟨a, op, b, c, d, e5, f, g, hsh⟩ := recordAtM2_shape hrec
  rw [hsh] at hm hopl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hopl
  have hm2 := hm
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm2
  obtain ⟨-, e1, -, -, -, -, -, -⟩ := hm2
  have hopEq : op = IfC.opIf := (natEq e1 (by simp [IfC.opIf]; omega) (by omega)).symm
  obtain ⟨bt, e, el, fee, hins, hend, hels, hfee, hrr⟩ :=
    recordAtM2_if_op (hrec.trans (congrArg some hsh)) (by rw [hopEq]; rfl)
  rw [hrr] at hm
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm
  obtain ⟨m0, -, m3, m4, m6⟩ := hm
  have hjl : j < 2 ^ 20 := Nat.lt_trans hj X.mf.total
  have hhb := (X.factsOf hk).hBound l hl
  have hfl := feeUnits_lt hfee
  have hoffb := X.off_bound hk
  have htot : X.M.codeSize < 2 ^ 20 := X.mf.total
  have p0 : rowNat tr 26 r cPc = X.offOf k + l := natEq m0 (hcP _) (by omega)
  have p3 : rowNat tr 26 r cH = (X.ckOf k).heights[l]?.getD 0 := natEq m3 (hcP _) (by omega)
  have p4 : rowNat tr 26 r cFee = fee := natEq m4 (hcP _) (by omega)
  have helt : el + 1 < (X.pfOf k).code.size := by
    obtain ⟨ls, h, hls, hh⟩ := (X.factsOf hk).lh hl
    obtain ⟨lsT, hT', ftgt, lsF, hF, hs, -, -, -, h5, -, -⟩ := X.if_succ hk hins hls hh
    have := ifStepM2_spec hend hels hs
    rw [← this.2.2.2.1]; exact h5
  have p6 : rowNat tr 26 r IfC.tgt = el + 1 + X.offOf k := natEq m6 (hcP _) (by omega)
  have hfeeMax : fee ≤ X.toCtx.maxFee := by
    have := X.recFee_le hj
    rw [hrj, Option.getD_some, Array.getElem?_eq_getElem hsz, Option.getD_some, hsh, hrr] at this
    simpa using this
  -- the checker data
  have hd : IfRowData 26 X.toCtx tr r fee :=
    { k := k, pc := l, bt := bt, e := e, el := el, kLt := hk, pcLt := hl, gpc := p0.symm,
      ins := hins, endE := hend, elseE := hels, feeEq := hfee, tgt := p6, hEq := p3,
      hLt := by rw [p3]; exact hhb,
      succ := by
        intro ls h hls hh
        obtain ⟨lsT, hT', ftgt, lsF, hF, hs, h1, h2, h3, h4, h5, h6⟩ := X.if_succ hk hins hls hh
        obtain ⟨q1, q2, q3, q4, q5, q6⟩ := ifStepM2_spec hend hels hs
        subst q2 q3 q4 q5 q6
        exact ⟨h - 1, q1, rfl, h1, h2, h3, h4, h5, h6⟩ }
  -- the condition's producer time
  have hconsT : ∀ x ∈ rowCons IfC.table tr pub 26 r, ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧
      ((x.tp + 1 + n : Nat) : F) = lvl (rowIn IfC.table tr pub 26 r) := by
    intro x hx
    rw [if_rowCons hact] at hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst hx
    have h1 := occ ((timeChk (v cTs) (v IfC.tc) (v IfC.hc) IfC.act)[0]'(by simp [timeChk]))
      (by simp [IfC.inters, timeChk])
    have h2 := occ ((timeChk (v cTs) (v IfC.tc) (v IfC.hc) IfC.act)[1]'(by simp [timeChk]))
      (by simp [IfC.inters, timeChk])
    simp only [timeChk, r16, B16, IfC.act, List.getElem_cons_zero, List.getElem_cons_succ, List.map_cons,
      List.map_nil, Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', conv_col_eval, hact'] at h1 h2
    obtain ⟨n, hn, he⟩ := m2_time_chk H (m2_hsend_r16 H hpub) h1 h2
    refine ⟨n, hn, ?_⟩
    rw [if_rowIn]
    simp only [lvl, List.getD_cons_succ, List.getD_cons_zero]
    rw [Fp.toNat_cast_of_lt (hcP _)] at he
    rw [he, cell_cast tr 26 r 1]; rfl
  exact if_rowfacts hcon hact hfeeMax p4 hd hconsT

#print axioms if_rowfacts_m2

end WasmBase
