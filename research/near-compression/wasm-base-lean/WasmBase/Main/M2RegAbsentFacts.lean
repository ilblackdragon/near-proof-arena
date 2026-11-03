import WasmBase.Main.RegSendM2
import WasmBase.M2RegAbsent
/-!
# WasmBase.Main.M2RegAbsentFacts — the absent-register header of `wasmBaseM2rAir`

Proved (standard axioms only) for a satisfied trace of `wasmBaseM2rAir` (`WasmBase/M2RegAbsent.lean`):

* **`regAt_m2r`**: REG-A at index 27 satisfies the group walk's interface, so every lemma of
  `Main/RegWalkG.lean` applies; **`m2r_hsend_r16`**: the per-bus R16 send bound
  (`hsend_r16_of_tail`, with REG-A and RINIT `R16Ok`); hence `m2r_regLenAgree_group`,
  `m2r_reg_gap_lt`, `m2r_reg_pos_lt_len` without `hsend`.
* **Row facts of the header:**
  * `m2r_fill_consumes_absent`: an active **fill** length row (`act = 1, kind = 1, rd = 0`) of
    register `rid` receives, with count 1, the absent message `absentF rid atp` on the CH bus;
  * `m2r_fill_absent_time`: its producer time satisfies `atp ≤ ts` (given `ts, atp < 2^29`);
  * `m2r_clear_produces_absent`: an active **clear** length row (`act = 1, kind = 1, clr = 1`)
    sends `absentF rid ts` with count 1;
  * `m2r_rinit_produces_absent`: an active RINIT row sends `absentF rid 0` with count 1;
  * `m2r_lenAct`: a group's length row that follows a byte row of the same group is active;
  * `m2r_rinit_prefix`, `m2r_rinit_step`, **`m2r_rinit_strict`**: RINIT's active rows form a prefix
    and their ids are strictly increasing (as naturals, `< 2^16`), so **distinct**
    (`m2r_rinit_distinct`): RINIT produces at most one absent message per register id.

## Open (named)

The bus-level consequence — per register id, `#fills ≤ 1 + #clears`, hence (with the walk and
`cClrNext*`) no two length messages of one id are live at once — needs the CH-bus decomposition of
this AIR: that **only** RINIT, REG-A clears, REG-A fills and DRAIN carry space-6, tag-3 messages.
For DRAIN and the instruction tables the space/tag fields are column expressions, so this is the same
freshness obligation as `Main/ExecHost.msgs_ch_host` (not yet re-derived for the M2 tables).  The
row facts above are exactly its per-table inputs.
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## The walk interface and the R16 send bound -/

theorem regA_table_r16 : RegA.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by
  decide
theorem rinit_table_r16 : RInit.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by
  decide

theorem m2r_recv_only_range16 (nloc ngl : Nat) :
    ∀ T ∈ (wasmBaseM2rAir nloc ngl).tables, T ≠ Range16.table → ∀ i ∈ T.inters, i.bus = busR16 →
      i.send = true := by
  intro T hT hne i hi hb
  have hsplit : (wasmBaseM2rAir nloc ngl).tables =
      (wasmBaseAir nloc ngl).tables ++ [HostR.table, HostO.table, HostTab.table, HostB.table, IfC.table,
        RegA.table, Conv.table, Unreach.table, RInit.table] := rfl
  rw [hsplit, List.mem_append] at hT
  rcases hT with h | h
  · exact base_recv_only_r16 nloc ngl T h hne i hi hb
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact table_r16_of_all hostR_table_r16 i hi hb
    · exact table_r16_of_all hostO_table_r16 i hi hb
    · exact table_r16_of_all hostTab_table_r16 i hi hb
    · exact table_r16_of_all hostB_table_r16 i hi hb
    · exact table_r16_of_all ifc_table_r16 i hi hb
    · exact table_r16_of_all regA_table_r16 i hi hb
    · exact table_r16_of_all conv_table_r16 i hi hb
    · exact table_r16_of_all unreach_table_r16 i hi hb
    · exact table_r16_of_all rinit_table_r16 i hi hb

/-- **REG-A at index 27 of `wasmBaseM2rAir` satisfies the walk's interface.** -/
theorem regAt_m2r (nloc ngl : Nat) : RegAt (wasmBaseM2rAir nloc ngl) 27 where
  lt := by rw [m2r_air_len]; decide
  cons := fun e he => by
    rw [m2r_air_27]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ he))
  inters := fun i hi => by
    rw [m2r_air_27]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hi))
  r16only := m2r_recv_only_range16 nloc ngl

theorem regA_r16ok : R16Ok RegA.table :=
  ⟨[v Reg.act, v Reg.kind, v Reg.fresh, v RegW.wr, v Reg.rd, v RegC.clr], by decide +kernel,
    by decide +kernel⟩

theorem rinit_r16ok : R16Ok RInit.table := ⟨[v RInit.act], by decide +kernel, by decide +kernel⟩

/-- **The R16 send-side bound for `wasmBaseM2rAir`.** -/
theorem m2r_hsend_r16 {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2rAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub) :
    ∀ o ∈ occs (wasmBaseM2rAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1 :=
  hsend_r16_of_tail (tail := [HostR.table, HostO.table, HostTab.table, HostB.table, IfC.table,
      RegA.table, Conv.table, Unreach.table, RInit.table]) rfl
    (by
      intro T hT
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hT
      rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hostR_r16ok
      · exact hostO_r16ok
      · exact hostTab_r16ok
      · exact hostB_r16ok
      · exact ifc_r16ok
      · exact regA_r16ok
      · exact conv_r16ok
      · exact unreach_r16ok
      · exact rinit_r16ok)
    H hpub

/-- `gap < 2^16` on a REG-A byte row. -/
theorem m2r_reg_gap_lt {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2rAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r : Nat} (hr : r < tr.height 27) (hk : rowNat tr 27 r Reg.kind = 0) :
    rowNat tr 27 r Reg.gap < 65536 :=
  regG_gap_lt (regAt_m2r nloc ngl) H (m2r_hsend_r16 H hpub) hr hk

/-- `pos < len` on a REG-A byte row. -/
theorem m2r_reg_pos_lt_len {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2rAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r : Nat} (hr : r < tr.height 27) (hk : rowNat tr 27 r Reg.kind = 0) :
    rowNat tr 27 r Reg.pos < rowNat tr 27 r Reg.blen :=
  regG_pos_lt_len (regAt_m2r nloc ngl) H hr hk (m2r_reg_gap_lt H hpub hr hk)

/-- **`regLenAgree_groupG` at REG-A of `wasmBaseM2rAir`, without `hsend`.** -/
theorem m2r_regLenAgree_group {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2rAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r0 : Nat} (hr0 : r0 < tr.height 27)
    (hf : rowNat tr 27 r0 Reg.f = 1) (hk : rowNat tr 27 r0 Reg.kind = 0)
    (hrid0 : rowNat tr 27 r0 Reg.rid ≤ 99) (hpos0 : rowNat tr 27 r0 Reg.pos < 16777216)
    (hactL' : ∀ n, n ≤ rowNat tr 27 r0 Reg.blen → r0 + n < tr.height 27 →
      rowNat tr 27 (r0 + n) Reg.kind = 1 → rowNat tr 27 (r0 + n) Reg.act = 1) :
    let L := rowNat tr 27 r0 Reg.blen
    r0 + L < tr.height 27 ∧
      rowNat tr 27 (r0 + L) Reg.kind = 1 ∧
      rowProd Reg.table tr pub 27 (r0 + L) =
        [Register.lenMsg (rowNat tr 27 r0 Reg.rid) L (rowNat tr 27 r0 Reg.ts)] ∧
      (∀ i, i < L → rowProd Reg.table tr pub 27 (r0 + i) =
        [Register.byteMsg (rowNat tr 27 r0 Reg.rid) i (rowNat tr 27 (r0 + i) Reg.bv)
          (rowNat tr 27 r0 Reg.ts)]) :=
  regLenAgree_groupG (regAt_m2r nloc ngl) H (m2r_hsend_r16 H hpub) hr0 hf hk hrid0 hpos0 hactL'

/-! ## The absent message -/

/-- The absent message of register `rid` produced at time `tp`, as field elements:
`[6, rid·2^24, 3, 0, 0, 0, 0, tp]`. -/
def absentF (rid tp : Nat) : List F :=
  [((Register.space : Nat) : F), ((rid : Nat) : F) * ((Register.cap : Nat) : F),
   ((RegA.absentTag : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F),
   ((tp : Nat) : F)]

/-- An interaction of table `t` whose count is 1 on row `r` is an occurrence with count 1. -/
theorem occ_of_inter {A : Air} {pub : List F} {tr : Trace} {t : Nat} (ht : t < A.tables.length)
    {r : Nat} (hr : r < tr.height t) {i : Inter} (hi : i ∈ (A.tables[t]'ht).inters)
    (hc : (i.count.eval (tr.row pub t r)).toNat = 1) :
    (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), 1) ∈ occs A tr pub :=
  mem_occs.mpr ⟨t, ht, r, hr, i, hi, by rw [hc]⟩

theorem regA_absent_recv :
    chRecv (Expr.c Register.space) Reg.lenSlotE (Expr.c RegA.absentTag) [0, 0, 0, 0] (v RegA.atp)
      RegA.fcnt ∈ RegA.table.inters := by
  simp [RegA.table, RegA.inters, RegA.newInters]

theorem regA_absent_send :
    chSend (Expr.c Register.space) Reg.lenSlotE (Expr.c RegA.absentTag) [0, 0, 0, 0] (v Reg.ts)
      RegA.ccnt ∈ RegA.table.inters := by
  simp [RegA.table, RegA.inters, RegA.newInters]

theorem regA_atp_r16a :
    r16 (v Reg.ts - v RegA.atp - 65536 * v RegA.ahp) RegA.fcnt ∈ RegA.table.inters := by
  simp [RegA.table, RegA.inters, RegA.newInters]

theorem regA_atp_r16b : r16 (4 * v RegA.ahp) RegA.fcnt ∈ RegA.table.inters := by
  simp [RegA.table, RegA.inters, RegA.newInters]

theorem m2r_27_lt (nloc ngl : Nat) : 27 < (wasmBaseM2rAir nloc ngl).tables.length := by
  rw [m2r_air_len]; decide

theorem m2r_30_lt (nloc ngl : Nat) : 30 < (wasmBaseM2rAir nloc ngl).tables.length := by
  rw [m2r_air_len]; decide

/-- The absent message, evaluated on a REG-A row. -/
theorem regA_absent_msg_eval (tr : Trace) (pub : List F) (r : Nat) (tcol : Nat) :
    ([Expr.c Register.space, Reg.lenSlotE, Expr.c RegA.absentTag] ++ [0, 0, 0, 0] ++ [v tcol]).map
      (fun e : Expr => e.eval (tr.row pub 27 r)) =
      absentF (rowNat tr 27 r Reg.rid) (rowNat tr 27 r tcol) := by
  simp only [absentF, Reg.lenSlotE, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Expr.eval_c, Expr.eval_mul', Expr.eval_ofNat', col_eval_nat]

/-- **A fill length row consumes the absent message of its register.**  On an active length row
(`kind = 1`) of a fill group (`rd = 0`), the absent message `[6, rid·2^24, 3, 0,0,0,0, atp]` is
received on the CH bus with count 1. -/
theorem m2r_fill_consumes_absent {nloc ngl : Nat} {pub : List F} {tr : Trace}
    {r : Nat} (hr : r < tr.height 27)
    (ha : rowNat tr 27 r Reg.act = 1) (hk : rowNat tr 27 r Reg.kind = 1)
    (hrd : rowNat tr 27 r Reg.rd = 0) :
    (busStk, false, absentF (rowNat tr 27 r Reg.rid) (rowNat tr 27 r RegA.atp), 1) ∈
      occs (wasmBaseM2rAir nloc ngl) tr pub := by
  have hc : (RegA.fcnt.eval (tr.row pub 27 r)).toNat = 1 := by
    simp only [RegA.fcnt, Reg.isL, Reg.fill, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat',
      col_eval_nat, ha, hk, hrd]
    decide
  have h := occ_of_inter (m2r_27_lt nloc ngl) hr
    (by rw [m2r_air_27]; exact regA_absent_recv) hc
  simpa only [chRecv, regA_absent_msg_eval] using h

/-- **A clear length row re-produces the absent message of its register at its `ts`.** -/
theorem m2r_clear_produces_absent {nloc ngl : Nat} {pub : List F} {tr : Trace}
    {r : Nat} (hr : r < tr.height 27)
    (ha : rowNat tr 27 r Reg.act = 1) (hk : rowNat tr 27 r Reg.kind = 1)
    (hc : rowNat tr 27 r RegC.clr = 1) :
    (busStk, true, absentF (rowNat tr 27 r Reg.rid) (rowNat tr 27 r Reg.ts), 1) ∈
      occs (wasmBaseM2rAir nloc ngl) tr pub := by
  have hc' : (RegA.ccnt.eval (tr.row pub 27 r)).toNat = 1 := by
    simp only [RegA.ccnt, Reg.isL, Expr.eval_mul', col_eval_nat, ha, hk, hc]
    decide
  have h := occ_of_inter (m2r_27_lt nloc ngl) hr
    (by rw [m2r_air_27]; exact regA_absent_send) hc'
  simpa only [chSend, regA_absent_msg_eval] using h

/-- **An active RINIT row produces the absent message of its id at time 0.** -/
theorem m2r_rinit_produces_absent {nloc ngl : Nat} {pub : List F} {tr : Trace}
    {r : Nat} (hr : r < tr.height 30) (ha : rowNat tr 30 r RInit.act = 1) :
    (busStk, true, absentF (rowNat tr 30 r RInit.rid) 0, 1) ∈
      occs (wasmBaseM2rAir nloc ngl) tr pub := by
  have hc : ((v RInit.act).eval (tr.row pub 30 r)).toNat = 1 := by
    rw [col_eval_nat, ha]; decide
  have hmem : chSend (Expr.c Register.space) (v RInit.rid * Expr.c Register.cap)
      (Expr.c RegA.absentTag) [0, 0, 0, 0] 0 (v RInit.act) ∈
      ((wasmBaseM2rAir nloc ngl).tables[30]'(m2r_30_lt nloc ngl)).inters := by
    rw [m2r_air_30]; simp [RInit.table, RInit.inters]
  have h := occ_of_inter (m2r_30_lt nloc ngl) hr hmem hc
  simpa only [chSend, absentF, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Expr.eval_c, Expr.eval_mul', Expr.eval_ofNat', col_eval_nat] using h

/-! ## R16 values on any table of `wasmBaseM2rAir` -/

/-- An R16 query of table `t` with count 1 is `< 2^16`. -/
theorem m2r_r16_lt {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2rAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {t : Nat} (ht : t < (wasmBaseM2rAir nloc ngl).tables.length) {r : Nat} (hr : r < tr.height t)
    {e c : Expr} (hi : r16 e c ∈ ((wasmBaseM2rAir nloc ngl).tables[t]'ht).inters)
    (hc : (c.eval (tr.row pub t r)).toNat = 1) :
    (e.eval (tr.row pub t r)).toNat < 65536 := by
  have hocc := occ_of_inter ht hr hi hc
  obtain ⟨x, hx, hxl⟩ := lookup_r16G H (m2r_hsend_r16 H hpub)
    (regG_r16_recv (regAt_m2r nloc ngl) H) hocc rfl rfl rfl
  simp only [r16, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hx
  rw [hx]; exact hxl

/-- The algebraic step of `atp ≤ ts` (the non-strict sibling of `regw_time_lt`). -/
theorem time_le_of_r16 {ts tp hp x y : Nat} (hts : ts < 2 ^ 29) (htp : tp < 2 ^ 29)
    (hx : x < 65536) (hy : y < 65536)
    (h1 : ((x : Nat) : F) = ((ts : Nat) : F) - ((tp : Nat) : F) -
      ((65536 : Nat) : F) * ((hp : Nat) : F))
    (h2 : ((y : Nat) : F) = ((4 : Nat) : F) * ((hp : Nat) : F)) :
    tp ≤ ts := by
  have e : ((tp + (x + 16384 * y) : Nat) : F) = ((ts : Nat) : F) := by
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
    rw [h1, h2]
    have : ((65536 : Nat) : F) = ((16384 : Nat) : F) * ((4 : Nat) : F) := by
      rw [← Lean.Grind.Semiring.natCast_mul]
    rw [this]; grind
  have := congrArg Fp.toNat e
  have hP := P_val
  rw [Fp.toNat_cast, Fp.toNat_cast_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- **The absent message a fill consumes was produced no later than the fill** (`atp ≤ ts`), for
times below `2^29`. -/
theorem m2r_fill_absent_time {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2rAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r : Nat} (hr : r < tr.height 27)
    (ha : rowNat tr 27 r Reg.act = 1) (hk : rowNat tr 27 r Reg.kind = 1)
    (hrd : rowNat tr 27 r Reg.rd = 0)
    (hts : rowNat tr 27 r Reg.ts < 2 ^ 29) (hatp : rowNat tr 27 r RegA.atp < 2 ^ 29) :
    rowNat tr 27 r RegA.atp ≤ rowNat tr 27 r Reg.ts := by
  have hc : (RegA.fcnt.eval (tr.row pub 27 r)).toNat = 1 := by
    simp only [RegA.fcnt, Reg.isL, Reg.fill, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat',
      col_eval_nat, ha, hk, hrd]
    decide
  have hx := m2r_r16_lt H hpub (m2r_27_lt nloc ngl) hr
    (by rw [m2r_air_27]; exact regA_atp_r16a) hc
  have hy := m2r_r16_lt H hpub (m2r_27_lt nloc ngl) hr
    (by rw [m2r_air_27]; exact regA_atp_r16b) hc
  refine time_le_of_r16 (hp := rowNat tr 27 r RegA.ahp) hts hatp hx hy ?_ ?_
  · rw [Fp.cast_toNat]
    simp only [Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval_col,
      Trace.row, cell_cast]
  · rw [Fp.cast_toNat]
    simp only [Chips.v, Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, Trace.row, cell_cast]

/-! ## `cLenAct` -/

/-- **A group's length row after a byte row of the same group is active.** -/
theorem m2r_lenAct {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2rAir nloc ngl) pub tr) {r : Nat} (hr : r + 1 < tr.height 27)
    (hf : rowNat tr 27 (r + 1) Reg.f = 0) (hk : rowNat tr 27 (r + 1) Reg.kind = 1) :
    rowNat tr 27 (r + 1) Reg.act = 1 := by
  have h := H.constr 27 (m2r_27_lt nloc ngl) r (by omega) RegA.cLenAct
    (by rw [m2r_air_27]; simp [RegA.table, RegA.constraints, RegA.newConstraints])
  simp only [RegA.cLenAct, Chips.nv, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat',
    Expr.eval_nxt, Trace.row, Nat.mod_eq_of_lt hr, cell_cast, hf, hk] at h
  have hb := regG_act_bit (regAt_m2r nloc ngl) H hr
  rcases hb with hb | hb
  · rw [hb] at h
    exact absurd h (by decide)
  · exact hb

/-! ## RINIT: distinct, sorted ids -/

theorem rinit_constr {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2rAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 30) :
    ∀ e ∈ RInit.table.constraints, e.eval (tr.row pub 30 r) = 0 := by
  intro e he
  exact H.constr 30 (m2r_30_lt nloc ngl) r hr e (by rw [m2r_air_30]; exact he)

theorem rinit_mem_inter {nloc ngl : Nat} {i : Inter} (hi : i ∈ RInit.table.inters) :
    i ∈ ((wasmBaseM2rAir nloc ngl).tables[30]'(m2r_30_lt nloc ngl)).inters := by
  rw [m2r_air_30]; exact hi

/-- `act` is a bit on a RINIT row. -/
theorem m2r_rinit_act_bit {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2rAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 30) :
    rowNat tr 30 r RInit.act = 0 ∨ rowNat tr 30 r RInit.act = 1 := by
  have h := rinit_constr H hr RInit.cAct (by simp [RInit.table, RInit.constraints])
  simp only [RInit.cAct, Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', Trace.row, cell_cast] at h
  exact bool_nat (rowNat_lt tr 30 r RInit.act) h

/-- **RINIT's active rows form a prefix.** -/
theorem m2r_rinit_prefix {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2rAir nloc ngl) pub tr) {r : Nat} (hr : r + 1 < tr.height 30)
    (ha : rowNat tr 30 (r + 1) RInit.act = 1) : rowNat tr 30 r RInit.act = 1 := by
  have h := rinit_constr H (r := r) (by omega) RInit.cPrefix
    (by simp [RInit.table, RInit.constraints])
  have hlast : (r + 1 == tr.height 30) = false := by simp; omega
  simp only [RInit.cPrefix, Chips.v, Chips.nv, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat',
    Expr.eval_col, Expr.eval_nxt, Expr.eval, Trace.row, hlast, Nat.mod_eq_of_lt hr, cell_cast, ha,
    Bool.false_eq_true, ite_false] at h
  rcases m2r_rinit_act_bit H (r := r) (by omega) with hb | hb
  · rw [hb] at h
    exact absurd h (by decide)
  · exact hb

/-- An active RINIT row's id is `< 2^16`. -/
theorem m2r_rinit_rid_lt {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2rAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r : Nat} (hr : r < tr.height 30) (ha : rowNat tr 30 r RInit.act = 1) :
    rowNat tr 30 r RInit.rid < 65536 := by
  have hc : ((v RInit.act).eval (tr.row pub 30 r)).toNat = 1 := by rw [col_eval_nat, ha]; decide
  have h := m2r_r16_lt H hpub (m2r_30_lt nloc ngl) hr
    (rinit_mem_inter (i := r16 (v RInit.rid) (v RInit.act)) (by simp [RInit.table, RInit.inters])) hc
  rwa [col_eval_nat, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)] at h

/-- An active RINIT row's gap is `< 2^16`. -/
theorem m2r_rinit_gap_lt {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2rAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r : Nat} (hr : r < tr.height 30) (ha : rowNat tr 30 r RInit.act = 1) :
    rowNat tr 30 r RInit.gap < 65536 := by
  have hc : ((v RInit.act).eval (tr.row pub 30 r)).toNat = 1 := by rw [col_eval_nat, ha]; decide
  have h := m2r_r16_lt H hpub (m2r_30_lt nloc ngl) hr
    (rinit_mem_inter (i := r16 (v RInit.gap) (v RInit.act)) (by simp [RInit.table, RInit.inters])) hc
  rwa [col_eval_nat, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)] at h

/-- **One RINIT step**: between consecutive active rows, `rid' = rid + 1 + gap'` in the naturals. -/
theorem m2r_rinit_step {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2rAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r : Nat} (hr : r + 1 < tr.height 30) (ha : rowNat tr 30 (r + 1) RInit.act = 1) :
    rowNat tr 30 (r + 1) RInit.rid =
      rowNat tr 30 r RInit.rid + 1 + rowNat tr 30 (r + 1) RInit.gap := by
  have ha0 := m2r_rinit_prefix H hr ha
  have h := rinit_constr H (r := r) (by omega) RInit.cInc
    (by simp [RInit.table, RInit.constraints])
  have hlast : (r + 1 == tr.height 30) = false := by simp; omega
  simp only [RInit.cInc, Chips.v, Chips.nv, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat',
    Expr.eval_col, Expr.eval_nxt, Expr.eval, Trace.row, hlast, Nat.mod_eq_of_lt hr, cell_cast, ha,
    Bool.false_eq_true, ite_false] at h
  have h0 := m2r_rinit_rid_lt H hpub (r := r) (by omega) ha0
  have h1 := m2r_rinit_rid_lt H hpub hr ha
  have hg := m2r_rinit_gap_lt H hpub hr ha
  have hP := P_val
  have e : ((rowNat tr 30 (r + 1) RInit.rid : Nat) : F) =
      ((rowNat tr 30 r RInit.rid + 1 + rowNat tr 30 (r + 1) RInit.gap : Nat) : F) := by
    simp only [Lean.Grind.Semiring.natCast_add, cast_one]
    grind
  exact natEq e (rowNat_lt _ _ _ _) (by omega)

/-- **RINIT's active ids are strictly increasing.** -/
theorem m2r_rinit_strict {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2rAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub) :
    ∀ r d, r + d + 1 < tr.height 30 → rowNat tr 30 (r + d + 1) RInit.act = 1 →
      rowNat tr 30 r RInit.rid < rowNat tr 30 (r + d + 1) RInit.rid := by
  intro r d
  induction d with
  | zero =>
    intro hr ha
    simp only [Nat.add_zero] at hr ha ⊢
    have := m2r_rinit_step H hpub hr ha
    omega
  | succ d ih =>
    intro hr ha
    have hs := m2r_rinit_step H hpub (r := r + d + 1) (by omega) (by simpa [Nat.add_assoc] using ha)
    have ha' := m2r_rinit_prefix H (r := r + d + 1) (by omega) (by simpa [Nat.add_assoc] using ha)
    have := ih (by omega) ha'
    rw [show r + (d + 1) + 1 = r + d + 1 + 1 by omega]
    omega

/-- **RINIT's active rows carry distinct ids**: at most one absent message per register id is
produced at the start. -/
theorem m2r_rinit_distinct {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2rAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r r' : Nat} (hr : r < tr.height 30) (hr' : r' < tr.height 30)
    (ha : rowNat tr 30 r RInit.act = 1) (ha' : rowNat tr 30 r' RInit.act = 1)
    (hne : r ≠ r') : rowNat tr 30 r RInit.rid ≠ rowNat tr 30 r' RInit.rid := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := m2r_rinit_strict H hpub r (r' - r - 1) (by omega)
      (by rw [show r + (r' - r - 1) + 1 = r' by omega]; exact ha')
    rw [show r + (r' - r - 1) + 1 = r' by omega] at this
    omega
  · have := m2r_rinit_strict H hpub r' (r - r' - 1) (by omega)
      (by rw [show r' + (r - r' - 1) + 1 = r by omega]; exact ha)
    rw [show r' + (r - r' - 1) + 1 = r by omega] at this
    omega

end WasmBase

#print axioms WasmBase.m2r_hsend_r16
#print axioms WasmBase.m2r_regLenAgree_group
#print axioms WasmBase.m2r_fill_consumes_absent
#print axioms WasmBase.m2r_fill_absent_time
#print axioms WasmBase.m2r_clear_produces_absent
#print axioms WasmBase.m2r_rinit_produces_absent
#print axioms WasmBase.m2r_lenAct
#print axioms WasmBase.m2r_rinit_distinct
