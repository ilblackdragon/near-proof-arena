import WasmBase.M3Ctx
import WasmBase.Main.SegGrowRow
import WasmBase.Main.SegRowsX
/-!
# WasmBase.Main.SegGrowFetch — CODE binding to the M3 records and a MEMG row's FETCH pin (E2E M6, GROW2)

On `wasmBaseSegAirG` the CODE table (17) carries the **M3** records (`checkModuleM3`): MEMG (32)
fetches `[pc, 0x40, h, fee, lin, 0, 0, 0]` / `[pc, 0x3F, h, fee, 0, 0, 0, 0]`.  Here:

* `codeRec3` / `CodeOK3 X tr` — the statement binding of the CODE table to `X : M3Ctx`'s records
  (`CodeOK` with the M3 records);
* `segG_recv_fetch` (only CODE receives on FETCH), `segG_hsend_fetch` (every FETCH send count of the
  grow AIR is `≤ 1`: the chips 1–13 and RET by their row facts, MEMG by `bool act`, the rest by the
  decidable `SendsOkB`), and **`segG_fetch3`**: FETCH lookup soundness against the M3 records;
* **`memg_fetch_grow` / `memg_fetch_size`**: an active MEMG grow (size) row's FETCH answer pins a
  checked function `k` and local pc `l` whose instruction is `memory.grow` (`memory.size`), with
  `growFee`'s fee and linear flag (`feeUnits`' fee) equal to the row's `fee`/`lin` cells and the row's
  `h` cell the static height `heights[l]` — all from `checkModuleM3` (`M3Ctx.recG_memGrow` /
  `recG_memSize`).
-/
namespace WasmBase
open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- CODE record `j` of an M3 module, as field elements. -/
def codeRec3 (X : M3Ctx) (j : Nat) : List F := (X.M.records[j]?.getD []).map fun x => ((x : Nat) : F)

/-- **Statement binding of the cached CODE table to the M3 records** (`CodeOK` for `checkModuleM3`). -/
def CodeOK3 (X : M3Ctx) (tr : Trace) : Prop :=
  ∀ r, r < tr.height 17 → ∃ j, j < X.M.codeSize ∧
    (List.range Boundary.recWidth).map (fun k => tr.cell 17 r k) = codeRec3 X j

theorem segG_recv_fetch (nloc ngl : Nat) : RecvOnly (wasmBaseSegAirG nloc ngl) busFetch 17 := by
  have e : wasmBaseSegAirG nloc ngl = wasmBaseSegAirG 0 0 := rfl
  rw [e]; exact recvOnly_of_all (by decide +kernel)

theorem segG_t17 (nloc ngl : Nat) :
    (wasmBaseSegAirG nloc ngl).tables[17]'(segG_lt nloc ngl 17 (by decide)) = Code.table := rfl

/-- The decidable FETCH send check holds for every grow-AIR table except the chips 1–14 and MEMG. -/
theorem segG_sendsOkF (nloc ngl : Nat) :
    ∀ t (ht : t < (wasmBaseSegAirG nloc ngl).tables.length), ¬ (1 ≤ t ∧ t ≤ 14) → t ≠ 32 →
      SegSha.SendsOkB busFetch ((wasmBaseSegAirG nloc ngl).tables[t]'ht) = true := by
  have e : (wasmBaseSegAirG nloc ngl).tables = (wasmBaseSegAirG 0 0).tables := rfl
  have h0 : ∀ t (ht : t < (wasmBaseSegAirG 0 0).tables.length), ¬ (1 ≤ t ∧ t ≤ 14) → t ≠ 32 →
      SegSha.SendsOkB busFetch ((wasmBaseSegAirG 0 0).tables[t]'ht) = true := by
    decide +kernel
  simp only [e]; exact h0

/-- MEMG's only FETCH send has count `act`. -/
theorem memg_fetch_count : MemG.table.inters.all
    (fun i => decide (i.bus ≠ busFetch) || !i.send || decide (i.count = MemG.act)) = true := by
  decide +kernel

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirG nloc ngl) pub tr)
include H

/-- MEMG's `act` is a bit. -/
theorem memg_act_le {r : Nat} (hr : r < tr.height 32) : (MemG.act.eval (tr.row pub 32 r)).toNat ≤ 1 := by
  have hb := H.constr 32 (segG_lt nloc ngl 32 (by decide)) r hr (bool MemG.act)
    (by rw [segG_t32']; simp [MemG.table, MemG.constraints])
  simp only [Chips.bool, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat'] at hb
  rcases bool_cases hb with h | h <;> rw [h] <;> decide

/-- **The FETCH send bound of `wasmBaseSegAirG`.** -/
theorem segG_hsend_fetch :
    ∀ o ∈ occs (wasmBaseSegAirG nloc ngl) tr pub, o.1 = busFetch → o.2.1 = true → o.2.2.2 ≤ 1 := by
  intro o ho hbo hs
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hbo hs ⊢
  have ht36 : t < 36 := by rw [segG_len] at ht; exact ht
  by_cases hc : 1 ≤ t ∧ t ≤ 13
  · have hT := segG_chipT nloc ngl t hc.1 hc.2
    have hcon := table_constr_eqX H ht (chipT t) hT hr
    rw [hT] at hi
    obtain ⟨h1, h13⟩ := hc
    rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨
      t = 11 ∨ t = 12 ∨ t = 13 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact add_counts_of hcon i hi
    · exact bit_counts_of hcon i hi
    · exact mul_counts_of hcon i hi
    · exact shift_counts_of hcon i hi
    · exact cmp_counts_of hcon i hi
    · exact const_counts_of hcon i hi
    · exact stack_counts_of hcon i hi
    · exact ctrl_counts_of hcon i hi
    · exact local_counts_of hcon i hi
    · exact div_counts_of hcon i hi
    · exact load_counts_of hcon i hi
    · exact store_counts_of hcon i hi
    · exact call_counts_of hcon i hi
  by_cases h14 : t = 14
  · subst h14
    have hcon : ∀ e ∈ Ret.table.constraints, e.eval (Local.natRow (rowNat tr 14 r) (tr.row pub 14 r)) = 0 :=
      table_constr_eqX H ht RetT.table (segG_t14' nloc ngl) hr
    rw [segG_t14'] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ret_counts_of hcon i hi
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      subst hi; exact absurd hbo (by decide)
  by_cases h32 : t = 32
  · subst h32
    rw [segG_t32'] at hi
    have hc := List.all_eq_true.mp memg_fetch_count i hi
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
    rcases hc with (hc | hc) | hc
    · exact absurd hbo hc
    · rw [hs] at hc; exact absurd hc (by decide)
    · rw [hc]; exact memg_act_le H hr
  · exact SegSha.le_of_sendsOkB H.toC ht (segG_sendsOkF nloc ngl t ht (by omega) h32) hr hi hbo hs

/-- **FETCH lookup soundness on the grow AIR, against the M3 records.** -/
theorem segG_fetch3 (X : M3Ctx) (hcode : CodeOK3 X tr) {o : Occ}
    (ho : o ∈ occs (wasmBaseSegAirG nloc ngl) tr pub)
    (hb : o.1 = busFetch) (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ j, j < X.M.codeSize ∧ o.2.2.1 = codeRec3 X j := by
  refine lookup_soundX H busFetch (by decide) (fun m => ∃ j, j < X.M.codeSize ∧ m = codeRec3 X j) ?_
    (segG_hsend_fetch H) ho hb hs hc
  intro o' ho' hb' hs' _
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho'
  simp only at hb' hs' ⊢
  by_cases h17 : t = 17
  · subst h17
    rw [segG_t17] at hi
    simp only [Code.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst hi
    obtain ⟨j, hj, he⟩ := hcode r hr
    refine ⟨j, hj, ?_⟩
    rw [← he]
    simp [List.map_map, Function.comp, v, Expr.eval_col, Trace.row, Boundary.recWidth]
  · exact absurd (segG_recv_fetch nloc ngl t ht h17 i hi hb') (by simp [hs'])

end

/-! ## A MEMG row's FETCH pin -/

theorem list8_cast {a b c d e f g h : Nat} {L : List Nat}
    (heq : [((a : Nat) : F), ((b : Nat) : F), ((c : Nat) : F), ((d : Nat) : F), ((e : Nat) : F),
      ((f : Nat) : F), ((g : Nat) : F), ((h : Nat) : F)] = L.map fun x => ((x : Nat) : F)) :
    ∃ a' b' c' d' e' f' g' h', L = [a', b', c', d', e', f', g', h'] ∧
      ((a : Nat) : F) = a' ∧ ((b : Nat) : F) = b' ∧ ((c : Nat) : F) = c' ∧ ((d : Nat) : F) = d' ∧
      ((e : Nat) : F) = e' := by
  rcases L with _ | ⟨a', _ | ⟨b', _ | ⟨c', _ | ⟨d', _ | ⟨e', _ | ⟨f', _ | ⟨g', _ | ⟨h', _ | ⟨i', L⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, reduceCtorEq, and_false, false_and] at heq
  exact ⟨a', b', c', d', e', f', g', h', rfl, heq.1, heq.2.1, heq.2.2.1, heq.2.2.2.1, heq.2.2.2.2.1⟩

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirG nloc ngl) pub tr)
include H

omit H in
/-- The FETCH occurrence of an active MEMG row. -/
theorem memg_fetch_occ {r : Nat} (hr : r < tr.height 32) (ha : (MemG.act.eval (tr.row pub 32 r)).toNat = 1) :
    (busFetch, true, [((mgc tr r cPc : Nat) : F), MemG.op.eval (tr.row pub 32 r), ((mgc tr r cH : Nat) : F),
      ((mgc tr r cFee : Nat) : F), ((mgc tr r MemG.lin : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F),
      ((0 : Nat) : F)], 1) ∈ occs (wasmBaseSegAirG nloc ngl) tr pub := by
  have h := row_occ (pub := pub) (segG_lt nloc ngl 32 (by decide)) hr
    (i := fetch (v cPc) MemG.op (v cH) (v cFee) [v MemG.lin, 0, 0, 0] MemG.act)
    (by rw [segG_t32']; simp [MemG.table, MemG.inters])
  simp only [fetch, List.cons_append, List.nil_append, List.map_cons, List.map_nil, memg_col_eval,
    Expr.eval_ofNat', ha] at h
  exact h

end

/-- `growFee`'s fee is 16-bit and its linear flag a bit. -/
theorem growFee_lt {cfg : NearCfg} {g : Option (Option (IK × Fee))} {fee lin : Nat}
    (h : growFee cfg g = some (fee, lin)) : fee < 2 ^ 16 ∧ lin ≤ 1 := by
  unfold growFee at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
  · split at h
    · rename_i hc
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
        · simp at h
    · simp at h
  · simp at h

/-- Every `recordAtM3` opcode is below `0x243`. -/
theorem recordAtM3_op_lt {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)}
    {H : Array Nat} {off pc : Nat} {cinfo : Nat → Option Nat} {rec : List Nat}
    (hr : recordAtM3 cfg p pf L H off cinfo pc = some rec) : rec.getD 1 0 < 0x243 := by
  unfold recordAtM3 at hr
  split at hr
  · cases hg : growFee cfg pf.gas[pc]? with
    | none => simp [hg] at hr
    | some fl =>
      simp only [hg, Option.map_some, Option.some.injEq] at hr
      subst hr; simp [opMemGrow]
  · cases hf : feeUnits cfg pf.gas[pc]? with
    | none => simp [hf] at hr
    | some fee =>
      simp only [hf, Option.map_some, Option.some.injEq] at hr
      subst hr; simp [opMemSize]
  · split at hr
    · split at hr
      · simp only [Option.some.injEq] at hr; subst hr; simp [opHost]
      · exact recordAtM2_op_lt hr
    · exact recordAtM2_op_lt hr
  · exact recordAtM2_op_lt hr

/-- Every global M3 record has the 8-field shape with an opcode below `0x243`. -/
theorem M3Ctx.recOp {X : M3Ctx} {j : Nat} (hj : j < X.M.codeSize) :
    (X.M.records[j]?.getD []).getD 1 0 < 0x243 := by
  obtain ⟨k, l, hk, hl, -, hrj⟩ := X.recG hj
  have hr := X.rec_at hk hl
  have hsz : l < (X.ckOf k).records.size := by rw [(X.factsOf hk).records]; exact hl
  rw [Array.getElem?_eq_getElem hsz] at hr hrj
  rw [hrj, Option.getD_some]
  exact recordAtM3_op_lt hr

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirG nloc ngl) pub tr)
include H

/-- The common part of the two FETCH pins: the fetched global record and the row's cells. -/
theorem memg_fetch_rec (X : M3Ctx) (hcode : CodeOK3 X tr) {r : Nat} (hr : r < tr.height 32)
    (ha : (MemG.act.eval (tr.row pub 32 r)).toNat = 1) {opN : Nat} (hopN : opN < 0x243)
    (hop : MemG.op.eval (tr.row pub 32 r) = ((opN : Nat) : F)) :
    ∃ j a c d e f g h, j < X.M.codeSize ∧ X.M.records[j]? = some [a, opN, c, d, e, f, g, h] ∧
      ((mgc tr r cPc : Nat) : F) = (a : F) ∧ ((mgc tr r cH : Nat) : F) = (c : F) ∧
      ((mgc tr r cFee : Nat) : F) = (d : F) ∧ ((mgc tr r MemG.lin : Nat) : F) = (e : F) := by
  have hP := P_val
  have ho := memg_fetch_occ (nloc := nloc) (ngl := ngl) hr ha
  rw [hop] at ho
  obtain ⟨j, hj, hm⟩ := segG_fetch3 H X hcode ho rfl rfl rfl
  simp only [codeRec3] at hm
  obtain ⟨a', b', c', d', e', f', g', h', hL, e0, e1, e2, e3, e4⟩ := list8_cast hm
  have hopl := X.recOp hj
  rw [hL] at hopl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hopl
  have hb : opN = b' := natEq e1 (by omega) (by omega)
  subst hb
  have hrs : X.M.records[j]? = some [a', opN, c', d', e', f', g', h'] := by
    have hsz : j < X.M.records.size := by have := X.mf.recSize; unfold M3Ctx.M at hj ⊢; omega
    rw [Array.getElem?_eq_getElem hsz] at hL ⊢
    simp only [Option.getD_some] at hL
    rw [hL]
  exact ⟨j, a', c', d', e', f', g', h', hj, hrs, e0, e2, e3, e4⟩

/-- **The FETCH pin of an active `memory.grow` row**: the row's pc cell is the global pc of a
`memory.grow` of a checked function, its `fee`/`lin` cells are `growFee`'s reading of the gas entry,
its `h` cell the static height. -/
theorem memg_fetch_grow (X : M3Ctx) (hcode : CodeOK3 X tr) {r : Nat} (hr : r < tr.height 32)
    (hg : mgc tr r MemG.fGrow = 1) (hs : mgc tr r MemG.fSize = 0) :
    ∃ k l fee lin, k < X.nf ∧ l < (X.pfOf k).code.size ∧ X.offOf k + l = mgc tr r cPc ∧
      (X.pfOf k).code[l]? = some .memGrow ∧ growFee X.cfg (X.pfOf k).gas[l]? = some (fee, lin) ∧
      mgc tr r cFee = fee ∧ mgc tr r MemG.lin = lin ∧ mgc tr r cH = (X.ckOf k).heights[l]?.getD 0 := by
  have hP := P_val
  have hPr := rowNat_lt tr 32 r
  have ha : (MemG.act.eval (tr.row pub 32 r)).toNat = 1 := segG_memg_act_cnt H hr hg
  have hop : MemG.op.eval (tr.row pub 32 r) = ((opMemGrow : Nat) : F) := by
    simp only [MemG.op, Expr.eval_add', Expr.eval_mul', Expr.eval_c, memg_col_eval, hg, hs]
    grind
  obtain ⟨j, a, c, d, e, f, g, h, hj, hrs, e0, e2, e3, e4⟩ :=
    memg_fetch_rec H X hcode hr ha (by simp [opMemGrow]) hop
  obtain ⟨k, l, fee, lin, hk, hl, hoff, hc, hgf, hrec⟩ := X.recG_memGrow hj (by rw [hrs]; rfl)
  rw [hrs, Option.some.injEq] at hrec
  simp only [List.cons.injEq] at hrec
  obtain ⟨ra, -, rc, rd, re, -⟩ := hrec
  rw [ra] at e0
  rw [rc] at e2
  rw [rd] at e3
  rw [re] at e4
  have hjl : j < 2 ^ 20 := Nat.lt_trans hj X.mf.total
  have hhb := (X.factsOf hk).hBound l hl
  have hfl := growFee_lt hgf
  refine ⟨k, l, fee, lin, hk, hl, (natEq e0 (hPr _) (by omega)).symm, hc, hgf, natEq e3 (hPr _) (by omega),
    natEq e4 (hPr _) (by omega), natEq e2 (hPr _) (by omega)⟩

/-- **The FETCH pin of an active `memory.size` row.** -/
theorem memg_fetch_size (X : M3Ctx) (hcode : CodeOK3 X tr) {r : Nat} (hr : r < tr.height 32)
    (hg : mgc tr r MemG.fGrow = 0) (hs : mgc tr r MemG.fSize = 1) :
    ∃ k l fee, k < X.nf ∧ l < (X.pfOf k).code.size ∧ X.offOf k + l = mgc tr r cPc ∧
      (X.pfOf k).code[l]? = some .memSize ∧ feeUnits X.cfg (X.pfOf k).gas[l]? = some fee ∧
      mgc tr r cFee = fee ∧ mgc tr r cH = (X.ckOf k).heights[l]?.getD 0 := by
  have hP := P_val
  have hPr := rowNat_lt tr 32 r
  have ha : (MemG.act.eval (tr.row pub 32 r)).toNat = 1 := by
    simp only [MemG.act, Expr.eval_add', memg_col_eval, hg, hs]; rfl
  have hop : MemG.op.eval (tr.row pub 32 r) = ((opMemSize : Nat) : F) := by
    simp only [MemG.op, Expr.eval_add', Expr.eval_mul', Expr.eval_c, memg_col_eval, hg, hs]
    grind
  obtain ⟨j, a, c, d, e, f, g, h, hj, hrs, e0, e2, e3, -⟩ :=
    memg_fetch_rec H X hcode hr ha (by simp [opMemSize]) hop
  obtain ⟨k, l, fee, hk, hl, hoff, hc, hfe, hrec⟩ := X.recG_memSize hj (by rw [hrs]; rfl)
  rw [hrs, Option.some.injEq] at hrec
  simp only [List.cons.injEq] at hrec
  obtain ⟨ra, -, rc, rd, -⟩ := hrec
  rw [ra] at e0
  rw [rc] at e2
  rw [rd] at e3
  have hjl : j < 2 ^ 20 := Nat.lt_trans hj X.mf.total
  have hhb := (X.factsOf hk).hBound l hl
  have hfl := feeUnits_lt hfe
  refine ⟨k, l, fee, hk, hl, (natEq e0 (hPr _) (by omega)).symm, hc, hfe, natEq e3 (hPr _) (by omega),
    natEq e2 (hPr _) (by omega)⟩

end

#print axioms segG_hsend_fetch
#print axioms segG_fetch3
#print axioms memg_fetch_grow
#print axioms memg_fetch_size

end WasmBase
