import WasmBase.Main.SegGrowFetch
import WasmBase.Main.SegExecQ
/-!
# WasmBase.Main.SegGrowMemg — a MEMG row's spec premise from the trace (E2E M6, GROW2)

The decoded MEMG row (table 32 of `wasmBaseSegAirG`) linked to the spec step, for an M3 module
`X : M3Ctx` and the semantic context `X.ctx := X.toM2.toCtx` (the M2 shadow: same `cfg`, `p`,
offsets, labels and heights, `M3Ctx.toM2_*`).  From `HoldsX (wasmBaseSegAirG …)` and `CodeOK3 X tr`:

* `memg_grow_at` / `memg_size_at`: at every related pre-state (`RelW X.ctx …` with the row's
  in-STATE), the row's FETCH pins `(E.k, pc)` (`memg_fetch_grow`/`_size`, `M3Ctx.loc_unique`), the
  successor facts (`M3Ctx.memGrow_succ`/`memSize_succ`), and the row's consumed stack message at slot
  `sb + h − 1` (the `h` cell is `heights[pc] = |stack| − sb`) is the stack top `.i32 w` with
  `w = n0 + 2^16·n1` (`RelW.stack_dec`); the consumed size message is `szMsg old tz`;
* **`memg_growOk_rowSpec`** / **`memg_growFail_rowSpec`** / **`memg_size_rowSpec`**: the
  `RowSpecSegJQ X.ctx J Q mf` premise of an active MEMG row, with `Q ⇒ SzC` (the size clause pins
  `old = pages`), via `step_memGrow_ok` / `step_memGrow_fail` / `step_memSize`.  A successful grow's
  productions are the row's own plus the zero bytes `zeroBytes A ts` of the addresses `A` handed to
  MEMBG (the fusion with MEMBG's rows is the action-list layer, open); the fee bound is the row's
  `fee + lin·n ≤ mf` (a hypothesis: on a failing grow `n` is only 27-bit, see the report);
* `memg_codeNonHost`: a MEMG row executes a non-host instruction (so `rowJKeep_sig` applies).
-/
namespace WasmBase
open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-! ## The semantic context of an M3 module -/

/-- The `Ctx` an M3 module's semantics runs in: its M2 shadow. -/
abbrev M3Ctx.ctx (X : M3Ctx) : Ctx := X.toM2.toCtx

theorem M3Ctx.ctx_offOf (X : M3Ctx) (k : Nat) : X.ctx.offOf k = X.offOf k := X.toM2_offOf k
theorem M3Ctx.ctx_pfOf (X : M3Ctx) (k : Nat) : X.ctx.pfOf k = X.pfOf k := X.toM2_pfOf k
theorem M3Ctx.ctx_nf (X : M3Ctx) : X.ctx.nf = X.nf := X.toM2_nf
theorem M3Ctx.ctx_labels (X : M3Ctx) (k : Nat) : (X.ctx.ckOf k).labels = (X.ckOf k).labels := (X.toM2_ck k).1
theorem M3Ctx.ctx_heights (X : M3Ctx) (k : Nat) : (X.ctx.ckOf k).heights = (X.ckOf k).heights :=
  (X.toM2_ck k).2.1
theorem M3Ctx.ctx_cfg (X : M3Ctx) : X.ctx.cfg = X.cfg := rfl
theorem M3Ctx.ctx_p (X : M3Ctx) : X.ctx.p = X.p := rfl

/-! ## MEMG's STATE messages -/

theorem memg_rowIn {tr : Trace} {pub : List F} {r : Nat} :
    rowIn MemG.table tr pub 32 r =
      [tr.cell 32 r cPc, tr.cell 32 r cTs, tr.cell 32 r cS, ((0 : Nat) : F), tr.cell 32 r MemG.kSb,
        tr.cell 32 r MemG.kCid] := by
  simp only [rowIn, MemG.table, MemG.inters, stateIn, List.cons_append, List.getD_cons_zero,
    List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', Trace.row]

theorem memg_nE_eval {tr : Trace} {pub : List F} {r : Nat} :
    MemG.nE.eval (tr.row pub 32 r) = ((mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1 : Nat) : F) := by
  simp only [MemG.nE, Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', memg_col_eval,
    Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]

theorem memg_rowOut {tr : Trace} {pub : List F} {r : Nat} :
    rowOut MemG.table tr pub 32 r =
      [tr.cell 32 r cPc + ((1 : Nat) : F), tr.cell 32 r cTs + ((1 : Nat) : F),
        tr.cell 32 r cS + tr.cell 32 r cFee + tr.cell 32 r MemG.lin * MemG.nE.eval (tr.row pub 32 r),
        ((0 : Nat) : F), tr.cell 32 r MemG.kSb, tr.cell 32 r MemG.kCid] := by
  simp only [rowOut, MemG.table, MemG.inters, stateOut, List.cons_append, List.getD_cons_succ,
    List.getD_cons_zero, List.map_cons, List.map_nil, Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat']
  simp only [v, Expr.eval_col, Trace.row]

/-! ## The pre-state facts of an active MEMG row -/

/-- The in-STATE of a MEMG row against a related pre-state: the row's pc cell is the global pc,
`kSb` the stack base, and `ts`, `S`, `kCid` the time, gas count and activation id (in the field). -/
theorem memg_in {X : M3Ctx} {tr : Trace} {pub : List F} {r : Nat} {E : Env} {s : St} {f : Frame}
    {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop} {a b : Nat}
    (R : RelW X.ctx E s f tps tpl t pc S live a b)
    (hin : rowIn MemG.table tr pub 32 r = stMsg (X.ctx.offOf E.k + pc) t S 0 E.sb E.cid) :
    mgc tr r cPc = X.offOf E.k + pc ∧ mgc tr r MemG.kSb = E.sb ∧ tr.cell 32 r cTs = ((t : Nat) : F) ∧
      tr.cell 32 r cS = ((S : Nat) : F) ∧ tr.cell 32 r MemG.kCid = ((E.cid : Nat) : F) := by
  have hP := P_val
  have hPr := rowNat_lt tr 32 r
  rw [memg_rowIn] at hin
  obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
  have hkE : E.k < X.nf := by have := R.kLt; rwa [M3Ctx.ctx_nf] at this
  have hpcE : pc < (X.pfOf E.k).code.size := by have := R.pcLt; rwa [M3Ctx.ctx_pfOf] at this
  have hoffb := X.off_bound hkE
  have htot := X.mf.total
  rw [M3Ctx.ctx_offOf] at i0
  rw [cell_cast] at i0 i4
  refine ⟨natEq i0 (hPr _) (by unfold M3Ctx.M at hoffb; omega), natEq i4 (hPr _) (by have := R.sbLt; omega),
    i1, i2, i5⟩

/-- A message of the stack top, decoded: tag 0 and limbs `n0, n1` make the top an `i32` `w` with
`w = n0 + 2^16·n1`. -/
theorem stack_top_i32 {v : Val} (hv : isNum v) {i tp n0 n1 tn : Nat}
    (h : enc 0 i v tp = ⟨0, i, 0, n0, n1, 0, 0, tn⟩) :
    ∃ w : UInt32, v = .i32 w ∧ w.toNat = n0 + 65536 * n1 := by
  cases v with
  | i32 w =>
    refine ⟨w, rfl, ?_⟩
    simp only [enc, vTag, vNum, Msg.mk.injEq] at h
    have := w.toNat_lt
    omega
  | i64 w => simp [enc, vTag] at h
  | _ => exact absurd hv (by simp [isNum])

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirG nloc ngl) pub tr)
include H

/-- **An active `memory.grow` row at a related pre-state**: everything `step_memGrow_ok` /
`step_memGrow_fail` take, read off the row. -/
theorem memg_grow_at (X : M3Ctx) (hcode : CodeOK3 X tr) {r : Nat} (hr : r < tr.height 32)
    (hg : mgc tr r MemG.fGrow = 1) (hs : mgc tr r MemG.fSize = 0)
    {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop} {a b : Nat}
    (R : RelW X.ctx E s f tps tpl t pc S live a b)
    (hin : rowIn MemG.table tr pub 32 r = stMsg (X.ctx.offOf E.k + pc) t S 0 E.sb E.cid)
    (hl : ∀ x ∈ rowCons MemG.table tr pub 32 r, live x) :
    ∃ w : UInt32, (X.ctx.pfOf E.k).code[pc]? = some .memGrow ∧
      growFee X.ctx.cfg (X.ctx.pfOf E.k).gas[pc]? = some (mgc tr r cFee, mgc tr r MemG.lin) ∧
      w.toNat = mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1 ∧
      E.sb + 1 ≤ s.stack.size ∧ s.stack[s.stack.size - 1]? = some (.i32 w) ∧
      pc + 1 < (X.ctx.pfOf E.k).code.size ∧
      (∃ ls, (X.ctx.ckOf E.k).labels[pc + 1]? = some ls ∧ f.labels = shiftLabels E.sb ls) ∧
      (X.ctx.ckOf E.k).heights[pc + 1]? = some (s.stack.size - E.sb) ∧
      mgc tr r MemG.kSb + mgc tr r cH = s.stack.size ∧
      rowCons MemG.table tr pub 32 r =
        [enc 0 (s.stack.size - 1) (.i32 w) (tps (s.stack.size - 1)), szMsg (mgc tr r MemG.old) (mgc tr r MemG.tz)] := by
  have hP := P_val
  have hPr := rowNat_lt tr 32 r
  obtain ⟨p0, psb, -, -, -⟩ := memg_in R hin
  obtain ⟨k, l, fee, lin, hk, hl', hoff, hc, hgf, hfee, hlin, hh⟩ := memg_fetch_grow H X hcode hr hg hs
  have hkE : E.k < X.nf := by have := R.kLt; rwa [M3Ctx.ctx_nf] at this
  have hpcE : pc < (X.pfOf E.k).code.size := by have := R.pcLt; rwa [M3Ctx.ctx_pfOf] at this
  obtain ⟨rfl, rfl⟩ := X.loc_unique hk hl' hkE hpcE (by rw [hoff, p0])
  obtain ⟨ls0, hL0, hfl0⟩ := R.labels
  have hH := R.height
  rw [M3Ctx.ctx_labels] at hL0
  rw [M3Ctx.ctx_heights] at hH
  obtain ⟨h1, hnext, hL1, hH1⟩ := X.memGrow_succ hkE hc hL0 hH
  have p3 : mgc tr r cH = s.stack.size - E.sb := by rw [hh, hH]; rfl
  have hsbR := R.sbLe
  have hszP : s.stack.size < P := by have := R.sbLt; have := (X.factsOf hkE).hBound _ hpcE; rw [hH] at this; simp at this; omega
  -- the consumed messages
  have hcons := (memg_grow_msgs (pub := pub) hg hs).1
  obtain ⟨mc, hmc_def⟩ : ∃ mc, mc = decMsg [((0 : Nat) : F),
      ((mgc tr r MemG.kSb : Nat) : F) + ((mgc tr r cH : Nat) : F) - 1, ((0 : Nat) : F),
      ((mgc tr r MemG.n0 : Nat) : F), ((mgc tr r MemG.n1 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F),
      ((mgc tr r MemG.tn : Nat) : F)] := ⟨_, rfl⟩
  rw [← hmc_def] at hcons
  have hmc : live mc := hl mc (by rw [hcons]; simp)
  have ms : mc.space = 0 := by simp only [hmc_def, decMsg, List.getD_cons_zero]; rfl
  have msl : mc.slot = s.stack.size - 1 := by
    simp only [hmc_def, decMsg, List.getD_cons_succ, List.getD_cons_zero]
    exact slot_toNat (k := 1) psb p3 hsbR (by omega) hszP
  obtain ⟨ea, -, -, -⟩ := R.stack_dec hmc ms msl (by omega)
  have hnum := R.numS (s.stack.size - 1) (by omega)
  have hmc' : mc = ⟨0, s.stack.size - 1, 0, mgc tr r MemG.n0, mgc tr r MemG.n1, 0, 0, mgc tr r MemG.tn⟩ := by
    rw [hmc_def]
    simp only [decMsg, List.getD_cons_succ, List.getD_cons_zero]
    rw [← msl, hmc_def]
    simp only [decMsg, List.getD_cons_succ, List.getD_cons_zero, Fp.toNat_cast_of_lt (hPr _)]
    rfl
  rw [hmc'] at ea
  obtain ⟨w, hw, hwn⟩ := stack_top_i32 hnum ea.symm
  have hsz2 : s.stack.size - 1 < s.stack.size := by omega
  have hwt : s.stack[s.stack.size - 1]? = some (.i32 w) := by
    rw [Array.getElem?_eq_getElem hsz2]
    rw [Array.getElem?_eq_getElem hsz2, Option.getD_some] at hw
    rw [hw]
  have hz : decMsg [((memSizeSpace : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((mgc tr r MemG.old : Nat) : F),
      ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((mgc tr r MemG.tz : Nat) : F)] =
      szMsg (mgc tr r MemG.old) (mgc tr r MemG.tz) := by
    simp only [decMsg, szMsg, List.getD_cons_succ, List.getD_cons_zero, Fp.toNat_cast_of_lt (hPr _)]
    rfl
  refine ⟨w, by rw [M3Ctx.ctx_pfOf]; exact hc, by rw [M3Ctx.ctx_pfOf, M3Ctx.ctx_cfg, hfee, hlin]; exact hgf,
    hwn, by omega, hwt, by rw [M3Ctx.ctx_pfOf]; exact hnext, ⟨ls0, by rw [M3Ctx.ctx_labels]; exact hL1, hfl0⟩,
    by rw [M3Ctx.ctx_heights]; exact hH1, by omega, ?_⟩
  rw [hcons, hz, hmc', ea, hw]

end

end WasmBase
