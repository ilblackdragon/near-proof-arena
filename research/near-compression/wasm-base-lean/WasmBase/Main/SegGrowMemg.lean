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
      mgc tr r MemG.kSb + mgc tr r cH = s.stack.size ∧ s.stack.size < P ∧
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
    by rw [M3Ctx.ctx_heights]; exact hH1, by omega, hszP, ?_⟩
  rw [hcons, hz, hmc', ea, hw]

omit H in
/-- The out-STATE of an active MEMG row against a related pre-state. -/
theorem memg_out (X : M3Ctx) {r : Nat} {E : Env} {s : St} {f : Frame}
    {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop} {a b : Nat}
    (R : RelW X.ctx E s f tps tpl t pc S live a b)
    (hin : rowIn MemG.table tr pub 32 r = stMsg (X.ctx.offOf E.k + pc) t S 0 E.sb E.cid) {n : Nat}
    (hn : n = mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1) :
    rowOut MemG.table tr pub 32 r =
      stMsg (X.ctx.offOf E.k + (pc + 1)) (t + 1) (S + (mgc tr r cFee + mgc tr r MemG.lin * n)) 0 E.sb E.cid := by
  obtain ⟨p0, psb, i1, i2, i5⟩ := memg_in R hin
  have p0' : rowNat tr 32 r cPc = X.offOf E.k + pc := p0
  have psb' : rowNat tr 32 r MemG.kSb = E.sb := psb
  rw [memg_rowOut, memg_nE_eval, ← hn, cell_cast tr 32 r cPc, cell_cast tr 32 r MemG.kSb, cell_cast tr 32 r cFee,
    cell_cast tr 32 r MemG.lin, i1, i2, i5, p0', psb', M3Ctx.ctx_offOf]
  simp only [stMsg, Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul, List.cons.injEq, and_true]
  and_intros <;> first | rfl | grind

omit H in
/-- The `i32` push of a value below `2^16` as a message. -/
theorem enc_i32V_small {i n t : Nat} (hn : n < 65536) : enc 0 i (i32V n) t = ⟨0, i, 0, n, 0, 0, 0, t⟩ := by
  have h32 : (UInt32.ofNat n).toNat = n := by
    exact UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
  simp only [enc, i32V, vTag, vNum, h32, Msg.mk.injEq, true_and, and_true]
  refine ⟨Nat.mod_eq_of_lt hn, ?_, ?_, ?_⟩ <;> rw [Nat.div_eq_of_lt (by omega)] <;> rfl

/-- **The spec premise of a successful MEMG `memory.grow` row** (`memGrowOk_rowSpecJQ` read off the
trace): with `Q ⇒ SzC`, the σ-keep `hJk`, the row's charge `fee + lin·n ≤ mf`, and the zero bytes
`A` of the grown range that MEMBG hands to this grow, the row's step is `step_memGrow_ok`. -/
theorem memg_growOk_rowSpec (X : M3Ctx) (hcode : CodeOK3 X tr) {r : Nat} (hr : r < tr.height 32)
    (hg : mgc tr r MemG.fGrow = 1) (hs : mgc tr r MemG.fSize = 0) (hok : mgc tr r MemG.ok = 1)
    {J : Nat → St → Prop} {Q : St → (Msg → Prop) → Prop} {mf : Nat} (hQ : ∀ s live, Q s live → SzC s live)
    (hJk : RowJKeep X.ctx J (rowIn MemG.table tr pub 32 r))
    (hmf : mgc tr r cFee + mgc tr r MemG.lin * (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1) ≤ mf)
    (A : List Nat) (hAnd : A.Nodup)
    (hA : ∀ a ∈ A, mgc tr r MemG.old * pageSize ≤ a ∧
      a < (mgc tr r MemG.old + (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1)) * pageSize)
    {sg : Nat × Nat} :
    RowSpecSegJQ X.ctx J Q mf (rowIn MemG.table tr pub 32 r) (rowOut MemG.table tr pub 32 r)
      (rowCons MemG.table tr pub 32 r) (rowProd MemG.table tr pub 32 r ++ zeroBytes A (mgc tr r cTs)) sg sg := by
  intro E s f tps tpl t pc S live R hJ hQs hin hl h1 h2 h3
  have hP := P_val
  have hPr := rowNat_lt tr 32 r
  obtain ⟨w, hins, hfee, hwn, hstk, hwt, hnext, hL1, hH1, hslot, hszP, hcons⟩ :=
    memg_grow_at H X hcode hr hg hs R hin hl
  obtain ⟨-, psb, i1, -, -⟩ := memg_in R hin
  have ht : mgc tr r cTs = t := natEq (by rw [← cell_cast]; exact i1) (hPr _) (by omega)
  rw [hcons] at hl ⊢
  have hz : live (szMsg (mgc tr r MemG.old) (mgc tr r MemG.tz)) := hl _ (by simp)
  have hpg : mgc tr r MemG.old = s.pages.size := SzC.pages (hQ s live hQs) hz
  obtain ⟨hle, -⟩ := memg_grow_ok_dec H hr hg hs hok
  have hm : maxPagesM3 = 2048 := rfl
  have hokc : s.pages.size + w.toNat ≤ X.ctx.cfg.maxMemoryPages := by
    rw [M3Ctx.ctx_cfg, X.mf.maxPages]; omega
  have hA' : ∀ a ∈ A, s.pages.size * pageSize ≤ a ∧ a < (s.pages.size + w.toNat) * pageSize := by
    intro a ha; rw [← hpg, hwn]; exact hA a ha
  -- the productions
  have hprod : rowProd MemG.table tr pub 32 r ++ zeroBytes A (mgc tr r cTs) =
      enc 0 (s.stack.size - 1) (i32V s.pages.size) t :: szMsg (s.pages.size + w.toNat) t :: zeroBytes A t := by
    rw [(memg_grow_msgs (pub := pub) hg hs).2, ht]
    have c0 : ((mgc tr r MemG.ok : Nat) : F) * ((mgc tr r MemG.old : Nat) : F) +
        (((mgc tr r MemG.fGrow : Nat) : F) - ((mgc tr r MemG.ok : Nat) : F)) * ((65535 : Nat) : F) =
        ((mgc tr r MemG.old : Nat) : F) := by rw [hok, hg]; grind
    have c1 : (((mgc tr r MemG.fGrow : Nat) : F) - ((mgc tr r MemG.ok : Nat) : F)) * ((65535 : Nat) : F) =
        ((0 : Nat) : F) := by rw [hok, hg]; grind
    have c2 : ((mgc tr r MemG.old : Nat) : F) + ((mgc tr r MemG.ok : Nat) : F) *
        (((mgc tr r MemG.n0 : Nat) : F) + ((65536 : Nat) : F) * ((mgc tr r MemG.n1 : Nat) : F)) =
        ((mgc tr r MemG.old + (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1) : Nat) : F) := by
      rw [hok]; simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]; grind
    have hsl : (((mgc tr r MemG.kSb : Nat) : F) + ((mgc tr r cH : Nat) : F) - 1).toNat = s.stack.size - 1 :=
      slot_toNat (k := 1) rfl (by omega) (by omega) (by omega) hszP
    rw [c0, c1, c2, enc_i32V_small (n := s.pages.size) (by omega), hpg, hwn]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, decMsg, List.getD_cons_zero,
      List.getD_cons_succ, szMsg, hsl]
    simp only [Fp.toNat_cast_of_lt (show t < P by omega), Fp.toNat_cast_of_lt (show (0 : Nat) < P by omega),
      Fp.toNat_cast_of_lt (show s.stack.size - 1 < P by omega),
      Fp.toNat_cast_of_lt (show memSizeSpace < P by simp [memSizeSpace]; omega),
      Fp.toNat_cast_of_lt (show s.pages.size < P by omega),
      Fp.toNat_cast_of_lt (show s.pages.size + (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1) < P by omega)]
    rfl
  refine ⟨E.k, pc + 1, mgc tr r cFee + mgc tr r MemG.lin * w.toNat, 0, E.sb, E.cid, by rw [hwn]; exact hmf,
    by omega, memg_out X R hin hwn, ?_⟩
  intro hg'
  refine ⟨fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  rw [hpg] at hz ⊢
  obtain ⟨s', hs', -, hR, -⟩ := step_memGrow_ok X.ctx R hins hfee hstk hwt hg' hokc hnext hL1 hH1
    (hQ s live hQs) hz A hAnd hA'
  rw [hprod]
  exact ⟨s', hs', hR, hJk E s f tps tpl t pc S live _ _ s' R hin h1 hJ hs'⟩

omit H in
/-- The `i32` `2^32 − 1` (a failed grow's result) as a message. -/
theorem enc_i32V_fail {i t : Nat} : enc 0 i (i32V (2 ^ 32 - 1)) t = ⟨0, i, 0, 65535, 65535, 0, 0, t⟩ := by
  have h32 : (UInt32.ofNat (2 ^ 32 - 1)).toNat = 2 ^ 32 - 1 := UInt32.toNat_ofNat_of_lt' (by decide)
  simp only [enc, i32V, vTag, vNum, h32]

/-- **The spec premise of a failed MEMG `memory.grow` row** (`ok = 0`): the step is
`step_memGrow_fail` (result `2^32 − 1`, memory and size unchanged). -/
theorem memg_growFail_rowSpec (X : M3Ctx) (hcode : CodeOK3 X tr) {r : Nat} (hr : r < tr.height 32)
    (hg : mgc tr r MemG.fGrow = 1) (hs : mgc tr r MemG.fSize = 0) (hok : mgc tr r MemG.ok = 0)
    {J : Nat → St → Prop} {Q : St → (Msg → Prop) → Prop} {mf : Nat} (hQ : ∀ s live, Q s live → SzC s live)
    (hJk : RowJKeep X.ctx J (rowIn MemG.table tr pub 32 r))
    (hmf : mgc tr r cFee + mgc tr r MemG.lin * (mgc tr r MemG.n0 + 65536 * mgc tr r MemG.n1) ≤ mf)
    {sg : Nat × Nat} :
    RowSpecSegJQ X.ctx J Q mf (rowIn MemG.table tr pub 32 r) (rowOut MemG.table tr pub 32 r)
      (rowCons MemG.table tr pub 32 r) (rowProd MemG.table tr pub 32 r) sg sg := by
  intro E s f tps tpl t pc S live R hJ hQs hin hl h1 h2 h3
  have hP := P_val
  have hPr := rowNat_lt tr 32 r
  obtain ⟨w, hins, hfee, hwn, hstk, hwt, hnext, hL1, hH1, hslot, hszP, hcons⟩ :=
    memg_grow_at H X hcode hr hg hs R hin hl
  obtain ⟨-, psb, i1, -, -⟩ := memg_in R hin
  have ht : mgc tr r cTs = t := natEq (by rw [← cell_cast]; exact i1) (hPr _) (by omega)
  rw [hcons] at hl ⊢
  have hz : live (szMsg (mgc tr r MemG.old) (mgc tr r MemG.tz)) := hl _ (by simp)
  have hpg : mgc tr r MemG.old = s.pages.size := SzC.pages (hQ s live hQs) hz
  obtain ⟨hgt, -⟩ := memg_grow_fail_dec H hr hg hs hok
  have hfail : X.ctx.cfg.maxMemoryPages < s.pages.size + w.toNat := by
    rw [M3Ctx.ctx_cfg, X.mf.maxPages]; omega
  have hprod : rowProd MemG.table tr pub 32 r =
      [enc 0 (s.stack.size - 1) (i32V (2 ^ 32 - 1)) t, szMsg s.pages.size t] := by
    rw [(memg_grow_msgs (pub := pub) hg hs).2, ht]
    have c0 : ((mgc tr r MemG.ok : Nat) : F) * ((mgc tr r MemG.old : Nat) : F) +
        (((mgc tr r MemG.fGrow : Nat) : F) - ((mgc tr r MemG.ok : Nat) : F)) * ((65535 : Nat) : F) =
        ((65535 : Nat) : F) := by rw [hok, hg]; grind
    have c1 : (((mgc tr r MemG.fGrow : Nat) : F) - ((mgc tr r MemG.ok : Nat) : F)) * ((65535 : Nat) : F) =
        ((65535 : Nat) : F) := by rw [hok, hg]; grind
    have c2 : ((mgc tr r MemG.old : Nat) : F) + ((mgc tr r MemG.ok : Nat) : F) *
        (((mgc tr r MemG.n0 : Nat) : F) + ((65536 : Nat) : F) * ((mgc tr r MemG.n1 : Nat) : F)) =
        ((mgc tr r MemG.old : Nat) : F) := by rw [hok]; grind
    have hsl : (((mgc tr r MemG.kSb : Nat) : F) + ((mgc tr r cH : Nat) : F) - 1).toNat = s.stack.size - 1 :=
      slot_toNat (k := 1) rfl (by omega) (by omega) (by omega) hszP
    rw [c0, c1, c2, enc_i32V_fail, hpg]
    simp only [List.map_cons, List.map_nil, decMsg, List.getD_cons_zero, List.getD_cons_succ, szMsg, hsl]
    simp only [Fp.toNat_cast_of_lt (show t < P by omega), Fp.toNat_cast_of_lt (show (0 : Nat) < P by omega),
      Fp.toNat_cast_of_lt (show (65535 : Nat) < P by omega),
      Fp.toNat_cast_of_lt (show memSizeSpace < P by simp [memSizeSpace]; omega),
      Fp.toNat_cast_of_lt (show s.pages.size < P by rw [← hpg]; exact hPr _)]
    rfl
  refine ⟨E.k, pc + 1, mgc tr r cFee + mgc tr r MemG.lin * w.toNat, 0, E.sb, E.cid, by rw [hwn]; exact hmf,
    by omega, memg_out X R hin hwn, ?_⟩
  intro hg'
  refine ⟨fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  rw [hpg] at hz ⊢
  obtain ⟨s', hs', -, hR, -⟩ := step_memGrow_fail X.ctx R hins hfee hstk hwt hg' hfail hnext hL1 hH1
    (hQ s live hQs) hz
  rw [hprod]
  exact ⟨s', hs', hR, hJk E s f tps tpl t pc S live _ _ s' R hin h1 hJ hs'⟩

/-- **An active `memory.size` row at a related pre-state**: everything `step_memSize` takes. -/
theorem memg_size_at (X : M3Ctx) (hcode : CodeOK3 X tr) {r : Nat} (hr : r < tr.height 32)
    (hg : mgc tr r MemG.fGrow = 0) (hs : mgc tr r MemG.fSize = 1)
    {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop} {a b : Nat}
    (R : RelW X.ctx E s f tps tpl t pc S live a b)
    (hin : rowIn MemG.table tr pub 32 r = stMsg (X.ctx.offOf E.k + pc) t S 0 E.sb E.cid) :
    (X.ctx.pfOf E.k).code[pc]? = some .memSize ∧
      feeUnits X.ctx.cfg (X.ctx.pfOf E.k).gas[pc]? = some (mgc tr r cFee) ∧
      pc + 1 < (X.ctx.pfOf E.k).code.size ∧
      (∃ ls, (X.ctx.ckOf E.k).labels[pc + 1]? = some ls ∧ f.labels = shiftLabels E.sb ls) ∧
      (X.ctx.ckOf E.k).heights[pc + 1]? = some (s.stack.size + 1 - E.sb) ∧
      mgc tr r MemG.kSb + mgc tr r cH = s.stack.size ∧ s.stack.size < P := by
  have hP := P_val
  have hPr := rowNat_lt tr 32 r
  obtain ⟨p0, psb, -, -, -⟩ := memg_in R hin
  obtain ⟨k, l, fee, hk, hl', hoff, hc, hfe, hfee, hh⟩ := memg_fetch_size H X hcode hr hg hs
  have hkE : E.k < X.nf := by have := R.kLt; rwa [M3Ctx.ctx_nf] at this
  have hpcE : pc < (X.pfOf E.k).code.size := by have := R.pcLt; rwa [M3Ctx.ctx_pfOf] at this
  obtain ⟨rfl, rfl⟩ := X.loc_unique hk hl' hkE hpcE (by rw [hoff, p0])
  obtain ⟨ls0, hL0, hfl0⟩ := R.labels
  have hH := R.height
  rw [M3Ctx.ctx_labels] at hL0
  rw [M3Ctx.ctx_heights] at hH
  obtain ⟨hnext, hL1, hH1⟩ := X.memSize_succ hkE hc hL0 hH
  have p3 : mgc tr r cH = s.stack.size - E.sb := by rw [hh, hH]; rfl
  have hsbR := R.sbLe
  have hszP : s.stack.size < P := by
    have := R.sbLt; have := (X.factsOf hkE).hBound _ hpcE; rw [hH] at this; simp at this; omega
  refine ⟨by rw [M3Ctx.ctx_pfOf]; exact hc, by rw [M3Ctx.ctx_pfOf, M3Ctx.ctx_cfg, hfee]; exact hfe,
    by rw [M3Ctx.ctx_pfOf]; exact hnext, ⟨ls0, by rw [M3Ctx.ctx_labels]; exact hL1, hfl0⟩,
    by rw [M3Ctx.ctx_heights, hH1]; congr 1; omega, by omega, hszP⟩

/-- **The spec premise of a MEMG `memory.size` row** (`step_memSize`). -/
theorem memg_size_rowSpec (X : M3Ctx) (hcode : CodeOK3 X tr) {r : Nat} (hr : r < tr.height 32)
    (hg : mgc tr r MemG.fGrow = 0) (hs : mgc tr r MemG.fSize = 1)
    {J : Nat → St → Prop} {Q : St → (Msg → Prop) → Prop} {mf : Nat} (hQ : ∀ s live, Q s live → SzC s live)
    (hJk : RowJKeep X.ctx J (rowIn MemG.table tr pub 32 r)) (hmf : mgc tr r cFee ≤ mf) {sg : Nat × Nat} :
    RowSpecSegJQ X.ctx J Q mf (rowIn MemG.table tr pub 32 r) (rowOut MemG.table tr pub 32 r)
      (rowCons MemG.table tr pub 32 r) (rowProd MemG.table tr pub 32 r) sg sg := by
  intro E s f tps tpl t pc S live R hJ hQs hin hl h1 h2 h3
  have hP := P_val
  have hPr := rowNat_lt tr 32 r
  have hok : mgc tr r MemG.ok = 0 := by
    have h := H.constr 32 (segG_lt nloc ngl 32 (by decide)) r hr (v MemG.ok * (1 - v MemG.fGrow))
      (by rw [segG_t32']; simp [MemG.table, MemG.constraints])
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memg_col_eval, hg] at h
    exact cast_zero_nat (hPr _) (by grind)
  have hlin : mgc tr r MemG.lin = 0 := by
    have h := H.constr 32 (segG_lt nloc ngl 32 (by decide)) r hr (v MemG.lin * (1 - v MemG.fGrow))
      (by rw [segG_t32']; simp [MemG.table, MemG.constraints])
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memg_col_eval, hg] at h
    exact cast_zero_nat (hPr _) (by grind)
  obtain ⟨hins, hfee, hnext, hL1, hH1, hslot, hszP⟩ := memg_size_at H X hcode hr hg hs R hin
  obtain ⟨-, psb, i1, -, -⟩ := memg_in R hin
  have ht : mgc tr r cTs = t := natEq (by rw [← cell_cast]; exact i1) (hPr _) (by omega)
  obtain ⟨hcons, hprod0⟩ := memg_size_msgs (pub := pub) hg hs hok
  have hz0 : decMsg [((memSizeSpace : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((mgc tr r MemG.old : Nat) : F),
      ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((mgc tr r MemG.tz : Nat) : F)] =
      szMsg (mgc tr r MemG.old) (mgc tr r MemG.tz) := by
    simp only [decMsg, szMsg, List.getD_cons_succ, List.getD_cons_zero, Fp.toNat_cast_of_lt (hPr _)]
    rfl
  rw [hz0] at hcons
  rw [hcons] at hl ⊢
  have hz : live (szMsg (mgc tr r MemG.old) (mgc tr r MemG.tz)) := hl _ (by simp)
  have hpg : mgc tr r MemG.old = s.pages.size := SzC.pages (hQ s live hQs) hz
  have hact : (MemG.act.eval (tr.row pub 32 r)).toNat = 1 := by
    simp only [MemG.act, Expr.eval_add', memg_col_eval, hg, hs]; rfl
  have hold : mgc tr r MemG.old < 65536 :=
    segG_col_lt H (segG_hsend_r16 H) (by decide) (segG_t32' nloc ngl) hr (k := MemG.old)
      (by simp [MemG.table, MemG.inters]) hact
  have hprod : rowProd MemG.table tr pub 32 r =
      [enc 0 s.stack.size (i32V s.pages.size) t, szMsg s.pages.size t] := by
    rw [hprod0, ht, enc_i32V_small (n := s.pages.size) (by omega), ← hpg]
    have hsl : (((mgc tr r MemG.kSb : Nat) : F) + ((mgc tr r cH : Nat) : F)).toNat = s.stack.size :=
      slot_toNat0 rfl (by omega) (by omega) hszP
    simp only [decMsg, List.getD_cons_zero, List.getD_cons_succ, szMsg, hsl]
    simp only [Fp.toNat_cast_of_lt (show t < P by omega), Fp.toNat_cast_of_lt (show (0 : Nat) < P by omega),
      Fp.toNat_cast_of_lt (show memSizeSpace < P by simp [memSizeSpace]; omega),
      Fp.toNat_cast_of_lt (hPr MemG.old)]
    rfl
  refine ⟨E.k, pc + 1, mgc tr r cFee, 0, E.sb, E.cid, hmf, by omega,
    by rw [memg_out X R hin rfl, hlin, Nat.zero_mul]; simp only [Nat.add_zero], ?_⟩
  intro hg'
  refine ⟨fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  rw [hpg] at hz ⊢
  obtain ⟨s', hs', -, hR, -⟩ := step_memSize X.ctx R hins hfee hg' h3 hnext hL1 hH1 (hQ s live hQs) hz
  rw [hprod]
  exact ⟨s', hs', hR, hJk E s f tps tpl t pc S live _ _ s' R hin h1 hJ hs'⟩

end

#print axioms memg_grow_at
#print axioms memg_size_at
#print axioms memg_growOk_rowSpec
#print axioms memg_growFail_rowSpec
#print axioms memg_size_rowSpec

end WasmBase
