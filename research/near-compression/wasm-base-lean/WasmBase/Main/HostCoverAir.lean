import WasmBase.Main.HostEffTwin
import WasmBase.Main.HostIfCover
import WasmBase.Main.HostSpace

/-!
# WasmBase.Main.HostCoverAir — the HOST row's message shape from the segment AIR (E2E M6, COVER item 1)

`rel_twin_post` (`Main/HostEffTwin.lean`) needs, of a HOST row's fused CH traffic (`consCHS`/`prodCHS`:
its own argument/result messages, its `HOSTB` bytes, its REG-C net traffic, its gas register):

* **(c) spaces** — only spaces `0, 3, 6, 7` (`host_cons_space`/`host_prod_space`, already proved), so
  no message in the globals (2), call-record (4), budget (5) or locals (`≥ 16`) spaces;
* **(c) stack messages** — the consumed space-0 messages are the row's present arguments `argMsg j`
  (`pf j = 1`) and the produced one its result word `wordMsg` (`nres = 1`): `host_cons_stk`,
  `host_prod_stk`; with `pf j = 1 ↔ j < np` (`host_pf_lt_np`, from the flag constraints) their slots
  are `size − np + j` / `size − np` (`host_arg_slot`), i.e. the top `np` slots, all consumed;
* **(a) write coverage** — every produced space-3 message has a consumed space-3 message at the same
  address (`host_prod3_paired`).  Syntactic (`PairSp`, `decide`): `HOSTB`'s MEMIO pair (request byte:
  consume at `mtp`, re-produce at `ts`, both counted by `memCnt`) and `REG`'s write pair (old byte `ob`
  consumed at `mtp`, new byte produced at `ts`, both counted by `wcnt`) are the only space-3 sends.

**AIR gap (not fixed here).**  The converse direction — every byte the *spec* call writes is on the
bus — fails: the only space-3 writes of the AIR are REG's `wcnt` rows, and `cWrHid` forces
`hid = read_register` on them.  The five `setU128H` arms (`account_balance`, `account_locked_balance`,
`attached_deposit`, `validator_stake`, `validator_total_stake`) write 16 bytes of linear memory
(`writeMemH ptr (natLE v 16)`) whose `HOSTB` response bytes (`dir = 1`, `reg = 0`) carry **no**
space-3 message (`memCnt = act·(1−dir)·(1−reg)` counts request bytes only).  So after such a call the
live memory messages still carry the old bytes: `HostIf.ans` is unsatisfiable for an honest run whose
written bytes differ from the old ones (completeness), and the twin transfer needs the write-coverage
premise `HostWritesCov` (named in `Main/HostIfCover2.lean`).  Minimal constraint: give `HOSTB` an
old-byte column `ob` and, with count `wmCnt = act·dir·(1−reg)`,
`chRecv 3 (ptr+pos) 0 [ob,0,0,0] mtp wmCnt`, `chSend 3 (ptr+pos) 0 [bv,0,0,0] ts wmCnt`,
`timeChk ts mtp hp wmCnt` (the `RegW.newInters` write shape), so response bytes of non-register
calls are memory writes exactly as `read_register`'s REG write rows are.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. (a) Produced memory messages are paired with consumed ones -/

/-- Every CH send of `T` in space 3 has a CH receive in space 3 with the same count and slot. -/
def PairSp (T : Table) : Bool :=
  T.inters.all fun i => !(decide (i.bus = busStk) && i.send && decide (i.msg.head? = some (.c 3))) ||
    T.inters.any fun i' => decide (i'.bus = busStk) && !i'.send && decide (i'.msg.head? = some (.c 3)) &&
      decide (i'.count = i.count) && decide (i'.msg[1]? = i.msg[1]?)

theorem pairSp_host : PairSp Host.table = true := by decide +kernel
theorem pairSp_hostb : PairSp HostB.table = true := by decide +kernel
theorem pairSp_regw : PairSp RegW.table = true := by decide +kernel
theorem pairSp_gas : PairSp GasT = true := by decide +kernel

theorem mem_rowMsgs_cnt {T : Table} {tr : Trace} {pub : List F} {t r b : Nat} {s : Bool} {m : List F}
    (hm : m ∈ rowMsgs T tr pub t r b s) :
    ∃ i ∈ T.inters, i.bus = b ∧ i.send = s ∧ (i.count.eval (tr.row pub t r)).toNat = 1 ∧
      m = i.msg.map (·.eval (tr.row pub t r)) := by
  rw [rowMsgs_eq] at hm
  obtain ⟨i, hi, he⟩ := List.mem_filterMap.mp hm
  obtain ⟨hi1, hi2⟩ := List.mem_filter.mp hi
  simp only [decide_eq_true_eq] at hi2
  split at he
  · cases he; exact ⟨i, hi1, hi2.1, hi2.2, by assumption, rfl⟩
  · cases he

theorem mem_rowMsgs_mk {T : Table} {tr : Trace} {pub : List F} {t r b : Nat} {s : Bool} {i : Inter}
    (hi : i ∈ T.inters) (hb : i.bus = b) (hs : i.send = s) (hc : (i.count.eval (tr.row pub t r)).toNat = 1) :
    i.msg.map (·.eval (tr.row pub t r)) ∈ rowMsgs T tr pub t r b s := by
  rw [rowMsgs_eq]
  exact List.mem_filterMap.mpr ⟨i, List.mem_filter.mpr ⟨hi, by simp [hb, hs]⟩, by simp [hc]⟩

theorem getD1_map (l : List Expr) (rw : Row) :
    (l.map (·.eval rw)).getD 1 0 = ((l[1]?).map (·.eval rw)).getD 0 := by
  rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> rfl

theorem getD0_map (l : List Expr) (rw : Row) :
    (l.map (·.eval rw)).getD 0 0 = ((l.head?).map (·.eval rw)).getD 0 := by
  rcases l with _ | ⟨a, l⟩ <;> rfl

/-- **A produced space-3 message of a `PairSp`, `ConstSp` table has a consumed space-3 message at
the same address in the same row.** -/
theorem pairSp_rowProd {T : Table} (hP : PairSp T = true) (hS : ConstSp T = true)
    {tr : Trace} {pub : List F} {t r : Nat} {x : Msg} (hx : x ∈ rowProd T tr pub t r) (h3 : x.space = 3) :
    ∃ y ∈ rowCons T tr pub t r, y.space = 3 ∧ y.slot = x.slot := by
  have hPv := P_val
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  obtain ⟨i, hi, hb, hs, hc, rfl⟩ := mem_rowMsgs_cnt hm
  -- the head of `i` is a constant space, hence `.c 3`
  have hcs := List.all_eq_true.mp hS i hi
  simp only [Bool.or_eq_true, decide_eq_true_eq, hb, ne_eq, not_true_eq_false, false_or,
    List.any_eq_true] at hcs
  obtain ⟨k, hk, hk'⟩ := hcs
  have hkP : k < P := by
    simp only [hostSpaces, Register.space, spaceGas, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> omega
  have hk3 : k = 3 := by
    have : (decMsg (i.msg.map (·.eval (tr.row pub t r)))).space = k := by
      simp only [decMsg, getD0_map, hk', Option.map_some, Option.getD_some, Expr.eval_c]
      exact Fp.toNat_cast_of_lt hkP
    rw [← this]; exact h3
  subst hk3
  -- its partner
  have hp := List.all_eq_true.mp hP i hi
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true] at hp
  rcases hp with ((h | h) | h) | ⟨i', hi', ⟨⟨⟨⟨hb', hs'⟩, hh'⟩, hc'⟩, hl'⟩⟩
  · exact absurd hb h
  · rw [hs] at h; cases h
  · exact absurd hk' h
  refine ⟨decMsg (i'.msg.map (·.eval (tr.row pub t r))), List.mem_map.mpr ⟨_, mem_rowMsgs_mk hi' hb' hs'
    (by rw [hc']; exact hc), rfl⟩, ?_, ?_⟩
  · simp only [decMsg, getD0_map, hh', Option.map_some, Option.getD_some, Expr.eval_c]
    exact Fp.toNat_cast_of_lt (by omega)
  · simp only [decMsg, getD1_map, hl']

/-- A consumed memory message at address `a` of the HOST row (`Cov3` of `consCHS`). -/
theorem host_prod3_paired (tr : Trace) (pub : List F) (r : Nat) :
    ∀ y ∈ prodCHS tr pub (22, r), y.space = 3 → Cov3 (consCHS tr pub (22, r)) y.slot := by
  intro x hx h3
  simp only [prodCHS, prodCHM2, rowProdM, hostbProdH, regProdH, gasProdH, chipTM2, ite_true,
    List.mem_append] at hx
  have toC : ∀ y, y ∈ consCHS tr pub (22, r) → y.space = 3 → y.slot = x.slot → Cov3 (consCHS tr pub (22, r)) x.slot :=
    fun y hy h1 h2 => ⟨y, hy, h1, h2⟩
  rcases hx with ((hx | hx | hx) | hx)
  · obtain ⟨y, hy, h1, h2⟩ := pairSp_rowProd pairSp_host constSp_host hx h3
    refine toC y ?_ h1 h2
    simp only [consCHS, consCHM2, rowConsM, chipTM2, ite_true, List.mem_append]
    exact Or.inl (Or.inl hy)
  · unfold hostbProdOf at hx
    obtain ⟨r', hr', hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨y, hy, h1, h2⟩ := pairSp_rowProd pairSp_hostb constSp_hostb hx h3
    refine toC y ?_ h1 h2
    simp only [consCHS, consCHM2, hostbConsH, hostbConsOf, ite_true, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inr (Or.inl ⟨r', hr', hy⟩))
  · unfold regProdOf at hx
    obtain ⟨r', hr', hx⟩ := List.mem_flatMap.mp hx
    unfold regNetProd at hx
    split at hx
    · simp at hx
    · obtain ⟨y, hy, h1, h2⟩ := pairSp_rowProd pairSp_regw constSp_regw hx h3
      refine toC y ?_ h1 h2
      simp only [consCHS, consCHM2, regConsH, regConsOf, regNetCons, ite_true, List.mem_append,
        List.mem_flatMap]
      exact Or.inl (Or.inr (Or.inr ⟨r', hr', hy⟩))
  · unfold gasProdOf at hx
    obtain ⟨y, hy, h1, h2⟩ := pairSp_rowProd pairSp_gas constSp_gas hx h3
    refine toC y ?_ h1 h2
    simp only [consCHS, gasConsH, gasConsOf, ite_true, List.mem_append]
    exact Or.inr hy

/-- **(c) The spaces of a HOST row's fused traffic.** -/
theorem host_sp4 (tr : Trace) (pub : List F) (r : Nat) :
    ∀ y ∈ consCHS tr pub (22, r) ++ prodCHS tr pub (22, r),
      y.space = 0 ∨ y.space = 3 ∨ y.space = 6 ∨ y.space = 7 := by
  intro y hy
  have h : HostSp y := by
    rcases List.mem_append.mp hy with h | h
    · exact host_cons_space tr pub rfl y h
    · exact host_prod_space tr pub rfl y h
  simpa [HostSp, hostSpaces, Register.space, spaceGas] using h

#print axioms host_prod3_paired
#print axioms host_sp4

/-! ## 2. (c) The stack messages of a HOST row -/

/-- No CH interaction of `T` has the constant space `0`. -/
def NoSp0 (T : Table) : Bool :=
  T.inters.all fun i => decide (i.bus ≠ busStk) || decide (i.msg.head? ≠ some (.c 0))

theorem noSp0_hostb : NoSp0 HostB.table = true := by decide +kernel
theorem noSp0_regw : NoSp0 RegW.table = true := by decide +kernel
theorem noSp0_gas : NoSp0 GasT = true := by decide +kernel

theorem noSp0_msg {T : Table} (hS : ConstSp T = true) (h0 : NoSp0 T = true)
    {tr : Trace} {pub : List F} {t r : Nat} {s : Bool} {m : List F}
    (hm : m ∈ rowMsgs T tr pub t r busStk s) : (decMsg m).space ≠ 0 := by
  have hPv := P_val
  obtain ⟨i, hi, hb, -, -, rfl⟩ := mem_rowMsgs_cnt hm
  have hcs := List.all_eq_true.mp hS i hi
  simp only [Bool.or_eq_true, decide_eq_true_eq, hb, ne_eq, not_true_eq_false, false_or,
    List.any_eq_true] at hcs
  obtain ⟨k, hk, hk'⟩ := hcs
  have hn := List.all_eq_true.mp h0 i hi
  simp only [Bool.or_eq_true, decide_eq_true_eq, hb, ne_eq, not_true_eq_false, false_or, hk',
    Option.some.injEq] at hn
  have hkP : k < P := by
    simp only [hostSpaces, Register.space, spaceGas, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> omega
  have hk0 : k ≠ 0 := fun e => hn (by rw [e])
  simp only [decMsg, getD0_map, hk', Option.map_some, Option.getD_some, Expr.eval_c]
  rw [Fp.toNat_cast_of_lt hkP]; exact hk0

theorem noSp0_rowCons {T : Table} (hS : ConstSp T = true) (h0 : NoSp0 T = true)
    {tr : Trace} {pub : List F} {t r : Nat} : ∀ x ∈ rowCons T tr pub t r, x.space ≠ 0 := by
  intro x hx
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  exact noSp0_msg hS h0 hm

theorem noSp0_rowProd {T : Table} (hS : ConstSp T = true) (h0 : NoSp0 T = true)
    {tr : Trace} {pub : List F} {t r : Nat} : ∀ x ∈ rowProd T tr pub t r, x.space ≠ 0 := by
  intro x hx
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  exact noSp0_msg hS h0 hm

/-- **The consumed stack messages of a HOST row are its present arguments.** -/
theorem host_cons_stk (tr : Trace) (pub : List F) (r : Nat) :
    ∀ y ∈ consCHS tr pub (22, r), y.space = 0 →
      ∃ j, j < Host.nArgs ∧ rowNat tr 22 r (Host.pf j) = 1 ∧ y = argMsg tr r j := by
  intro y hy h0
  simp only [consCHS, consCHM2, rowConsM, hostbConsH, regConsH, gasConsH, chipTM2, ite_true,
    List.mem_append] at hy
  rcases hy with ((hy | hy | hy) | hy)
  · rw [host_row_cons] at hy
    obtain ⟨j, hj, hy⟩ := List.mem_flatMap.mp hy
    by_cases hp : rowNat tr 22 r (Host.pf j) = 1
    · rw [if_pos hp] at hy
      exact ⟨j, argRange_lt hj, hp, List.mem_singleton.mp hy⟩
    · rw [if_neg hp] at hy; simp at hy
  · unfold hostbConsOf at hy
    obtain ⟨r', -, hy⟩ := List.mem_flatMap.mp hy
    exact absurd h0 (noSp0_rowCons constSp_hostb noSp0_hostb y hy)
  · unfold regConsOf at hy
    obtain ⟨r', -, hy⟩ := List.mem_flatMap.mp hy
    exact absurd h0 (noSp0_rowCons constSp_regw noSp0_regw y hy)
  · unfold gasConsOf at hy
    exact absurd h0 (noSp0_rowCons constSp_gas noSp0_gas y hy)

/-- **The produced stack message of a HOST row is its result word.** -/
theorem host_prod_stk (tr : Trace) (pub : List F) (r : Nat) :
    ∀ y ∈ prodCHS tr pub (22, r), y.space = 0 → y = wordMsg tr r := by
  intro y hy h0
  simp only [prodCHS, prodCHM2, rowProdM, hostbProdH, regProdH, gasProdH, chipTM2, ite_true,
    List.mem_append] at hy
  rcases hy with ((hy | hy | hy) | hy)
  · rw [host_row_prod] at hy
    split at hy
    · exact List.mem_singleton.mp hy
    · simp at hy
  · unfold hostbProdOf at hy
    obtain ⟨r', -, hy⟩ := List.mem_flatMap.mp hy
    exact absurd h0 (noSp0_rowProd constSp_hostb noSp0_hostb y hy)
  · unfold regProdOf at hy
    obtain ⟨r', -, hy⟩ := List.mem_flatMap.mp hy
    unfold regNetProd at hy
    split at hy
    · simp at hy
    · exact absurd h0 (noSp0_rowProd constSp_regw noSp0_regw y hy)
  · unfold gasProdOf at hy
    exact absurd h0 (noSp0_rowProd constSp_gas noSp0_gas y hy)

/-! ## 3. The argument flags: `pf j = 1 ↔ j < np` -/

/-- **The HOST row's field facts on a segment trace** (`host_rowfacts` from the segment AIR's
table-22 constraints, `seg_host_con`). -/
theorem host_rowfacts_seg {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22)
    (hact : rowAct Host.table tr pub 22 r) : HostRowFacts pub tr r := by
  have hcon := seg_host_con H hr
  have hact' : rowNat tr 22 r Host.act = 1 := host_act_nat hact
  have hactF : (rowNat tr 22 r Host.act : F) = 1 := by
    rw [hact']; exact cast_one
  have hbS : (rowNat tr 22 r Host.st : F) * ((rowNat tr 22 r Host.st : F) - 1) = 0 := by
    have h := hcon Host.cSt host_cSt_mem
    simpa only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat',
      natRow_cur, cast_one, Host.cSt, Host.st] using h
  have hbR : (rowNat tr 22 r Host.ar : F) * ((rowNat tr 22 r Host.ar : F) - 1) = 0 := by
    have h := hcon Host.cAr host_cAr_mem
    simpa only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat',
      natRow_cur, cast_one, Host.cAr, Host.ar] using h
  have hpfBit : ∀ j, j < Host.nArgs →
      (rowNat tr 22 r (Host.pf j) : F) * ((rowNat tr 22 r (Host.pf j) : F) - 1) = 0 := by
    intro j hj
    have h := hcon (Host.cP j) (host_cP_mem j hj)
    simpa only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat',
      natRow_cur, cast_one, Host.cP] using h
  have hnp' : (rowNat tr 22 r Host.np : F) =
      ((cellSum (rowNat tr 22 r) Host.pf Host.argRange : Nat) : F) := by
    have h := hcon Host.cNp host_cNp_mem
    simp only [v, Expr.eval_sub', Expr.eval_col, natRow_cur, Host.cNp] at h
    rw [eval_pfSum] at h
    have : (rowNat tr 22 r Host.np : F) - ((cellSum (rowNat tr 22 r) Host.pf Host.argRange : Nat) : F) = 0 := h
    grind
  have hord' : ∀ j, j + 1 < Host.nArgs → (rowNat tr 22 r (Host.pf (j + 1)) : F) -
      (rowNat tr 22 r (Host.pf j) : F) * (rowNat tr 22 r (Host.pf (j + 1)) : F) = 0 := by
    intro j hj
    have h := hcon (Host.cPOrder j) (host_cPOrder_mem j hj)
    simpa only [v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, natRow_cur, Host.cPOrder] using h
  have hnr' : (rowNat tr 22 r Host.nres : F) - (rowNat tr 22 r Host.ar : F) +
      (rowNat tr 22 r Host.st : F) * (rowNat tr 22 r Host.ar : F) = 0 := by
    have h := hcon Host.cNres host_cNres_mem
    simpa only [v, Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_col, natRow_cur,
      Host.cNres, Host.nres, Host.st, Host.ar] using h
  have hpad : ∀ j, j < Host.nArgs → (rowNat tr 22 r (Host.tagP j) : F) -
      (rowNat tr 22 r (Host.pf j) : F) * (rowNat tr 22 r (Host.tagP j) : F) = 0 := by
    intro j hj
    have h := hcon (Host.cPad j) (host_cPad_mem j hj)
    simpa only [v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, natRow_cur, Host.cPad] using h
  exact ⟨hactF, hbS, hbR, hpfBit, hnp', hord', hnr', hpad, host_rowIn, host_rowOut⟩

theorem cellSum_range9 (c : Nat → Nat) :
    cellSum c Host.pf Host.argRange = c (Host.pf 0) + c (Host.pf 1) + c (Host.pf 2) + c (Host.pf 3) +
      c (Host.pf 4) + c (Host.pf 5) + c (Host.pf 6) + c (Host.pf 7) + c (Host.pf 8) := by
  simp [cellSum, Host.argRange, Host.nArgs, List.range, List.range.loop]

/-- **A prefix-closed bit vector of nine flags summing to `np` has exactly the first `np` set.** -/
theorem pf_iff_lt (c : Nat → Nat) (hbit : ∀ j, j < Host.nArgs → c (Host.pf j) ≤ 1)
    (hord : ∀ j, j + 1 < Host.nArgs → c (Host.pf (j + 1)) ≤ c (Host.pf j))
    {np : Nat} (hnp : np = cellSum c Host.pf Host.argRange) :
    ∀ j, j < Host.nArgs → (c (Host.pf j) = 1 ↔ j < np) := by
  rw [cellSum_range9] at hnp
  have hn : Host.nArgs = 9 := rfl
  have b0 := hbit 0 (by omega); have b1 := hbit 1 (by omega); have b2 := hbit 2 (by omega)
  have b3 := hbit 3 (by omega); have b4 := hbit 4 (by omega); have b5 := hbit 5 (by omega)
  have b6 := hbit 6 (by omega); have b7 := hbit 7 (by omega); have b8 := hbit 8 (by omega)
  have o0 := hord 0 (by omega); have o1 := hord 1 (by omega); have o2 := hord 2 (by omega)
  have o3 := hord 3 (by omega); have o4 := hord 4 (by omega); have o5 := hord 5 (by omega)
  have o6 := hord 6 (by omega); have o7 := hord 7 (by omega)
  simp only [Nat.reduceAdd, Nat.zero_add] at o0 o1 o2 o3 o4 o5 o6 o7
  intro j hj
  rw [hn] at hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- **`pf j = 1 ↔ j < np`** at an active HOST row of a segment trace. -/
theorem host_pf_lt_np {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22)
    (hact : rowAct Host.table tr pub 22 r) :
    rowNat tr 22 r Host.np ≤ Host.nArgs ∧
      ∀ j, j < Host.nArgs → (rowNat tr 22 r (Host.pf j) = 1 ↔ j < rowNat tr 22 r Host.np) := by
  have RF := host_rowfacts_seg H hr hact
  have hpfBit : ∀ j, j < Host.nArgs → rowNat tr 22 r (Host.pf j) ≤ 1 := by
    intro j hj
    rcases bool_nat (rowNat_lt tr 22 r (Host.pf j)) (RF.pfBit j hj) with h | h <;> omega
  have hord : ∀ j, j + 1 < Host.nArgs → rowNat tr 22 r (Host.pf (j + 1)) ≤ rowNat tr 22 r (Host.pf j) :=
    fun j hj => host_order_nat (tr.row pub 22 r) (rowNat_lt tr 22 r) hpfBit RF.order hj
  have hnp : rowNat tr 22 r Host.np = cellSum (rowNat tr 22 r) Host.pf Host.argRange :=
    natEq RF.npEq (rowNat_lt tr 22 r Host.np) (cellSum_argRange_lt (fun j hj => hpfBit j (argRange_lt hj)))
  refine ⟨?_, pf_iff_lt _ hpfBit hord hnp⟩
  have h := cellSum_le (rowNat tr 22 r) Host.pf 1 Host.argRange (fun j hj => hpfBit j (argRange_lt hj))
  rw [argRange_length] at h; omega

#print axioms host_cons_stk
#print axioms host_prod_stk
#print axioms host_pf_lt_np

end WasmBase
