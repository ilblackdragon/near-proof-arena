import ZkFormal.PQ.Receipt.Table
import ZkFormal.Near.Extract.Eval

/-!
# `ZkFormal.PQ.Receipt.Rows` — the `PBC` row lemmas

What a `HoldsP`/`TableLocal` witness of `PBC` gives, field by field, as *theorems*: every
constraint of `Table.lean` becomes the `Nat` fact it is meant to express.  These are the lemmas
`Bookkeeping.lean` builds on, and they are why the table is small enough to read.

The pattern is the v3 tables' (`Near/Extract/Eval.lean`,
`NearV3/Rcpt/Extract/SizeProof.lean`): read a constraint off `TableLocal.constr`, `simp` the DSL
evaluation, then `grind`/`omega` the field equation.  A field equation becomes a `Nat` equation
through `eq_of_cast` (both sides below `P`) or `Nat.mod_eq_of_lt`.

## The point of the shape

The interesting lemmas are the *counter* ones, because they are what makes `rcpt`/`prm` mean
"number of receipts / promises so far" rather than "a witnessed number":

* `rcpt_row`: `rcpt = prevR + addR` on an active row;
* `rcpt_chain`: consecutive active rows have `next.prevR = rcpt`;
* `rcpt_start`: the first row has `prevR = 0`.

By induction (`counts_are_additive`, `Bookkeeping.lean`) these give
`rcpt(row n) = Σ_{k ≤ n} addR(row k)`: the counter is a *sum of bits*, not a witness.  The same
holds for `prm`.  That is the whole bookkeeping obligation: an index the Wasm side returns is
below the number of receipts because the receipt counter is a count.
-/

namespace ZkFormal.PQ.Receipt

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.V2

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- A `PBC` constraint vanishes on row `r`. -/
theorem con (hL : TableLocal table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    {e : Expr} (he : e ∈ constraints) : e.eval tr tt r pub = 0 :=
  hL.constr r hr e he

/-- Row `r + 1` really is the next row. -/
theorem nxt {r : Nat} (h : r + 1 < tr.height tt) : (r + 1) % tr.height tt = r + 1 :=
  Nat.mod_eq_of_lt h

/-! ## Membership -/

/-- `simp only [constraints, List.mem_append]` flattens the constraint list into

`(((((bits ∨ state) ∨ start) ∨ tgt) ∨ dep) ∨ data) ∨ inert`

so each group's membership is a fixed `Or` nesting.  These six lemmas are the only place the
nesting appears. -/
theorem mem_bits {e : Expr} (he : e ∈ cBits) : e ∈ constraints := by
  simp only [constraints, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl he)))))

theorem mem_state {e : Expr} (he : e ∈ cState) : e ∈ constraints := by
  simp only [constraints, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr he)))))

theorem mem_start {e : Expr} (he : e ∈ cStart) : e ∈ constraints := by
  simp only [constraints, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr he))))

theorem mem_tgt {e : Expr} (he : e ∈ cTgt) : e ∈ constraints := by
  simp only [constraints, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr he)))

theorem mem_dep {e : Expr} (he : e ∈ cDep) : e ∈ constraints := by
  simp only [constraints, List.mem_append]; exact Or.inl (Or.inl (Or.inr he))

theorem mem_data {e : Expr} (he : e ∈ cData) : e ∈ constraints := by
  simp only [constraints, List.mem_append]; exact Or.inl (Or.inr he)

theorem mem_inert {e : Expr} (he : e ∈ cInert) : e ∈ constraints := by
  simp only [constraints, List.mem_append]; exact Or.inr he

/-- The seven state-group constraints are in the table (the `Or` nesting is `mem_state`). -/
theorem mem_nres : cNres ∈ constraints := by
  simp only [constraints, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (by simp [cState]))))))

theorem mem_rcpt : cRcpt ∈ constraints := by
  simp only [constraints, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (by simp [cState]))))))

theorem mem_prm : cPrm ∈ constraints := by
  simp only [constraints, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (by simp [cState]))))))

theorem mem_rcptChain : cRcptChain ∈ constraints := by
  simp only [constraints, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (by simp [cState]))))))

theorem mem_prmChain : cPrmChain ∈ constraints := by
  simp only [constraints, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (by simp [cState]))))))

theorem mem_firstAct : cFirstAct ∈ constraints := by
  simp only [constraints, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (by simp [cState]))))))

theorem mem_padPad : cPadPad ∈ constraints := by
  simp only [constraints, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (by simp [cState]))))))

theorem mem_act_bit : bool (c act) ∈ constraints :=
  mem_bits (by unfold cBits bitCols; exact List.mem_cons_self)
theorem mem_st_bit : bool (c st) ∈ constraints :=
  mem_bits (by unfold cBits bitCols; exact List.mem_cons_of_mem _ List.mem_cons_self)
theorem mem_startR : .mul .isFirst (c prevR) ∈ constraints :=
  mem_start (by unfold cStart; exact List.mem_cons_self)
theorem mem_startP : .mul .isFirst (c prevP) ∈ constraints :=
  mem_start (by unfold cStart; exact List.mem_cons_of_mem _ List.mem_cons_self)
theorem mem_tgtOff : .mul (sub (k 1) (c hasTgt)) (c tgt) ∈ constraints :=
  mem_tgt (by unfold cTgt; exact List.mem_cons_self)
theorem mem_tgtLt :
    .mul (c hasTgt) (sub (.add (c tgt) (.add (c gTgt) (k 1))) (c rcpt)) ∈ constraints :=
  mem_tgt (by unfold cTgt; exact List.mem_cons_of_mem _ List.mem_cons_self)
theorem mem_depOff : .mul (sub (k 1) (c hasDep)) (c dep) ∈ constraints :=
  mem_dep (by unfold cDep; exact List.mem_cons_self)
theorem mem_depLe : .mul (c hasDep) (sub (.add (c dep) (c gDep)) (k 128)) ∈ constraints :=
  mem_dep (by unfold cDep; exact List.mem_cons_of_mem _ List.mem_cons_self)
theorem mem_dataOff : .mul (sub (k 1) (c hasDep)) (sub (c addD) (c dadd)) ∈ constraints :=
  mem_data (by unfold cData; exact List.mem_cons_self)
theorem mem_dataOn : .mul (c hasDep) (sub (c addD) (c dep)) ∈ constraints :=
  mem_data (by unfold cData; exact List.mem_cons_of_mem _ List.mem_cons_self)

/-! ## Bit columns -/

/-- `act` is a bit. -/
theorem act_bit (hL : TableLocal table tr tt pub) {r : Nat} (hr : r < tr.height tt) :
    tr.cell tt r act = 0 ∨ tr.cell tt r act = 1 := by
  have h := con (r := r) hL hr mem_act_bit
  simp only [eval_bool, eval_c] at h
  exact bool_cases h

/-- `st` is a bit. -/
theorem st_bit (hL : TableLocal table tr tt pub) {r : Nat} (hr : r < tr.height tt) :
    tr.cell tt r st = 0 ∨ tr.cell tt r st = 1 := by
  have h := con (r := r) hL hr mem_st_bit
  simp only [eval_bool, eval_c] at h
  exact bool_cases h

/-! ## The counters

Everything is `if act = 1`-gated, so each lemma takes `act = 1`.  The gate is what lets the row
be padding without breaking the law. -/

/-- **`rcpt = prevR + addR`** on an active row. -/
theorem rcpt_row (hL : TableLocal table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r act = 1) : tr.cell tt r rcpt = tr.cell tt r prevR + tr.cell tt r addR := by
  have h := con (r := r) hL hr mem_rcpt
  simp only [cRcpt, eval_mul, eval_sub, eval_add, eval_c] at h
  rw [ha] at h
  grind

/-- **`prm = prevP + addP`** on an active row. -/
theorem prm_row (hL : TableLocal table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r act = 1) : tr.cell tt r prm = tr.cell tt r prevP + tr.cell tt r addP := by
  have h := con (r := r) hL hr mem_prm
  simp only [cPrm, eval_mul, eval_sub, eval_add, eval_c] at h
  rw [ha] at h
  grind

/-- **The receipt counter chains.**  Consecutive active rows have `next.prevR = rcpt`, so the
counter is one running count and not a per-row witness. -/
theorem rcpt_chain (hL : TableLocal table tr tt pub) {r : Nat} (hr : r + 1 < tr.height tt)
    (ha : tr.cell tt r act = 1) (hn : tr.cell tt (r + 1) act = 1) :
    tr.cell tt (r + 1) prevR = tr.cell tt r rcpt := by
  have h0 : r < tr.height tt := by omega
  have h := con (r := r) hL h0 mem_rcptChain
  simp only [cRcptChain, eval_mul3, eval_mul, eval_sub, eval_c, eval_n, eval_isTransition,
    nxt hr, ite_eq_right (show ¬ r + 1 = tr.height tt by omega)] at h
  rw [ha, hn] at h
  grind

/-- **The promise counter chains**, exactly as the receipt counter. -/
theorem prm_chain (hL : TableLocal table tr tt pub) {r : Nat} (hr : r + 1 < tr.height tt)
    (ha : tr.cell tt r act = 1) (hn : tr.cell tt (r + 1) act = 1) :
    tr.cell tt (r + 1) prevP = tr.cell tt r prm := by
  have h0 : r < tr.height tt := by omega
  have h := con (r := r) hL h0 mem_prmChain
  simp only [cPrmChain, eval_mul3, eval_mul, eval_sub, eval_c, eval_n, eval_isTransition,
    nxt hr, ite_eq_right (show ¬ r + 1 = tr.height tt by omega)] at h
  rw [ha, hn] at h
  grind

/-- **The first row is a call.** -/
theorem first_act (hL : TableLocal table tr tt pub) (h2 : 1 < tr.height tt) :
    tr.cell tt 0 act = 1 := by
  have h0 : 0 < tr.height tt := by omega
  have h := con (r := 0) hL h0 mem_firstAct
  simp only [cFirstAct, eval_mul, eval_sub, eval_c, eval_k, eval_isFirst, ite_eq_left rfl] at h
  grind

/-- **The counters start at `0`.** -/
theorem start_zero (hL : TableLocal table tr tt pub) (h0 : 0 < tr.height tt) :
    tr.cell tt 0 prevR = 0 ∧ tr.cell tt 0 prevP = 0 := by
  have h1 := con (r := 0) hL h0 mem_startR
  have h2 := con (r := 0) hL h0 mem_startP
  simp only [eval_mul, eval_c, eval_isFirst, ite_eq_left rfl] at h1 h2
  exact ⟨by simpa [Lean.Grind.Semiring.one_mul] using h1,
    by simpa [Lean.Grind.Semiring.one_mul] using h2⟩

/-- **Padding follows padding.** -/
theorem pad_pad (hL : TableLocal table tr tt pub) {r : Nat} (hr : r + 1 < tr.height tt)
    (ha : tr.cell tt r act = 0) : tr.cell tt (r + 1) act = 0 := by
  have h0 : r < tr.height tt := by omega
  have h := con (r := r) hL h0 mem_padPad
  simp only [cPadPad, eval_mul3, eval_sub, eval_c, eval_n, eval_k, eval_isTransition,
    nxt hr, ite_eq_right (show ¬ r + 1 = tr.height tt by omega)] at h
  rw [ha] at h
  grind

/-! ## Small sums in `Fp`, in `ℕ`

A field equation `a + b = c` (or `a + b + 1 = c`) between *small* values is the same equation in
`ℕ`; this is the only place the cast is done, so the row lemmas read as arithmetic. -/

theorem natSum2 {x y z : Fp} (h : x + y = z) (hz : z.toNat < P)
    (hb : x.toNat + y.toNat < P) : x.toNat + y.toNat = z.toNat := by
  have e : (((x.toNat + y.toNat : Nat)) : Fp) = z := by
    rw [ZkFormal.Near.natCast_add, ZkFormal.Near.natCast_eq, ZkFormal.Near.natCast_eq,
      Fp.ofNat_toNat, Fp.ofNat_toNat]
    exact h
  have := congrArg Fp.toNat e
  rw [ZkFormal.Near.toNat_natCast, Nat.mod_eq_of_lt hb] at this
  exact this

theorem natSum3 {x y z : Fp} (h : x + y + 1 = z)
    (hb : x.toNat + y.toNat + 1 < P) : x.toNat + y.toNat + 1 = z.toNat := by
  have e : (((x.toNat + y.toNat + 1 : Nat)) : Fp) = z := by
    rw [ZkFormal.Near.natCast_add, ZkFormal.Near.natCast_add, ZkFormal.Near.natCast_eq,
      ZkFormal.Near.natCast_eq, ZkFormal.Near.natCast_eq, Fp.ofNat_toNat, Fp.ofNat_toNat]
    exact h
  have := congrArg Fp.toNat e
  rw [ZkFormal.Near.toNat_natCast, Nat.mod_eq_of_lt hb] at this
  exact this

/-! ## Bounds

The two comparison constraints are stated as the field equations they are; turning them into
`Nat` inequalities needs the `PBR` 16-bit range checks of the columns involved (a bus obligation,
`Bookkeeping.pbrClaim`), because a field equation `a + b + 1 = c` only pins `a < c` once `a`, `b`,
`c` are known to be small.  Splitting it this way keeps the table's arithmetic and its soundness
argument separable. -/

/-- **`tgt + gTgt + 1 = rcpt`** (field form) on a row that resolves a promise index. -/
theorem tgt_gt (hL : TableLocal table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (ht : tr.cell tt r hasTgt = 1) :
    tr.cell tt r tgt + tr.cell tt r gTgt + 1 = tr.cell tt r rcpt := by
  have h := con (r := r) hL hr mem_tgtLt
  simp only [eval_mul, eval_sub, eval_add, eval_c, eval_k, Lean.Grind.Semiring.one_mul] at h
  rw [ht] at h
  grind

/-- **`tgt < rcpt`** as a `Nat`, from the field equation and the `PBR` 16-bit bounds of the
three columns.  This is the lemma the bookkeeping statement cites: once `tgt`, `gTgt`, `rcpt` are
16-bit, `tgt + gTgt + 1 = rcpt` in `Fp` is the same equation in `ℕ` and gives `tgt < rcpt`. -/
theorem tgt_lt (hL : TableLocal table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (ht : tr.cell tt r hasTgt = 1)
    (hb : (tr.cell tt r tgt).toNat + (tr.cell tt r gTgt).toNat + 1 < P) :
    (tr.cell tt r tgt).toNat < (tr.cell tt r rcpt).toNat := by
  have h := tgt_gt hL hr ht
  have hnat : (tr.cell tt r tgt).toNat + (tr.cell tt r gTgt).toNat + 1 =
      (tr.cell tt r rcpt).toNat :=
    natSum3 h hb
  omega

/-- **`tgt` is `0` when the call names no promise.** -/
theorem tgt_off (hL : TableLocal table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (ht : tr.cell tt r hasTgt = 0) : tr.cell tt r tgt = 0 := by
  have h := con (r := r) hL hr mem_tgtOff
  simp only [eval_mul, eval_sub, eval_c, eval_k] at h
  rw [ht] at h
  grind

/-- **`dep = 0` when the call has no dependency list.** -/
theorem dep_off (hL : TableLocal table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (hd : tr.cell tt r hasDep = 0) : tr.cell tt r dep = 0 := by
  have h := con (r := r) hL hr mem_depOff
  simp only [eval_mul, eval_sub, eval_c, eval_k] at h
  rw [hd] at h
  grind

/-- **`dep + gDep = 128`** (field form) on a row with a dependency list. -/
theorem dep_sum (hL : TableLocal table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (hd : tr.cell tt r hasDep = 1) : tr.cell tt r dep + tr.cell tt r gDep = 128 := by
  have h := con (r := r) hL hr mem_depLe
  simp only [eval_mul, eval_sub, eval_add, eval_c, eval_k, Lean.Grind.Semiring.one_mul] at h
  rw [hd] at h
  grind

/-- **`dep ≤ 128`**: from `dep + gDep = 128` in `Fp` and the 16-bit bound making it a `ℕ`
equation, `dep ≤ 128`. -/
theorem dep_le (hL : TableLocal table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (hd : tr.cell tt r hasDep = 1)
    (hb : (tr.cell tt r dep).toNat + (tr.cell tt r gDep).toNat < P) :
    (tr.cell tt r dep).toNat ≤ 128 := by
  have h := dep_sum hL hr hd
  have hnat : (tr.cell tt r dep).toNat + (tr.cell tt r gDep).toNat = 128 := by
    have e : (((tr.cell tt r dep).toNat + (tr.cell tt r gDep).toNat : Nat) : Fp) =
        ((128 : Nat) : Fp) := by
      rw [ZkFormal.Near.natCast_add, ZkFormal.Near.natCast_eq, ZkFormal.Near.natCast_eq,
        Fp.ofNat_toNat, Fp.ofNat_toNat]
      exact h
    have h2 := congrArg Fp.toNat e
    rw [ZkFormal.Near.toNat_natCast, Nat.mod_eq_of_lt hb] at h2
    have h128 : Fp.toNat ((128 : Nat) : Fp) = 128 := by decide
    rw [h128] at h2
    exact h2
  omega

/-- **The data-id count is the class's** (`hasDep = 0`), or the dependency count
(`hasDep = 1`).  This is `thenDataIdsH` / `dataCount + 1` restated. -/
theorem data_of (hL : TableLocal table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (hd : tr.cell tt r hasDep = 0) : tr.cell tt r addD = tr.cell tt r dadd := by
  have h := con (r := r) hL hr mem_dataOff
  simp only [eval_mul, eval_sub, eval_c, eval_k] at h
  rw [hd] at h
  grind

theorem data_on (hL : TableLocal table tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (hd : tr.cell tt r hasDep = 1) : tr.cell tt r addD = tr.cell tt r dep := by
  have h := con (r := r) hL hr mem_dataOn
  simp only [eval_mul, eval_sub, eval_c, eval_k] at h
  rw [hd] at h
  grind

end ZkFormal.PQ.Receipt
