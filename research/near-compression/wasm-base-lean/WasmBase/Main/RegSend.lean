import WasmBase.Main.HostChipBits
import WasmBase.Main.RegFacts
import WasmBase.Main.RegWalk
/-!
# WasmBase.Main.RegSend — the R16 send-side bound for `wasmBaseRegAir`

`regLenAgree_group` (`Main/RegWalk.lean`) takes

```
hsend : ∀ o ∈ occs (wasmBaseRegAir nloc ngl) tr pub, o.2.1 = true → o.2.2.2 ≤ 1
```

as a hypothesis, and reaches it through `reg_gap_lt → reg_r16_query_16bit → lookup_sound`.  This file
discharges it, so `regLenAgree_group` becomes unconditional.

## The bound has to be per-bus, and R16 is the bus that matters

`HOSTO`'s two interactions are counted with a *free* column `mult` (`HostO.table.constraints = []`,
`hosto_no_count_bound`), so the unrestricted statement "every send of the trace has count ≤ 1" is
**false** for any host trace.  `Bus.lookup_sound` already takes the bus-restricted form
`o.1 = b → o.2.1 = true → count ≤ 1`, and `RegWalk` applies it with `b = busR16`.  So the statement
proved here is

```
∀ o ∈ occs (wasmBaseRegAir …) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1
```

which is exactly `lookup_sound`'s `hsend` at bus 3 (`reg_hsend_r16`).

## Where the pieces come from

* **tables 0–21**: `occ_bits_of` (`Main/Exec.lean`) was split out of the base `occ_bits` so that it
  needs only *row constraints*, never the base AIR's bus balance.  Its conclusion covers every send,
  hence every R16 send; `reg_base_constr` supplies the constraints from `Holds (wasmBaseRegAir …)`,
  because tables 0–21 of the REG AIR are literally `wasmBaseAir`'s.
* **HOST (22)**: every R16 query is counted `act` or some `pf j`; both are bits.
* **HOSTO (23), HOSTT (24)**: no R16 interaction at all.
* **HOSTB (25)**: R16 queries are counted `memCnt = act·(1−dir)·(1−reg)`, or its un-folded form
  `act·(1−reg)`; `act`, `dir`, `reg` are its bits.
* **REG (26)**: six R16 queries, counted `act·fresh`, `act·fresh`, `act·(1−kind)`, `act`, `act`, `act`.
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## `wasmBaseRegAir`'s base tables -/

/-- **The base tables' row constraints on a REG trace.**  Tables 0–21 of `wasmBaseRegAir` are
`wasmBaseAir`'s tables, so `Holds` of the REG AIR gives the base AIR's constraints verbatim — which is
why `occ_bits_of` (stated against constraints, not `Holds`) applies here. -/
theorem reg_base_constr {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) :
    ∀ t (ht : t < (wasmBaseAir nloc ngl).tables.length) r, r < tr.height t →
      ∀ e ∈ ((wasmBaseAir nloc ngl).tables[t]'ht).constraints,
        e.eval (natRow (rowNat tr t r) (tr.row pub t r)) = 0 := by
  intro t ht r hr e he
  have h22 : t < 22 := by simpa [air_len] using ht
  have hreg : (wasmBaseRegAir nloc ngl).tables[t]'(by rw [reg_air_len]; omega) =
      (wasmBaseAir nloc ngl).tables[t]'ht := by
    rw [reg_air_get nloc ngl t (by omega), host_air_get nloc ngl t h22]
  have he' : e ∈ ((wasmBaseRegAir nloc ngl).tables[t]'(by rw [reg_air_len]; omega)).constraints := by
    rw [hreg]; exact he
  exact table_constr H (by rw [reg_air_len]; omega) hr e he'

/-- A table membership in `wasmBaseHostAir`'s table `t < 22` is one in `wasmBaseAir`'s. -/
theorem reg_hi_base {nloc ngl : Nat} {t : Nat} (ht : t < 22) {i : Inter}
    (hi : i ∈ ((wasmBaseHostAir nloc ngl).tables[t]'(by rw [host_air_len]; omega)).inters) :
    i ∈ ((wasmBaseAir nloc ngl).tables[t]'(by simp [air_len]; exact ht)).inters := by
  rw [← host_air_get nloc ngl t ht]
  exact hi

/-- An occurrence of the base AIR, built from a REG trace's base table. -/
theorem occ_base_of_reg {nloc ngl : Nat} {tr : Trace} {pub : List F} {t r : Nat}
    (ht : t < 22) (hr : r < tr.height t) {i : Inter}
    (hi : i ∈ ((wasmBaseAir nloc ngl).tables[t]'(by simp [air_len]; exact ht)).inters) :
    (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat) ∈
      occs (wasmBaseAir nloc ngl) tr pub :=
  mem_occs.mpr ⟨t, by simp [air_len]; exact ht, r, hr, i, hi, rfl⟩

/-- **Every send in tables 0–21 of a REG trace has count ≤ 1.**  `occ_bits_of` at the REG trace's own
base-table constraints. -/
theorem occ_bits_reg_base {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub)
    (hcounts : ∀ t, 1 ≤ t → t ≤ 14 → ∀ r, r < tr.height t → ∀ i ∈ (chipT t).inters,
      (i.count.eval (tr.row pub t r)).toNat ≤ 1) :
    ∀ o ∈ occs (wasmBaseAir nloc ngl) tr pub,
      (o.2.1 = true ∨ o.1 = busState ∨ o.1 = busStk) → o.2.2.2 ≤ 1 :=
  occ_bits_of hpub hcounts (reg_base_constr H)

/-- **An R16 send in tables 0–21 of a REG trace has count ≤ 1.** -/
theorem reg_send_base {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub)
    (hcounts : ∀ t, 1 ≤ t → t ≤ 14 → ∀ r, r < tr.height t → ∀ i ∈ (chipT t).inters,
      (i.count.eval (tr.row pub t r)).toNat ≤ 1)
    {t r : Nat} (ht : t < 22) (hr : r < tr.height t) {i : Inter}
    (hi : i ∈ ((wasmBaseHostAir nloc ngl).tables[t]'(by rw [host_air_len]; omega)).inters)
    (hs : i.send = true) :
    (i.count.eval (tr.row pub t r)).toNat ≤ 1 :=
  occ_bits_reg_base H hpub hcounts _
    (occ_base_of_reg ht hr (reg_hi_base ht hi)) (Or.inl hs)

/-! ## The instruction tables' counts, on a REG trace

`ChipFacts` (`Main/Exec.lean`) bundles this for `wasmBaseAir`.  On a REG trace the same tables occur at
the same indices, and each chip's `*_counts_of` lemma (`Main/Row*`) needs only that table's row
constraints — which `Holds (wasmBaseRegAir …)` supplies.  So the counts are derivable here without
assuming `ChipFacts`, which is what makes the final bound unconditional. -/

/-- Index `t ∈ [1, 14]` of `wasmBaseRegAir` is `chipT t`. -/
theorem reg_air_chipT (nloc ngl t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 14) :
    (wasmBaseRegAir nloc ngl).tables[t]'(by rw [reg_air_len]; omega) = chipT t := by
  rw [reg_air_get nloc ngl t (by omega), host_air_get nloc ngl t (by omega)]
  exact chipT_eq nloc ngl t h1 h9

/-- **The instruction tables' count bits on a REG trace.** -/
theorem reg_chip_counts {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) :
    ∀ t, 1 ≤ t → t ≤ 14 → ∀ r, r < tr.height t → ∀ i ∈ (chipT t).inters,
      (i.count.eval (tr.row pub t r)).toNat ≤ 1 := by
  intro t h1 h9 r hr i hi
  have ht : t < (wasmBaseRegAir nloc ngl).tables.length := by rw [reg_air_len]; omega
  have hcon := table_constr_eq H ht (chipT t) (reg_air_chipT nloc ngl t h1 h9) hr
  rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨
    t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact ret_counts_of hcon i hi

/-! ## Occurrences of `wasmBaseRegAir`, by table -/

/-- **An occurrence of `wasmBaseRegAir` lies in one of its 27 tables.**  Tables 0–25 are
`wasmBaseHostAir`'s by index (`reg_air_get`); table 26 is `REG`. -/
theorem occ_table_reg {nloc ngl : Nat} {tr : Trace} {pub : List F} {o : Occ}
    (ho : o ∈ occs (wasmBaseRegAir nloc ngl) tr pub) :
    (∃ t, ∃ ht : t < 26, ∃ r, r < tr.height t ∧
      ∃ i ∈ ((wasmBaseHostAir nloc ngl).tables[t]'(by rw [host_air_len]; exact ht)).inters,
        o = (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat)) ∨
    (∃ r, r < tr.height 26 ∧ ∃ i ∈ Reg.table.inters,
        o = (i.bus, i.send, i.msg.map (·.eval (tr.row pub 26 r)),
          (i.count.eval (tr.row pub 26 r)).toNat)) := by
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  have ht27 : t < 27 := by simpa [reg_air_len] using ht
  rcases (show t < 26 ∨ t = 26 by omega) with h | rfl
  · left
    refine ⟨t, h, r, hr, i, ?_, rfl⟩
    rwa [reg_air_get nloc ngl t h] at hi
  · right
    refine ⟨r, hr, i, ?_, rfl⟩
    rwa [reg_air_26] at hi

/-! ## Row bits on the host tables, re-derived on the REG AIR -/

/-- The constraints of `HostB` vanish on a REG trace's HOSTB row. -/
theorem reg_hostb_constr {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 25) :
    ∀ e ∈ HostB.table.constraints, e.eval (natRow (rowNat tr 25 r) (tr.row pub 25 r)) = 0 := by
  have ht : 25 < (wasmBaseRegAir nloc ngl).tables.length := by rw [reg_air_len]; omega
  exact table_constr_eq H ht HostB.table (reg_air_25 nloc ngl) hr

/-- A `bool`-constrained column of `HostB` is a bit on a REG trace's HOSTB row. -/
theorem reg_hostb_bit {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 25)
    {c : Nat} (hc : Chips.bool (v c) ∈ HostB.table.constraints) :
    rowNat tr 25 r c = 0 ∨ rowNat tr 25 r c = 1 := by
  have hb := reg_hostb_constr H hr (Chips.bool (v c)) hc
  simp only [Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', natRow] at hb
  exact bool_nat (rowNat_lt tr 25 r c) hb

/-- `act` is a bit on a HOST row of a REG trace. -/
theorem reg_host_act_le {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22) :
    rowNat tr 22 r Host.act ≤ 1 := by
  show rowNat tr 22 r 5 ≤ 1
  have hb := reg_air_host_constr H hr Host.cAct host_cAct_mem
  simp only [Host.cAct, Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', Host.act, natRow] at hb
  rcases bool_nat (rowNat_lt tr 22 r 5) hb with h | h <;> omega

/-- `pf j` is a bit on a HOST row of a REG trace. -/
theorem reg_host_pf_le {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22)
    {j : Nat} (hj : j < Host.nArgs) : rowNat tr 22 r (Host.pf j) ≤ 1 := by
  have hb := reg_air_host_constr H hr (Host.cP j) (host_cP_mem j hj)
  simp only [Host.cP, Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', Host.pf, natRow] at hb
  rcases bool_nat (rowNat_lt tr 22 r (Host.pf j)) hb with h | h <;> omega

/-- **`memCnt` is a bit on a REG trace's HOSTB row.** -/
theorem reg_hostb_memCnt_le {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 25) :
    (HostB.memCnt.eval (tr.row pub 25 r)).toNat ≤ 1 := by
  have hact := reg_hostb_bit (H := H) hr (c := HostB.act) (by simp [HostB.table, HostB.constraints, HostB.cAct])
  have hdir := reg_hostb_bit (H := H) hr (c := HostB.dir) (by simp [HostB.table, HostB.constraints, HostB.cDir])
  have hreg := reg_hostb_bit (H := H) hr (c := HostB.reg) (by simp [HostB.table, HostB.constraints, HostB.cReg])
  have e : (HostB.memCnt.eval (tr.row pub 25 r)).toNat =
      (rowNat tr 25 r HostB.act * (1 - rowNat tr 25 r HostB.dir) *
        (1 - rowNat tr 25 r HostB.reg)) := by
    simp only [HostB.memCnt, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat',
      Expr.eval_col, Trace.row]
    rw [cell_cast tr 25 r HostB.act, cell_cast tr 25 r HostB.dir, cell_cast tr 25 r HostB.reg]
    rcases hact with h | h <;> rcases hdir with h' | h' <;> rcases hreg with h'' | h'' <;>
      rw [h, h', h''] <;> decide
  rw [e]
  rcases hact with h | h <;> rcases hdir with h' | h' <;> rcases hreg with h'' | h'' <;>
    rw [h, h', h''] <;> decide

/-- Same, in the un-folded shape `act · (1 − reg)` that `HOSTB`'s `r16`/`byteQ` queries use. -/
theorem reg_hostb_act_one_minus_reg_le {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 25) :
    ((v HostB.act * (1 - v HostB.reg)).eval (tr.row pub 25 r)).toNat ≤ 1 := by
  have hact := reg_hostb_bit (H := H) hr (c := HostB.act) (by simp [HostB.table, HostB.constraints, HostB.cAct])
  have hreg := reg_hostb_bit (H := H) hr (c := HostB.reg) (by simp [HostB.table, HostB.constraints, HostB.cReg])
  have e : ((v HostB.act * (1 - v HostB.reg)).eval (tr.row pub 25 r)).toNat =
      (rowNat tr 25 r HostB.act * (1 - rowNat tr 25 r HostB.reg)) := by
    simp only [Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval_col,
      Trace.row]
    rw [cell_cast tr 25 r HostB.act, cell_cast tr 25 r HostB.reg]
    rcases hact with h | h <;> rcases hreg with h' | h' <;> rw [h, h'] <;> decide
  rw [e]
  rcases hact with h | h <;> rcases hreg with h' | h' <;> rw [h, h'] <;> decide

/-! ## The count shapes of the R16 queries -/

/-- **`HOST`'s R16 counts are `act` or some `pf j`.** -/
theorem host_r16_cases {i : Inter} (hi : i ∈ Host.table.inters) (hb : i.bus = busR16) :
    i.count = Expr.col Host.act ∨ ∃ j, j < Host.nArgs ∧ i.count = Expr.col (Host.pf j) := by
  have hall : Host.table.inters.all (fun j => decide (j.bus = busR16 →
      j.count = Expr.col Host.act ∨
        ∃ k, k < Host.nArgs ∧ j.count = Expr.col (Host.pf k))) = true := by
    decide
  exact of_decide_eq_true (List.all_eq_true.mp hall i hi) hb

/-- **`HOSTB`'s R16 counts are `memCnt` or its un-folded `act·(1−reg)` form.** -/
theorem hostb_r16_cases {i : Inter} (hi : i ∈ HostB.table.inters) (hb : i.bus = busR16) :
    i.count = HostB.memCnt ∨ i.count = v HostB.act * (1 - v HostB.reg) := by
  have hall : HostB.table.inters.all (fun j => decide (j.bus = busR16 →
      j.count = HostB.memCnt ∨ j.count = v HostB.act * (1 - v HostB.reg))) = true := by
    decide
  exact of_decide_eq_true (List.all_eq_true.mp hall i hi) hb

/-- **REG's R16 counts are `act·fresh`, `act·(1−kind)` or `act`.** -/
theorem reg_r16_cases {i : Inter} (hi : i ∈ Reg.table.inters) (hb : i.bus = busR16) :
    i.count = v Reg.act * v Reg.fresh ∨ i.count = v Reg.act * Reg.isB ∨
      i.count = v Reg.act := by
  have hall : Reg.table.inters.all (fun j => decide (j.bus = busR16 →
      j.count = v Reg.act * v Reg.fresh ∨ j.count = v Reg.act * Reg.isB ∨
        j.count = v Reg.act)) = true := by
    decide
  exact of_decide_eq_true (List.all_eq_true.mp hall i hi) hb

/-- `HOSTO` has no R16 send. -/
theorem hosto_no_r16 :
    HostO.table.inters.all (fun i => decide (i.bus ≠ busR16 ∨ i.send = false)) = true := by decide

/-- `HOSTT` has no R16 send. -/
theorem hostT_no_r16 :
    HostTab.table.inters.all (fun i => decide (i.bus ≠ busR16 ∨ i.send = false)) = true := by decide

/-- No R16 send in a table whose every R16 interaction is a receive. -/
theorem no_r16_send {T : Table}
    (h : T.inters.all (fun i => decide (i.bus ≠ busR16 ∨ i.send = false)) = true)
    {i : Inter} (hi : i ∈ T.inters) (hb : i.bus = busR16) (hs : i.send = true) : False := by
  have h' := List.all_eq_true.mp h i hi
  simp only [decide_eq_true_eq, ne_eq] at h'
  rcases h' with h' | h'
  · exact h' hb
  · rw [hs] at h'; exact Bool.noConfusion h'

/-! ## Evaluating the count expressions on a REG row -/

/-- `act`, `fresh` are bits, so `act·fresh ≤ 1` on a REG row. -/
theorem reg_act_fresh_le {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26) :
    ((v Reg.act * v Reg.fresh).eval (tr.row pub 26 r)).toNat ≤ 1 := by
  obtain ⟨hA, -, -, -, hF⟩ := reg_row_bits H hr
  have hact : rowNat tr 26 r Reg.act = 0 ∨ rowNat tr 26 r Reg.act = 1 :=
    bool_nat (rowNat_lt tr 26 r Reg.act) hA
  have hfresh : rowNat tr 26 r Reg.fresh = 0 ∨ rowNat tr 26 r Reg.fresh = 1 :=
    bool_nat (rowNat_lt tr 26 r Reg.fresh) hF
  have e : ((v Reg.act * v Reg.fresh).eval (tr.row pub 26 r)).toNat =
      (rowNat tr 26 r Reg.act * rowNat tr 26 r Reg.fresh) := by
    simp only [Chips.v, Expr.eval_mul', Expr.eval_col, Trace.row]
    rw [cell_cast tr 26 r Reg.act, cell_cast tr 26 r Reg.fresh]
    rcases hact with h | h <;> rcases hfresh with h' | h' <;> rw [h, h'] <;> decide
  rw [e]
  rcases hact with h | h <;> rcases hfresh with h' | h' <;> rw [h, h'] <;> decide

/-- `act·(1−kind) ≤ 1` on a REG row. -/
theorem reg_act_isB_le {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26) :
    ((v Reg.act * Reg.isB).eval (tr.row pub 26 r)).toNat ≤ 1 := by
  obtain ⟨hA, hK, -, -, -⟩ := reg_row_bits H hr
  have hact : rowNat tr 26 r Reg.act = 0 ∨ rowNat tr 26 r Reg.act = 1 :=
    bool_nat (rowNat_lt tr 26 r Reg.act) hA
  have hkind : rowNat tr 26 r Reg.kind = 0 ∨ rowNat tr 26 r Reg.kind = 1 :=
    bool_nat (rowNat_lt tr 26 r Reg.kind) hK
  have e : ((v Reg.act * Reg.isB).eval (tr.row pub 26 r)).toNat =
      (rowNat tr 26 r Reg.act * (1 - rowNat tr 26 r Reg.kind)) := by
    simp only [Reg.isB, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat',
      Expr.eval_col, Trace.row]
    rw [cell_cast tr 26 r Reg.act, cell_cast tr 26 r Reg.kind]
    rcases hact with h | h <;> rcases hkind with h' | h' <;> rw [h, h'] <;> decide
  rw [e]
  rcases hact with h | h <;> rcases hkind with h' | h' <;> rw [h, h'] <;> decide

/-- `act ≤ 1` on a REG row. -/
theorem reg_act_le {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26) :
    ((v Reg.act).eval (tr.row pub 26 r)).toNat ≤ 1 := by
  obtain ⟨hA, -, -, -, -⟩ := reg_row_bits H hr
  have hact : rowNat tr 26 r Reg.act = 0 ∨ rowNat tr 26 r Reg.act = 1 :=
    bool_nat (rowNat_lt tr 26 r Reg.act) hA
  have e : ((v Reg.act).eval (tr.row pub 26 r)).toNat = rowNat tr 26 r Reg.act := by
    simp only [Chips.v, Expr.eval_col, Trace.row, rowNat, Fp.cast_toNat]
  rw [e]
  rcases hact with h | h <;> omega

/-! ## The host tables' R16 sends -/

/-- **Every R16 send of the host tables of a REG trace has count ≤ 1.** -/
theorem reg_send_host {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr)
    (t : Nat) (ht26 : t < 26) (ht : t = 22 ∨ t = 23 ∨ t = 24 ∨ t = 25) :
    ∀ r, r < tr.height t →
      ∀ i ∈ ((wasmBaseHostAir nloc ngl).tables[t]'(by rw [host_air_len]; exact ht26)).inters,
        i.bus = busR16 → i.send = true → (i.count.eval (tr.row pub t r)).toNat ≤ 1 := by
  intro r hr i hi hb hs
  rcases ht with rfl | rfl | rfl | rfl
  · -- HOST (22): the count is `act` or some `pf j`
    rw [host_air_22 nloc ngl] at hi
    have eact : ((Expr.col Host.act).eval (tr.row pub 22 r)).toNat = rowNat tr 22 r Host.act := by
      simp only [Expr.eval_col, Trace.row, rowNat, Fp.cast_toNat]
    rcases host_r16_cases hi hb with h | ⟨j, hj, h⟩
    · rw [h, eact]; exact reg_host_act_le H hr
    · rw [h]
      simp only [Expr.eval_col, Trace.row, rowNat, Fp.cast_toNat]
      exact reg_host_pf_le H hr hj
  · -- HOSTO (23): no R16 send
    rw [host_air_23 nloc ngl] at hi
    exact absurd (no_r16_send hosto_no_r16 hi hb hs) not_false
  · -- HOSTT (24): no R16 send
    rw [host_air_24 nloc ngl] at hi
    exact absurd (no_r16_send hostT_no_r16 hi hb hs) not_false
  · -- HOSTB (25)
    rw [host_air_25 nloc ngl] at hi
    rcases hostb_r16_cases hi hb with h | h
    · rw [h]; exact reg_hostb_memCnt_le H hr
    · rw [h]; exact reg_hostb_act_one_minus_reg_le H hr

/-! ## REG's own R16 sends -/

/-- **Every R16 send of REG has count ≤ 1.** -/
theorem reg_r16_counts {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 26) :
    ∀ i ∈ Reg.table.inters, i.bus = busR16 → i.send = true →
      (i.count.eval (tr.row pub 26 r)).toNat ≤ 1 := by
  intro i hi hb _
  rcases reg_r16_cases hi hb with h | h | h
  · rw [h]; exact reg_act_fresh_le H hr
  · rw [h]; exact reg_act_isB_le H hr
  · rw [h]; exact reg_act_le H hr

/-! ## The bound -/

/-- **The R16 send-side bound for `wasmBaseRegAir`.**  This is the hypothesis `regLenAgree_group`
consumes (via `reg_gap_lt → reg_r16_query_16bit → lookup_sound`), proved from `Holds` alone: the
per-chip count bits come from `reg_chip_counts`.

It is stated **per bus** because the unrestricted form is false: `HOSTO`'s free column `mult`
(`hosto_no_count_bound`) counts its `HOSTR` send. -/
theorem reg_hsend_r16 {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub) :
    ∀ o ∈ occs (wasmBaseRegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1 := by
  intro o ho hb hs
  rcases occ_table_reg ho with ⟨t, ht, r, hr, i, hi, rfl⟩ | ⟨r, hr, i, hi, rfl⟩
  · rcases (show t < 22 ∨ t = 22 ∨ t = 23 ∨ t = 24 ∨ t = 25 by omega) with h | rfl | rfl | rfl | rfl
    · exact reg_send_base H hpub (reg_chip_counts H) h hr hi hs
    · exact reg_send_host H 22 (by decide) (Or.inl rfl) r hr i hi hb hs
    · exact reg_send_host H 23 (by decide) (Or.inr (Or.inl rfl)) r hr i hi hb hs
    · exact reg_send_host H 24 (by decide) (Or.inr (Or.inr (Or.inl rfl))) r hr i hi hb hs
    · exact reg_send_host H 25 (by decide) (Or.inr (Or.inr (Or.inr rfl))) r hr i hi hb hs
  · exact reg_r16_counts H hr i hi hb hs

/-! ## The unconditional group theorem -/

/-- **`regLenAgree_group` without the `hsend` hypothesis.**  `reg_hsend_r16` discharges it from
`Holds` alone, so the group walk's conclusion is now a consequence of the AIR relation (given the
public-input layout and the group's start/key-domain data).

The remaining hypotheses are the group's start (`f = 1`, `kind = 0`), its key-domain bounds
(`rid ≤ 99`, `pos < 2^24`), and the activity of its length row — all of them data about the group
being walked, not AIR facts. -/
theorem regLenAgree_group_of_holds {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseRegAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub)
    {r0 : Nat} (hr0 : r0 < tr.height 26)
    (hf : rowNat tr 26 r0 Reg.f = 1) (hk : rowNat tr 26 r0 Reg.kind = 0)
    (hrid0 : rowNat tr 26 r0 Reg.rid ≤ 99) (hpos0 : rowNat tr 26 r0 Reg.pos < 16777216)
    (hactL' : ∀ n, n ≤ rowNat tr 26 r0 Reg.blen → r0 + n < tr.height 26 →
      rowNat tr 26 (r0 + n) Reg.kind = 1 → rowNat tr 26 (r0 + n) Reg.act = 1) :
    let L := rowNat tr 26 r0 Reg.blen
    r0 + L < tr.height 26 ∧
      rowNat tr 26 (r0 + L) Reg.kind = 1 ∧
      rowProd Reg.table tr pub 26 (r0 + L) =
        [Register.lenMsg (rowNat tr 26 r0 Reg.rid) L (rowNat tr 26 r0 Reg.ts)] ∧
      (∀ i, i < L → rowProd Reg.table tr pub 26 (r0 + i) =
        [Register.byteMsg (rowNat tr 26 r0 Reg.rid) i (rowNat tr 26 (r0 + i) Reg.bv)
          (rowNat tr 26 r0 Reg.ts)]) :=
  regLenAgree_group H (reg_hsend_r16 H hpub) hr0 hf hk hrid0 hpos0 hactL'

end WasmBase
