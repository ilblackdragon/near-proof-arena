import WasmBase.Main.RegSend
import WasmBase.Main.RegWalkG
import WasmBase.Main.RegMemLink
/-!
# WasmBase.Main.RegSendM2 — the R16 send bound for `wasmBaseIfRegAir` and `wasmBaseM2Air`

`Main/RegSend.lean` proves the per-bus R16 send bound for `wasmBaseRegAir`.  This file proves it for
the two E2E AIRs

```
wasmBaseIfRegAir = wasmBaseAir (0–21) ++ [HOST', HOSTO, HOSTT, HOSTB, IF, REG']
wasmBaseM2Air    = wasmBaseAir (0–21) ++ [HOST', HOSTO, HOSTT, HOSTB, IF, REG-C, CONV, UNREACH]
```

and uses it to

* discharge the `hsend` hypothesis of the generic group walk (`Main/RegWalkG.lean`): the group
  theorem `regLenAgree_groupG`, the gap bound `regG_gap_lt` and `pos < len` become consequences of
  `Holds` (plus the public-input layout `PubOK` and the group's start/key-domain data);
* turn `regw_time_lt` (`Main/RegMemLink.lean`) into a theorem about `Holds`: on an active REG'/REG-C
  write row, `mtp < ts` (`ifreg_regw_mtp_lt_ts`, `m2_regw_mtp_lt_ts`), given the domain bounds
  `ts, mtp < 2^29` as explicit hypotheses.

## How the bound is proved

* **Tables 0–21** are `wasmBaseAir`'s by index, so `occ_bits_of` (`Main/Exec.lean`) applies to the
  trace's own base-table constraints, exactly as in `RegSend` (`base_send_le_of_prefix`).
* **Tables ≥ 22** are handled by one generic, decidable check instead of per-table case analysis:
  `BitE bs e` says syntactically that `e` is built from the expressions `bs` by products and `1 − ·`;
  `R16Ok T` says that some list `bs` has every `bool b` among `T`'s constraints and every R16 send of
  `T` is counted by a `BitE bs` expression.  `r16_le_of_ok` turns `R16Ok T` into "every R16 send of
  table `t` has count ≤ 1" on a satisfied trace.  The per-table witnesses:

| table | R16 send counts | `bs` |
|---|---|---|
| HOST' (22) | `act`, `pf j` (HOST's, the bus-211 send is not R16) | `act`, `pf 0 … pf 8` |
| HOSTO (23), HOSTT (24) | none | `[]` |
| HOSTB (25) | `act·(1−dir)·(1−reg)`, `act·(1−reg)` | `act, dir, reg` |
| IF (26) | `f_if` (its `timeChk`) | `f_if` |
| REG' / REG-C (27) | `act·fresh`, `act·(1−kind)`, `act`, `act·(1−kind)·wr`, `act·kind·wr` | `act, kind, fresh, wr` |
| CONV (28) | `f_wrap + f_extu + f_exts` (`bool act` is a constraint), `f_exts` | `act, f_exts` |
| UNREACH (29) | none | `[]` |

The check is `decide`d per table, so it is against the tables' actual interaction lists.
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## Syntactic bit expressions -/

/-- `e` is built from `bs` by products and `1 − ·` (or is one of `bs` itself). -/
def BitE (bs : List Expr) : Expr → Bool
  | .mul a b => bs.any (fun x => decide (x = .mul a b)) || (BitE bs a && BitE bs b)
  | .sub a b => bs.any (fun x => decide (x = .sub a b)) || (decide (a = .c 1) && BitE bs b)
  | e => bs.any (fun x => decide (x = e))

theorem bitE_mem {bs : List Expr} {e : Expr} (h : bs.any (fun x => decide (x = e)) = true) :
    e ∈ bs := by
  obtain ⟨x, hx, he⟩ := List.any_eq_true.mp h
  rw [decide_eq_true_eq] at he
  exact he ▸ hx

/-- **Soundness of `BitE`**: if every `b ∈ bs` evaluates to a bit, so does every `BitE bs` expression. -/
theorem bitE_sound (bs : List Expr) (rw : Row)
    (hbs : ∀ b ∈ bs, b.eval rw = 0 ∨ b.eval rw = 1) :
    ∀ e, BitE bs e = true → e.eval rw = 0 ∨ e.eval rw = 1
  | .mul a b, h => by
      simp only [BitE, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨ha, hb⟩
      · exact hbs _ (bitE_mem h)
      · have h1 := bitE_sound bs rw hbs a ha
        have h2 := bitE_sound bs rw hbs b hb
        simp only [Expr.eval]
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> grind
  | .sub a b, h => by
      simp only [BitE, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with h | ⟨rfl, hb⟩
      · exact hbs _ (bitE_mem h)
      · have h2 := bitE_sound bs rw hbs b hb
        simp only [Expr.eval, cast_one]
        rcases h2 with h2 | h2 <;> rw [h2] <;> grind
  | .c n, h => hbs _ (bitE_mem h)
  | .col i, h => hbs _ (bitE_mem h)
  | .nxt i, h => hbs _ (bitE_mem h)
  | .pub i, h => hbs _ (bitE_mem h)
  | .first, h => hbs _ (bitE_mem h)
  | .last, h => hbs _ (bitE_mem h)
  | .trans, h => hbs _ (bitE_mem h)
  | .add a b, h => hbs _ (bitE_mem h)

theorem toNat_le_one_of_bit {x : F} (h : x = 0 ∨ x = 1) : x.toNat ≤ 1 := by
  rcases h with h | h <;> rw [h] <;> decide

/-! ## The per-table check -/

/-- The bit columns `bs` are `bool`-constrained in `T`. -/
def BitsOk (T : Table) (bs : List Expr) : Bool :=
  bs.all (fun b => T.constraints.any (fun c => decide (c = bool b)))

/-- Every R16 send of `T` is counted by a `BitE bs` expression. -/
def R16CountsOk (T : Table) (bs : List Expr) : Bool :=
  T.inters.all (fun i => decide (i.bus ≠ busR16) || !i.send || BitE bs i.count)

/-- **A table whose R16 send counts are syntactically bits.** -/
def R16Ok (T : Table) : Prop := ∃ bs, BitsOk T bs = true ∧ R16CountsOk T bs = true

/-- **`R16Ok` gives the bound on a satisfied trace.** -/
theorem r16_le_of_ok {A : Air} {pub : List F} {tr : Trace} (H : Holds A pub tr) {t : Nat}
    (ht : t < A.tables.length) (hok : R16Ok (A.tables[t]'ht)) {r : Nat} (hr : r < tr.height t)
    {i : Inter} (hi : i ∈ (A.tables[t]'ht).inters) (hb : i.bus = busR16) (hs : i.send = true) :
    (i.count.eval (tr.row pub t r)).toNat ≤ 1 := by
  obtain ⟨bs, hbits, hcnt⟩ := hok
  apply toNat_le_one_of_bit
  refine bitE_sound bs _ ?_ i.count ?_
  · intro b hb'
    have hc := List.all_eq_true.mp hbits b hb'
    obtain ⟨c, hcm, hce⟩ := List.any_eq_true.mp hc
    rw [decide_eq_true_eq] at hce
    subst hce
    have h0 := H.constr t ht r hr _ hcm
    simp only [Chips.bool, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', cast_one] at h0
    exact bool_cases h0
  · have hc := List.all_eq_true.mp hcnt i hi
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
    rcases hc with (hc | hc) | hc
    · exact absurd hb hc
    · rw [hs] at hc; exact absurd hc (by decide)
    · exact hc

/-! ## The witnesses for the tail tables -/

theorem hostR_r16ok : R16Ok HostR.table :=
  ⟨v Host.act :: (List.range Host.nArgs).map (fun j => v (Host.pf j)), by decide +kernel,
    by decide +kernel⟩

theorem hostO_r16ok : R16Ok HostO.table := ⟨[], by decide +kernel, by decide +kernel⟩

theorem hostTab_r16ok : R16Ok HostTab.table := ⟨[], by decide +kernel, by decide +kernel⟩

theorem hostB_r16ok : R16Ok HostB.table :=
  ⟨[v HostB.act, v HostB.dir, v HostB.reg], by decide +kernel, by decide +kernel⟩

theorem ifc_r16ok : R16Ok IfC.table := ⟨[v IfC.fIf], by decide +kernel, by decide +kernel⟩

theorem regw_r16ok : R16Ok RegW.table :=
  ⟨[v Reg.act, v Reg.kind, v Reg.fresh, v RegW.wr], by decide +kernel, by decide +kernel⟩

theorem regc_r16ok : R16Ok RegC.table :=
  ⟨[v Reg.act, v Reg.kind, v Reg.fresh, v RegW.wr], by decide +kernel, by decide +kernel⟩

theorem conv_r16ok : R16Ok Conv.table := ⟨[Conv.act, v Conv.fExtS], by decide +kernel, by decide +kernel⟩

theorem unreach_r16ok : R16Ok Unreach.table := ⟨[], by decide +kernel, by decide +kernel⟩

/-! ## The base tables -/

/-- **Every send of a base table (index `< 22`) has count ≤ 1**, for any AIR whose first 22 tables
are `wasmBaseAir`'s: `occ_bits_of` at the trace's own base-table constraints. -/
theorem base_send_le_of_prefix {X : Ctx} {A : Air} {nloc ngl : Nat} {tail : List Table}
    {pub : List F} {tr : Trace}
    (hA : A.tables = (wasmBaseAir nloc ngl).tables ++ tail)
    (H : Holds A pub tr) (hpub : PubOK X nloc ngl pub)
    {t : Nat} (ht : t < A.tables.length) (h22 : t < 22) {r : Nat} (hr : r < tr.height t)
    {i : Inter} (hi : i ∈ (A.tables[t]'ht).inters) (hs : i.send = true) :
    (i.count.eval (tr.row pub t r)).toNat ≤ 1 := by
  have hget : ∀ t (ht : t < A.tables.length) (h22 : t < 22),
      A.tables[t]'ht = (wasmBaseAir nloc ngl).tables[t]'(by rw [air_len]; exact h22) := by
    intro t ht h22
    simp only [hA]
    rw [List.getElem_append_left]
  have hcon : ∀ t (ht : t < (wasmBaseAir nloc ngl).tables.length) r, r < tr.height t →
      ∀ e ∈ ((wasmBaseAir nloc ngl).tables[t]'ht).constraints,
        e.eval (natRow (rowNat tr t r) (tr.row pub t r)) = 0 := by
    intro t ht' r hr e he
    have h22 : t < 22 := by rwa [air_len] at ht'
    have htA : t < A.tables.length := by rw [hA, List.length_append, air_len]; omega
    exact table_constr H htA hr e (by rw [hget t htA h22]; exact he)
  have hcounts : ∀ t, 1 ≤ t → t ≤ 14 → ∀ r, r < tr.height t → ∀ i ∈ (chipT t).inters,
      (i.count.eval (tr.row pub t r)).toNat ≤ 1 := by
    intro t h1 h9 r hr i hi
    have ht' : t < (wasmBaseAir nloc ngl).tables.length := by rw [air_len]; omega
    have hc : ∀ e ∈ (chipT t).constraints, e.eval (natRow (rowNat tr t r) (tr.row pub t r)) = 0 := by
      intro e he
      exact hcon t ht' r hr e (by rw [chipT_eq nloc ngl t h1 h9]; exact he)
    rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨
      t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact add_counts_of hc i hi
    · exact bit_counts_of hc i hi
    · exact mul_counts_of hc i hi
    · exact shift_counts_of hc i hi
    · exact cmp_counts_of hc i hi
    · exact const_counts_of hc i hi
    · exact stack_counts_of hc i hi
    · exact ctrl_counts_of hc i hi
    · exact local_counts_of hc i hi
    · exact div_counts_of hc i hi
    · exact load_counts_of hc i hi
    · exact store_counts_of hc i hi
    · exact call_counts_of hc i hi
    · exact ret_counts_of hc i hi
  have hocc : (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)),
      (i.count.eval (tr.row pub t r)).toNat) ∈ occs (wasmBaseAir nloc ngl) tr pub :=
    mem_occs.mpr ⟨t, by rw [air_len]; exact h22, r, hr, i, by rw [← hget t ht h22]; exact hi, rfl⟩
  exact occ_bits_of hpub hcounts hcon _ hocc (Or.inl hs)

/-! ## The bound, generically -/

/-- **The per-bus R16 send bound for any `wasmBaseAir ++ tail` AIR whose tail tables are
`R16Ok`.** -/
theorem hsend_r16_of_tail {X : Ctx} {A : Air} {nloc ngl : Nat} {tail : List Table}
    {pub : List F} {tr : Trace}
    (hA : A.tables = (wasmBaseAir nloc ngl).tables ++ tail) (htail : ∀ T ∈ tail, R16Ok T)
    (H : Holds A pub tr) (hpub : PubOK X nloc ngl pub) :
    ∀ o ∈ occs A tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1 := by
  intro o ho hb hs
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hb hs ⊢
  rcases Nat.lt_or_ge t 22 with h22 | h22
  · exact base_send_le_of_prefix hA H hpub ht h22 hr hi hs
  · refine r16_le_of_ok H ht ?_ hr hi hb hs
    apply htail
    have hl : (wasmBaseAir nloc ngl).tables.length ≤ t := by rw [air_len]; exact h22
    have e : A.tables[t]'ht = tail[t - (wasmBaseAir nloc ngl).tables.length]'(by
        have := ht; rw [hA, List.length_append] at this; omega) := by
      simp only [hA]
      rw [List.getElem_append_right hl]
    rw [e]
    exact List.getElem_mem _

/-! ## The two E2E AIRs -/

/-- **The R16 send-side bound for `wasmBaseIfRegAir`.** -/
theorem ifreg_hsend_r16 {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseIfRegAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub) :
    ∀ o ∈ occs (wasmBaseIfRegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1 :=
  hsend_r16_of_tail (tail := [HostR.table, HostO.table, HostTab.table, HostB.table, IfC.table,
      RegW.table]) rfl
    (by
      intro T hT
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hT
      rcases hT with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hostR_r16ok
      · exact hostO_r16ok
      · exact hostTab_r16ok
      · exact hostB_r16ok
      · exact ifc_r16ok
      · exact regw_r16ok)
    H hpub

/-- **The R16 send-side bound for `wasmBaseM2Air`.** -/
theorem m2_hsend_r16 {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub) :
    ∀ o ∈ occs (wasmBaseM2Air nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1 :=
  hsend_r16_of_tail (tail := [HostR.table, HostO.table, HostTab.table, HostB.table, IfC.table,
      RegC.table, Conv.table, Unreach.table]) rfl
    (by
      intro T hT
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hT
      rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hostR_r16ok
      · exact hostO_r16ok
      · exact hostTab_r16ok
      · exact hostB_r16ok
      · exact ifc_r16ok
      · exact regc_r16ok
      · exact conv_r16ok
      · exact unreach_r16ok)
    H hpub

/-! ## The group walk, unconditionally -/

/-- `gap < 2^16` on a REG' byte row of a `wasmBaseIfRegAir` trace. -/
theorem ifreg_reg_gap_lt {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseIfRegAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r : Nat} (hr : r < tr.height 27) (hk : rowNat tr 27 r Reg.kind = 0) :
    rowNat tr 27 r Reg.gap < 65536 :=
  regG_gap_lt (regAt_ifreg nloc ngl) H (ifreg_hsend_r16 H hpub) hr hk

/-- `gap < 2^16` on a REG-C byte row of a `wasmBaseM2Air` trace. -/
theorem m2_reg_gap_lt {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r : Nat} (hr : r < tr.height 27) (hk : rowNat tr 27 r Reg.kind = 0) :
    rowNat tr 27 r Reg.gap < 65536 :=
  regG_gap_lt (regAt_m2 nloc ngl) H (m2_hsend_r16 H hpub) hr hk

/-- `pos < len` on a REG' byte row of a `wasmBaseIfRegAir` trace. -/
theorem ifreg_reg_pos_lt_len {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseIfRegAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r : Nat} (hr : r < tr.height 27) (hk : rowNat tr 27 r Reg.kind = 0) :
    rowNat tr 27 r Reg.pos < rowNat tr 27 r Reg.blen :=
  regG_pos_lt_len (regAt_ifreg nloc ngl) H hr hk (ifreg_reg_gap_lt H hpub hr hk)

/-- `pos < len` on a REG-C byte row of a `wasmBaseM2Air` trace. -/
theorem m2_reg_pos_lt_len {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r : Nat} (hr : r < tr.height 27) (hk : rowNat tr 27 r Reg.kind = 0) :
    rowNat tr 27 r Reg.pos < rowNat tr 27 r Reg.blen :=
  regG_pos_lt_len (regAt_m2 nloc ngl) H hr hk (m2_reg_gap_lt H hpub hr hk)

/-- **`regLenAgree_groupG` at REG' of `wasmBaseIfRegAir`, without `hsend`.** -/
theorem ifreg_regLenAgree_group {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseIfRegAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
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
  regLenAgree_groupG (regAt_ifreg nloc ngl) H (ifreg_hsend_r16 H hpub) hr0 hf hk hrid0 hpos0 hactL'

/-- **`regLenAgree_groupG` at REG-C of `wasmBaseM2Air`, without `hsend`.** -/
theorem m2_regLenAgree_group {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
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
  regLenAgree_groupG (regAt_m2 nloc ngl) H (m2_hsend_r16 H hpub) hr0 hf hk hrid0 hpos0 hactL'

/-! ## `mtp < ts` on a write row -/

theorem regw_time_inter0 :
    r16 (v Reg.ts - v RegW.mtp - 1 - B16 * v RegW.mhp) RegW.wcnt ∈ RegW.table.inters := by
  simp [RegW.table, RegW.inters, RegW.newInters, timeChk]

theorem regw_time_inter1 : r16 (4 * v RegW.mhp) RegW.wcnt ∈ RegW.table.inters := by
  simp [RegW.table, RegW.inters, RegW.newInters, timeChk]

/-- The write count `act·(1−kind)·wr` is 1 on a byte row with `wr = 1`. -/
theorem regw_wcnt_one {A : Air} {ti : Nat} {pub : List F} {tr : Trace}
    (hA : RegAt A ti) (H : Holds A pub tr) {r : Nat} (hr : r < tr.height ti)
    (hk : rowNat tr ti r Reg.kind = 0) (hwr : rowNat tr ti r RegW.wr = 1) :
    (RegW.wcnt.eval (tr.row pub ti r)).toNat = 1 := by
  have ha := regG_byte_active hA H hr hk
  simp only [RegW.wcnt, Reg.isB, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat',
    Expr.eval_col, Trace.row]
  rw [cell_cast tr ti r Reg.act, cell_cast tr ti r Reg.kind, cell_cast tr ti r RegW.wr, ha, hk, hwr]
  decide

/-- An R16 send of a 16-bit-checked value, row form: the evaluated query is `< 2^16`. -/
theorem r16_row_lt {A : Air} {ti : Nat} {pub : List F} {tr : Trace}
    (hA : RegAt A ti) (H : Holds A pub tr)
    (hsend : ∀ o ∈ occs A tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1)
    {r : Nat} (hr : r < tr.height ti) {e c : Expr} (hi : r16 e c ∈ (A.tables[ti]'hA.lt).inters)
    (hc : (c.eval (tr.row pub ti r)).toNat = 1) :
    (e.eval (tr.row pub ti r)).toNat < 65536 := by
  have hocc : (busR16, true, [e.eval (tr.row pub ti r)], 1) ∈ occs A tr pub := by
    refine mem_occs.mpr ⟨ti, hA.lt, r, hr, r16 e c, hi, ?_⟩
    simp only [r16, List.map_cons, List.map_nil, hc]
  obtain ⟨x, hx, hxl⟩ := lookup_r16G H hsend (regG_r16_recv hA H) hocc rfl rfl rfl
  simp only [List.cons.injEq, and_true] at hx
  rw [hx]; exact hxl

/-- **`mtp < ts` on an active write row, generically.**  For any AIR whose table `ti` carries REG'
(`RegAt` plus REG''s interactions), given the per-bus R16 send bound: a byte row with `wr = 1` has
`mtp < ts`, for times below `2^29` (the domain bound of `regw_time_lt`). -/
theorem regw_mtp_lt_tsG {A : Air} {ti : Nat} {pub : List F} {tr : Trace}
    (hA : RegAt A ti) (hW : ∀ i ∈ RegW.table.inters, i ∈ (A.tables[ti]'hA.lt).inters)
    (H : Holds A pub tr)
    (hsend : ∀ o ∈ occs A tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1)
    {r : Nat} (hr : r < tr.height ti)
    (hk : rowNat tr ti r Reg.kind = 0) (hwr : rowNat tr ti r RegW.wr = 1)
    (hts : rowNat tr ti r Reg.ts < 2 ^ 29) (hm : rowNat tr ti r RegW.mtp < 2 ^ 29) :
    rowNat tr ti r RegW.mtp < rowNat tr ti r Reg.ts := by
  have hc := regw_wcnt_one hA H hr hk hwr
  have hx := r16_row_lt hA H hsend hr (hW _ regw_time_inter0) hc
  have hy := r16_row_lt hA H hsend hr (hW _ regw_time_inter1) hc
  refine regw_time_lt (hp := rowNat tr ti r RegW.mhp) hts hm hx hy ?_ ?_
  · rw [Fp.cast_toNat]
    simp only [B16, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval_col,
      Trace.row, cell_cast]
  · rw [Fp.cast_toNat]
    simp only [Chips.v, Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, Trace.row, cell_cast]

/-- **`mtp < ts` on an active REG' write row of a `wasmBaseIfRegAir` trace.** -/
theorem ifreg_regw_mtp_lt_ts {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseIfRegAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r : Nat} (hr : r < tr.height 27)
    (hk : rowNat tr 27 r Reg.kind = 0) (hwr : rowNat tr 27 r RegW.wr = 1)
    (hts : rowNat tr 27 r Reg.ts < 2 ^ 29) (hm : rowNat tr 27 r RegW.mtp < 2 ^ 29) :
    rowNat tr 27 r RegW.mtp < rowNat tr 27 r Reg.ts :=
  regw_mtp_lt_tsG (regAt_ifreg nloc ngl) (fun i hi => by rw [ifreg_air_27]; exact hi) H
    (ifreg_hsend_r16 H hpub) hr hk hwr hts hm

/-- **`mtp < ts` on an active REG-C write row of a `wasmBaseM2Air` trace.** -/
theorem m2_regw_mtp_lt_ts {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r : Nat} (hr : r < tr.height 27)
    (hk : rowNat tr 27 r Reg.kind = 0) (hwr : rowNat tr 27 r RegW.wr = 1)
    (hts : rowNat tr 27 r Reg.ts < 2 ^ 29) (hm : rowNat tr 27 r RegW.mtp < 2 ^ 29) :
    rowNat tr 27 r RegW.mtp < rowNat tr 27 r Reg.ts :=
  regw_mtp_lt_tsG (regAt_m2 nloc ngl)
    (fun i hi => by rw [m2_air_27]; exact List.mem_append_left _ hi) H
    (m2_hsend_r16 H hpub) hr hk hwr hts hm

end WasmBase

#print axioms WasmBase.ifreg_hsend_r16
#print axioms WasmBase.m2_hsend_r16
#print axioms WasmBase.ifreg_regLenAgree_group
#print axioms WasmBase.m2_regLenAgree_group
#print axioms WasmBase.ifreg_reg_pos_lt_len
#print axioms WasmBase.m2_reg_pos_lt_len
#print axioms WasmBase.ifreg_regw_mtp_lt_ts
#print axioms WasmBase.m2_regw_mtp_lt_ts
