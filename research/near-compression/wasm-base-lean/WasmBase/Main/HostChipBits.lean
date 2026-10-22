import WasmBase.Main.ExecHost
import WasmBase.Main.HostChipFacts
import WasmBase.Main.RowHostSpec

/-!
# WasmBase.Main.HostChipBits — which host tables touch the buses the induction counts

`ChipFacts` (`Main/Exec.lean`) constrains tables 1-14 of `wasmBaseAir`.  For `wasm_base_exec_host`
the AIR is `wasmBaseHostAir` (26 tables; 22-25 appended).  This file records exactly what the
induction needs from the four host tables, and which of those facts hold.

## The requirement, precisely

`exec_of_rows` needs "every relevant interaction count is a bit" in only two places:

1. `msgs_perm` turns bus **balance** into a message **permutation** — for the STATE bus (0) and the
   CH bus (2), the only buses whose messages the induction permutes;
2. `rowAct` is defined as "count = 1", so deciding row activity needs bit-ness on those same buses.

So the premise is needed **only on buses 0 and 2**, not on the host buses 208-210.

## What touches buses 0 and 2

Only the HOST table.  HOSTO, HOSTT and HOSTB touch none of them:

* `HOST` (22): `stateIn`/`stateOut` on bus 0 with count `act`, and CH receives/sends on bus 2 with
  counts `pf j` / `nres` — all bits, the last two since `edae7a53d` added `Host.cActPf` /
  `Host.cActNres` (`host_row_inactive_emits_nothing`);
* `HOSTO` (23): only `HOSTQ` (208, receive) and `HOSTR` (209, send);
* `HOSTT` (24): only `HOSTT` (9, receive);
* `HOSTB` (25): only `HOSTB` (210) and `BYTE` (4).

## `HOSTO.mult` is unconstrained, and harmless

`HostO.table.constraints = []` and both of its interactions are counted with the free column `mult`
(`hosto_constraints_nil`, `hosto_counts_are_mult`).  Nothing forces `mult ≤ 1`.

**This does not affect `wasm_base_exec_host`.**  `HOSTO` is the witness oracle that stands in for
the state side (`pq-host-chip/RESULTS.md`); its multiplicity is the number of calls it answers, so
`mult > 1` is the correct semantics and constraining it would be wrong.  Because `HOSTO` touches
neither bus 0 nor bus 2 (`hosto_avoids_state_ch`), the induction never reads that count.

(An earlier revision of this file claimed this blocked the instantiation.  It does not: the
requirement is per-bus, and `HOSTO` is on the wrong buses for it.)
-/
namespace WasmBase

open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## HOSTO is unconstrained -/

/-- **`HOSTO` has no constraints.** -/
theorem hosto_constraints_nil : HostO.table.constraints = [] := rfl

/-- **`HOSTO`'s two counts are the free column `mult`.** -/
theorem hosto_counts_are_mult :
    (HostO.table.inters.map fun i => i.count) = [Expr.col HostO.mult, Expr.col HostO.mult] := rfl

/-- **`HOSTO`'s multiplicity is not bounded by any constraint.**  With no constraints, every row of
`HOSTO` satisfies them vacuously whatever `mult` is.  Harmless for the induction: see
`hosto_avoids_state_ch`. -/
theorem hosto_no_count_bound (r : Nat) (tr : Trace) (pub : List F) :
    ∀ e ∈ HostO.table.constraints, e.eval (tr.row pub 23 r) = (0 : F) := by
  intro e he
  rw [hosto_constraints_nil] at he
  exact absurd he (List.not_mem_nil)

/-! ## Which host tables touch the buses the induction counts -/

/-- **The induction counts buses STATE (0) and CH (2) only.**  This is the predicate the segment
theorem's `ChipFacts` analogue needs, and it is what makes `HOSTO.mult` irrelevant. -/
def touchesStateOrCh (T : Table) : Prop :=
  (T.inters.filter fun i => i.bus = busState ∨ i.bus = busStk) ≠ []

/-- **`HOSTO` touches neither STATE nor CH.** -/
theorem hosto_avoids_state_ch : ¬ touchesStateOrCh HostO.table := by
  unfold touchesStateOrCh; decide

/-- **`HOSTT` touches neither STATE nor CH.** -/
theorem hosttab_avoids_state_ch : ¬ touchesStateOrCh HostTab.table := by
  unfold touchesStateOrCh; decide

/-- **`HOSTB` touches CH (space 3) since the MEMIO link.**  Its two space-3 interactions are counted
by `memCnt = act·(1−dir)·(1−reg)`, which is a bit once `act`, `dir`, `reg` are (`hostb_memCnt_bit`),
and it touches nothing on STATE. -/
theorem hostb_touches_ch : touchesStateOrCh HostB.table := by
  unfold touchesStateOrCh; decide

/-- **`HOSTB` touches no STATE interaction.** -/
theorem hostb_avoids_state : (HostB.table.inters.filter (fun i => i.bus = busState)) = [] := by
  decide

/-- **`HOSTB`'s space-3 count is a bit.**  `memCnt = act·(1−dir)·(1−reg)` and `act`, `dir`, `reg` are
bits by `cAct`/`cDir`/`cReg`, so the product lands in `{0,1}`.  This is what keeps `msgs_perm` sound
now that `HOSTB` is an emitter on the CH bus: a count of `2` (or more) would let one row balance
several messages. -/
theorem hostb_memCnt_bit {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 25) :
    (HostB.memCnt.eval (tr.row pub 25 r)).toNat ≤ 1 := by
  have ht : 25 < (wasmBaseHostAir nloc ngl).tables.length := by simp [wasmBaseHostAir, air_len]
  have hcon : ∀ e ∈ HostB.table.constraints, e.eval (natRow (rowNat tr 25 r) (tr.row pub 25 r)) = 0 :=
    table_constr H ht hr
  have hc0 := hcon HostB.cAct (by simp [HostB.table, HostB.constraints])
  have hd0 := hcon HostB.cDir (by simp [HostB.table, HostB.constraints])
  have hr0 := hcon HostB.cReg (by simp [HostB.table, HostB.constraints])
  simp only [HostB.cAct, HostB.cDir, HostB.cReg, Chips.bool, Chips.v, Expr.eval_mul',
    Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow] at hc0 hd0 hr0
  have bitA : rowNat tr 25 r HostB.act = 0 ∨ rowNat tr 25 r HostB.act = 1 :=
    bool_nat (rowNat_lt tr 25 r HostB.act) hc0
  have bitD : rowNat tr 25 r HostB.dir = 0 ∨ rowNat tr 25 r HostB.dir = 1 :=
    bool_nat (rowNat_lt tr 25 r HostB.dir) hd0
  have bitR : rowNat tr 25 r HostB.reg = 0 ∨ rowNat tr 25 r HostB.reg = 1 :=
    bool_nat (rowNat_lt tr 25 r HostB.reg) hr0
  have e : (HostB.memCnt.eval (tr.row pub 25 r)) =
      ((rowNat tr 25 r HostB.act : Nat) : F) * (1 - ((rowNat tr 25 r HostB.dir : Nat) : F)) *
        (1 - ((rowNat tr 25 r HostB.reg : Nat) : F)) := by
    simp only [HostB.memCnt, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat',
      Expr.eval_col, Trace.row, cell_cast, HostB.act, HostB.dir, HostB.reg, cast_one]
  rw [e]
  rcases bitA with h | h <;> rcases bitD with h' | h' <;> rcases bitR with h'' | h'' <;>
    rw [h, h', h''] <;> decide

/-- **`HOSTB`'s two CH counts are `memCnt`.** -/
theorem hostb_ch_count_list :
    ((HostB.table.inters.filter (fun i => i.bus = busState ∨ i.bus = busStk)).map (·.count)) =
      [HostB.memCnt, HostB.memCnt] := by
  decide

/-- Each of `HOSTB`'s CH interactions has count ≤ 1 on any `Holds` row. -/
theorem hostb_inter_bound {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 25) :
    ∀ i ∈ HostB.table.inters, (i.bus = busState ∨ i.bus = busStk) →
      (i.count.eval (tr.row pub 25 r)).toNat ≤ 1 := by
  intro i hi hb
  have hmem : i ∈ HostB.table.inters.filter (fun j => j.bus = busState ∨ j.bus = busStk) :=
    List.mem_filter.mpr ⟨hi, by simpa using hb⟩
  have hcount : i.count ∈ [HostB.memCnt, HostB.memCnt] := by
    have := List.mem_map_of_mem (f := (·.count)) hmem
    rwa [hostb_ch_count_list] at this
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcount
  rcases hcount with h | h <;> rw [h] <;> exact hostb_memCnt_bit H hr

/-- **Only `HOST` touches them**, and there its counts are `act`, `pf j` and `nres` — bits, the
latter two by `edae7a53d`'s gating constraints. -/
theorem host_touches_state_ch : touchesStateOrCh Host.table := by
  unfold touchesStateOrCh; decide


/-! ## Occurrences of the host AIR, by table -/

/-- **An occurrence of `wasmBaseHostAir` is in one of the 26 tables.**  Tables 0-21 are the base
AIR's (`host_air_get`), table 22 is `HOST`, 23 `HOSTO`, 24 `HOSTT`, 25 `HOSTB`. -/
theorem occ_table_host {nloc ngl : Nat} {tr : Trace} {pub : List F} {o : Occ}
    (ho : o ∈ occs (wasmBaseHostAir nloc ngl) tr pub) :
    (∃ t, ∃ ht : t < 22, ∃ r, r < tr.height t ∧
      ∃ i ∈ ((wasmBaseAir nloc ngl).tables[t]'(by simp [air_len]; exact ht)).inters,
        o = (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat)) ∨
    (∃ r, r < tr.height 22 ∧ ∃ i ∈ Host.table.inters,
        o = (i.bus, i.send, i.msg.map (·.eval (tr.row pub 22 r)), (i.count.eval (tr.row pub 22 r)).toNat)) ∨
    (∃ r, r < tr.height 23 ∧ ∃ i ∈ HostO.table.inters,
        o = (i.bus, i.send, i.msg.map (·.eval (tr.row pub 23 r)), (i.count.eval (tr.row pub 23 r)).toNat)) ∨
    (∃ r, r < tr.height 24 ∧ ∃ i ∈ HostTab.table.inters,
        o = (i.bus, i.send, i.msg.map (·.eval (tr.row pub 24 r)), (i.count.eval (tr.row pub 24 r)).toNat)) ∨
    (∃ r, r < tr.height 25 ∧ ∃ i ∈ HostB.table.inters,
        o = (i.bus, i.send, i.msg.map (·.eval (tr.row pub 25 r)), (i.count.eval (tr.row pub 25 r)).toNat)) := by
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  have ht26 : t < 26 := by rwa [host_air_len] at ht
  rcases (show t < 22 ∨ t = 22 ∨ t = 23 ∨ t = 24 ∨ t = 25 by omega) with h | rfl | rfl | rfl | rfl
  · left
    refine ⟨t, h, r, hr, i, ?_, rfl⟩
    rw [host_air_get nloc ngl t h] at hi
    exact hi
  · right; left
    refine ⟨r, hr, i, ?_, rfl⟩
    rwa [host_air_22] at hi
  · right; right; left
    refine ⟨r, hr, i, ?_, rfl⟩
    rwa [host_air_23] at hi
  · right; right; right; left
    refine ⟨r, hr, i, ?_, rfl⟩
    rwa [host_air_24] at hi
  · right; right; right; right
    refine ⟨r, hr, i, ?_, rfl⟩
    rwa [host_air_25] at hi


/-! ## Which interactions of a host table lie on STATE/CH -/

/-- `HOST`'s STATE/CH interactions, by direction.  Bus 0 carries `stateIn`/`stateOut` (count `act`);
bus 2 carries two `stkRecv` (count `pf j`) and one `stkSend` (count `nres`). -/
theorem host_state_ch_inters :
    (Host.table.inters.filter (fun i => i.bus = busState ∨ i.bus = busStk)) =
      [Host.table.inters.getD 0 default, Host.table.inters.getD 1 default] ++
      (Host.argRange.map fun j => Host.table.inters.getD (Host.chBase + Host.chStride * j) default) ++
      [Host.table.inters.getD Host.sendIdx default] := by
  simp only [Host.table, Host.inters, Host.argRange, Host.nArgs, Host.chBase, Host.chStride,
    Host.sendIdx, List.range_succ, List.map_cons, List.map_nil, List.append_nil]
  decide

/-- **HOSTO and HOSTT have no STATE/CH interaction at all**, so their (unconstrained) counts on
their own buses never enter the induction.  `HOSTB` is *not* in this list any more: the MEMIO link
made it a CH emitter (`hostb_touches_ch`), and its counts are the bits `hostb_memCnt_bit`. -/
theorem env_inters_nil :
    (HostO.table.inters.filter (fun i => i.bus = busState ∨ i.bus = busStk)) = [] ∧
    (HostTab.table.inters.filter (fun i => i.bus = busState ∨ i.bus = busStk)) = [] := by
  refine ⟨?_, ?_⟩ <;> decide


/-! ## `st`, `ar`, `nres` are bits on any HOST row -/

/-- **`st` is a bit on any `Holds` HOST row.**  Directly from `Host.cSt` (`bool (v st)`). -/
theorem host_st_bit_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Host.table.constraints, e.eval (natRow (rowNat tr 22 r) (tr.row pub 22 r)) = 0) :
    rowNat tr 22 r Host.st = 0 ∨ rowNat tr 22 r Host.st = 1 := by
  show rowNat tr 22 r 9 = 0 ∨ rowNat tr 22 r 9 = 1
  have hs := hcon Host.cSt host_cSt_mem
  simp only [Host.cSt, Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', Host.st, natRow] at hs
  exact bool_nat (rowNat_lt tr 22 r 9) hs

/-- **`ar` is a bit on any `Holds` HOST row.**  Directly from `Host.cAr`. -/
theorem host_ar_bit_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Host.table.constraints, e.eval (natRow (rowNat tr 22 r) (tr.row pub 22 r)) = 0) :
    rowNat tr 22 r Host.ar = 0 ∨ rowNat tr 22 r Host.ar = 1 := by
  show rowNat tr 22 r 8 = 0 ∨ rowNat tr 22 r 8 = 1
  have ha := hcon Host.cAr host_cAr_mem
  simp only [Host.cAr, Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', Host.ar, natRow] at ha
  exact bool_nat (rowNat_lt tr 22 r 8) ha

/-- **`nres` is a bit on any `Holds` HOST row.**  `Host.cNres` gives `nres = (1 − st)·ar` in the
field, and `st`, `ar` are boolean, so `nres ∈ {0, 1}`.  No `act` gating is involved: the product is
a bit whatever `act` is, which is why `Host.cActNres` is only about the *inactive* case. -/
theorem host_nres_bit_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Host.table.constraints, e.eval (natRow (rowNat tr 22 r) (tr.row pub 22 r)) = 0) :
    rowNat tr 22 r Host.nres = 0 ∨ rowNat tr 22 r Host.nres = 1 := by
  show rowNat tr 22 r 10 = 0 ∨ rowNat tr 22 r 10 = 1
  obtain hst := host_st_bit_of hcon
  obtain har := host_ar_bit_of hcon
  have hn := hcon Host.cNres host_cNres_mem
  simp only [Host.cNres, Chips.v, Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_col,
    Expr.eval_ofNat', Host.nres, Host.st, Host.ar, natRow] at hn
  have hn' : (rowNat tr 22 r 10 : F) - (rowNat tr 22 r 8 : F) +
      (rowNat tr 22 r 9 : F) * (rowNat tr 22 r 8 : F) = 0 := hn
  have h9 : Host.st = 9 := rfl
  have h8 : Host.ar = 8 := rfl
  rw [h9] at hst
  rw [h8] at har
  have hn2 : (rowNat tr 22 r 10 : F) = (rowNat tr 22 r 8 : F) -
      (rowNat tr 22 r 9 : F) * (rowNat tr 22 r 8 : F) := by grind
  rcases hst with hst | hst
  · -- st = 0: nres = ar
    have e : (rowNat tr 22 r 10 : F) = (rowNat tr 22 r 8 : F) := by
      rw [hst] at hn2
      grind
    rcases har with har | har
    · exact Or.inl ((cast_inj_iff (rowNat_lt tr 22 r 10) (by decide : (0 : Nat) < P)).mp (by
        rw [e, har]))
    · exact Or.inr ((cast_inj_iff (rowNat_lt tr 22 r 10) (by decide : (1 : Nat) < P)).mp (by
        rw [e, har]))
  · -- st = 1: nres = 0
    have e : (rowNat tr 22 r 10 : F) = 0 := by
      rw [hst] at hn2
      have h1 : ((1 : Nat) : F) = 1 := rfl
      rw [h1] at hn2
      grind
    exact Or.inl ((cast_inj_iff (rowNat_lt tr 22 r 10) (by decide : (0 : Nat) < P)).mp e)

theorem host_st_bit {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22) :
    rowNat tr 22 r Host.st = 0 ∨ rowNat tr 22 r Host.st = 1 :=
  host_st_bit_of (table_constr H (by simp [wasmBaseHostAir, air_len]) hr)

theorem host_ar_bit {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22) :
    rowNat tr 22 r Host.ar = 0 ∨ rowNat tr 22 r Host.ar = 1 :=
  host_ar_bit_of (table_constr H (by simp [wasmBaseHostAir, air_len]) hr)

theorem host_nres_bit {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22) :
    rowNat tr 22 r Host.nres = 0 ∨ rowNat tr 22 r Host.nres = 1 :=
  host_nres_bit_of (table_constr H (by simp [wasmBaseHostAir, air_len]) hr)

/-! ## The five STATE/CH counts of a HOST row, as bounds -/

/-- `Expr.col i` evaluates to the cell's canonical representative. -/
theorem col_eval (tr : Trace) (pub : List F) (t r i : Nat) :
    ((Expr.col i).eval (tr.row pub t r)).toNat = rowNat tr t r i := by
  simp only [Expr.eval_col, Trace.row, rowNat, Fp.cast_toNat]

/-- **`act` is ≤ 1.** -/
theorem host_act_bit {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22) :
    rowNat tr 22 r Host.act ≤ 1 := by
  show rowNat tr 22 r 5 ≤ 1
  have ht : 22 < (wasmBaseHostAir nloc ngl).tables.length := by simp [wasmBaseHostAir, air_len]
  have hcon : ∀ e ∈ Host.table.constraints, e.eval (natRow (rowNat tr 22 r) (tr.row pub 22 r)) = 0 :=
    table_constr H ht hr
  have hb := hcon Host.cAct host_cAct_mem
  simp only [Host.cAct, Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', Host.act, natRow] at hb
  have hb' : (rowNat tr 22 r 5 : F) * ((rowNat tr 22 r 5 : F) - 1) = 0 := hb
  rcases bool_nat (rowNat_lt tr 22 r 5) hb' with h | h <;> omega

/-- **`pf j` is ≤ 1** for `j ≤ 1`, by `Host.cP0` / `Host.cP1`. -/
theorem host_pf_le {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22)
    {j : Nat} (hj : j < Host.nArgs) : rowNat tr 22 r (Host.pf j) ≤ 1 := by
  show rowNat tr 22 r (19 + j) ≤ 1
  have ht : 22 < (wasmBaseHostAir nloc ngl).tables.length := by simp [wasmBaseHostAir, air_len]
  have hcon : ∀ e ∈ Host.table.constraints, e.eval (natRow (rowNat tr 22 r) (tr.row pub 22 r)) = 0 :=
    table_constr H ht hr
  have hb := hcon (Host.cP j) (host_cP_mem j hj)
  simp only [Host.cP, Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', Host.pf, natRow] at hb
  have hb' : (rowNat tr 22 r (19 + j) = 0 ∨ rowNat tr 22 r (19 + j) = 1) :=
    bool_nat (rowNat_lt tr 22 r (19 + j)) hb
  rcases hb' with h | h <;> omega

/-- **`nres` is ≤ 1.** -/
theorem host_nres_le {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22) :
    rowNat tr 22 r Host.nres ≤ 1 := by
  rcases host_nres_bit H hr with h | h <;> omega

/-! ## `occ_bits` for the host AIR on buses STATE/CH -/

/-- **The counts of `HOST`'s STATE/CH interactions, as a list.**  Two `act` (the STATE messages),
one `pf j` per argument, and one `nres` (the send).  Stating the *list of counts* rather than
destructuring the interactions keeps this independent of the exact `inters` layout. -/
theorem host_state_ch_count_list :
    ((Host.table.inters.filter (fun i => i.bus = busState ∨ i.bus = busStk)).map (·.count)) =
      Expr.col Host.act :: Expr.col Host.act ::
        (Host.argRange.map (fun j => Expr.col (Host.pf j)) ++ [Expr.col Host.nres]) := by
  simp only [Host.table, Host.inters, Host.chBase, Host.chStride, Host.sendIdx, Host.argRange]
  decide

/-- Each of `HOST`'s STATE/CH interactions has count ≤ 1 on any `Holds` row. -/
theorem host_inter_bound {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22) :
    ∀ i ∈ Host.table.inters, (i.bus = busState ∨ i.bus = busStk) →
      (i.count.eval (tr.row pub 22 r)).toNat ≤ 1 := by
  intro i hi hb
  have hmem : i ∈ Host.table.inters.filter (fun j => j.bus = busState ∨ j.bus = busStk) :=
    List.mem_filter.mpr ⟨hi, by simpa using hb⟩
  -- the count is one of `act`, `pf j`, `nres`
  have hcount : i.count ∈ (Expr.col Host.act :: Expr.col Host.act ::
      (Host.argRange.map (fun j => Expr.col (Host.pf j)) ++ [Expr.col Host.nres])) := by
    have := List.mem_map_of_mem (f := (·.count)) hmem
    rwa [host_state_ch_count_list] at this
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_singleton,
    Host.argRange, List.mem_range, or_false, List.not_mem_nil] at hcount
  rcases hcount with h | h | ⟨j, hj, h⟩ | h
  · rw [h]; rw [col_eval]; exact host_act_bit H hr
  · rw [h]; rw [col_eval]; exact host_act_bit H hr
  · rw [← h]; rw [col_eval]; exact host_pf_le H hr (by simpa [Host.argRange] using hj)
  · rw [h]; rw [col_eval]; exact host_nres_le H hr

/-! ## `occ_bits` for the host AIR on buses STATE/CH -/

/-- **Every STATE/CH occurrence of `wasmBaseHostAir` has count ≤ 1.**  Tables 0-21 come from the
base AIR's `occ_bits` via `occs_mono_host`; `HOST`'s interactions on these buses are bounded by
`host_inter_bound`; `HOSTB`'s two space-3 counts by `hostb_inter_bound` (the MEMIO link); and
`HOSTO`/`HOSTT` have none (`env_inters_nil`). -/
theorem occ_bits_host {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (H0 : Holds (wasmBaseAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub) (CF : ChipFacts X nloc ngl pub tr) :
    ∀ o ∈ occs (wasmBaseHostAir nloc ngl) tr pub, o.1 = busState ∨ o.1 = busStk → o.2.2.2 ≤ 1 := by
  intro o ho hk
  rcases occ_table_host ho with ⟨t, ht, r, hr, i, hi, rfl⟩ | ⟨r, hr, i, hi, rfl⟩ |
    ⟨r, hr, i, hi, rfl⟩ | ⟨r, hr, i, hi, rfl⟩ | ⟨r, hr, i, hi, rfl⟩
  · exact occ_bits H0 hpub CF _
      (mem_occs.mpr ⟨t, by simp [air_len]; exact ht, r, hr, i, hi, rfl⟩)
      (by
        have e : i.bus = busState ∨ i.bus = busStk := by
          rcases hk with h | h
          · exact Or.inl (by simpa using h)
          · exact Or.inr (by simpa using h)
        rcases e with h | h <;> simp [h])
  · exact host_inter_bound H hr i hi (by simpa using hk)
  · have := env_inters_nil.1
    rw [List.eq_nil_iff_forall_not_mem] at this
    have hb' : i.bus = busState ∨ i.bus = busStk := by
      rcases hk with h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr (by simpa using h)
    exact absurd (List.mem_filter.mpr ⟨hi, by rcases hb' with h | h <;> simp [h]⟩) (this i)
  · have := env_inters_nil.2
    rw [List.eq_nil_iff_forall_not_mem] at this
    have hb' : i.bus = busState ∨ i.bus = busStk := by
      rcases hk with h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr (by simpa using h)
    exact absurd (List.mem_filter.mpr ⟨hi, by rcases hb' with h | h <;> simp [h]⟩) (this i)
  · exact hostb_inter_bound H hr i hi (by simpa using hk)

end WasmBase
