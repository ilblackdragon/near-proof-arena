import WasmBase.Main.SegHoldsX
import WasmBase.SegAirMP
/-!
# WasmBase.Main.SegHoldsS — the segment relation without table 20 (E2E M4c, sub-lane MP)

`wasmBaseSegAir` (M4) and `wasmBaseSegAirMP` (M4b, batched Merkle multiproof) differ only in table 20
(`MPATH`, `segMP_same`), whose interactions are on the memory buses `busLeaf` (15), `busRch` (16),
the multiproof's node bus `busNode` (17, MP only) and the chip bus `extBus` (103).  The segment
soundness argument (`seg_sound`) needs nothing about table 20 or those buses except bus 103's
receives of the CUT streams (tables 30/31).

**`HoldsXS nloc ngl pub tr`** is that part of the relation, stated over `wasmBaseSegAir`'s tables:
`HoldsX` with the constraints of table 20 and the balance / load bound of the buses 15, 16, 17, 103
removed (`OkBus`).  Both AIRs imply it:

* `HoldsX.toS : HoldsX (wasmBaseSegAir …) pub tr → HoldsXS …` (field by field);
* `HoldsX.toSMP : HoldsX (wasmBaseSegAirMP …) pub tr → HoldsXS …`: the tables `≠ 20` are equal
  (`segMP_same`) and on a bus `OkBus b` neither AIR's table 20 has an interaction, so the bus-`b`
  occurrences (`occs_filter_bus`), `busNat` and `busLoad` of the two AIRs coincide.

The generic `HoldsX` lemmas are restated here for `HoldsXS` (`…XS`, with the side conditions
`t ≠ 20` / `OkBus b`).  The `seg_sound` chain is re-derived from `HoldsXS` in `Main/SegS/*.lean`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Local
set_option linter.unusedSimpArgs false

/-- The buses `seg_sound` uses the balance of: all but the memory-root buses 15, 16, 17 and the chip
bus 103. -/
def OkBus (b : Nat) : Prop := b ≠ Seg.busLeaf ∧ b ≠ Seg.busRch ∧ b ≠ Seg.busNode ∧ b ≠ extBus

instance (b : Nat) : Decidable (OkBus b) := by unfold OkBus; infer_instance

/-- A table index other than 20 (`MPATH`), as a class so that concrete indices are discharged by
instance search. -/
class SegT (t : Nat) : Prop where
  ne20 : t ≠ 20

instance : SegT 0 := ⟨by decide⟩
instance : SegT 1 := ⟨by decide⟩
instance : SegT 2 := ⟨by decide⟩
instance : SegT 3 := ⟨by decide⟩
instance : SegT 4 := ⟨by decide⟩
instance : SegT 5 := ⟨by decide⟩
instance : SegT 6 := ⟨by decide⟩
instance : SegT 7 := ⟨by decide⟩
instance : SegT 8 := ⟨by decide⟩
instance : SegT 9 := ⟨by decide⟩
instance : SegT 10 := ⟨by decide⟩
instance : SegT 11 := ⟨by decide⟩
instance : SegT 12 := ⟨by decide⟩
instance : SegT 13 := ⟨by decide⟩
instance : SegT 14 := ⟨by decide⟩
instance : SegT 15 := ⟨by decide⟩
instance : SegT 16 := ⟨by decide⟩
instance : SegT 17 := ⟨by decide⟩
instance : SegT 18 := ⟨by decide⟩
instance : SegT 19 := ⟨by decide⟩
instance : SegT 21 := ⟨by decide⟩
instance : SegT 22 := ⟨by decide⟩
instance : SegT 23 := ⟨by decide⟩
instance : SegT 24 := ⟨by decide⟩
instance : SegT 25 := ⟨by decide⟩
instance : SegT 26 := ⟨by decide⟩
instance : SegT 27 := ⟨by decide⟩
instance : SegT 28 := ⟨by decide⟩
instance : SegT 29 := ⟨by decide⟩
instance : SegT 30 := ⟨by decide⟩
instance : SegT 31 := ⟨by decide⟩

/-- **The segment relation without table 20**: `HoldsX (wasmBaseSegAir …)` with table 20's
constraints and the balance / load bound of the buses 15, 16, 17, 103 removed. -/
structure HoldsXS (nloc ngl : Nat) (pub : List F) (tr : Trace) : Prop where
  pubLen : pub.length = (wasmBaseSegAir nloc ngl).numPub
  heightPos : ∀ t, t < (wasmBaseSegAir nloc ngl).tables.length → 4 ≤ tr.height t
  heightLe : ∀ t, t < (wasmBaseSegAir nloc ngl).tables.length → tr.height t ≤ 2 ^ maxLogHeight
  constr : ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length) [SegT t], ∀ r, r < tr.height t →
    ∀ e ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).constraints, e.eval (tr.row pub t r) = 0
  balance : ∀ b m, OkBus b →
    busNat (wasmBaseSegAir nloc ngl) tr pub b true m % P = busNat (wasmBaseSegAir nloc ngl) tr pub b false m % P
  busBound : ∀ b, OkBus b → busLoad (wasmBaseSegAir nloc ngl) tr b < P

theorem HoldsX.toS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) :
    HoldsXS nloc ngl pub tr :=
  ⟨H.pubLen, H.heightPos, H.heightLe, fun t ht _ => H.constr t ht, fun b m hb => H.balance b m hb.2.2.2,
    fun b _ => H.busBound b⟩

/-! ## `wasmBaseSegAirMP` implies `HoldsXS` -/

theorem flatMap_zipIdx_congr {α β : Type} (F G : α × Nat → List β) :
    ∀ (l1 l2 : List α) (n : Nat), l1.length = l2.length →
      (∀ i (h1 : i < l1.length) (h2 : i < l2.length), F (l1[i], n + i) = G (l2[i], n + i)) →
      (l1.zipIdx n).flatMap F = (l2.zipIdx n).flatMap G
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | a :: l1, b :: l2, n, h, hF => by
    simp only [List.zipIdx_cons, List.flatMap_cons]
    have h0 := hF 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0
    rw [h0, flatMap_zipIdx_congr F G l1 l2 (n + 1) (by simpa using h) (fun i h1 h2 => by
      have := hF (i + 1) (by simp; omega) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [show n + 1 + i = n + (i + 1) by omega]; exact this)]

theorem map_zipIdx_congr {α β : Type} (F G : α × Nat → β) :
    ∀ (l1 l2 : List α) (n : Nat), l1.length = l2.length →
      (∀ i (h1 : i < l1.length) (h2 : i < l2.length), F (l1[i], n + i) = G (l2[i], n + i)) →
      (l1.zipIdx n).map F = (l2.zipIdx n).map G
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | a :: l1, b :: l2, n, h, hF => by
    simp only [List.zipIdx_cons, List.map_cons]
    have h0 := hF 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0
    rw [h0, map_zipIdx_congr F G l1 l2 (n + 1) (by simpa using h) (fun i h1 h2 => by
      have := hF (i + 1) (by simp; omega) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [show n + 1 + i = n + (i + 1) by omega]; exact this)]

theorem segMP_len' (nloc ngl : Nat) :
    (wasmBaseSegAirMP nloc ngl).tables.length = (wasmBaseSegAir nloc ngl).tables.length := by
  rw [segMP_len, seg_air_len]

theorem segMP_tab (nloc ngl t : Nat) (h20 : t ≠ 20) (h1 : t < (wasmBaseSegAirMP nloc ngl).tables.length)
    (h2 : t < (wasmBaseSegAir nloc ngl).tables.length) :
    (wasmBaseSegAirMP nloc ngl).tables[t]'h1 = (wasmBaseSegAir nloc ngl).tables[t]'h2 := by
  have := segMP_same nloc ngl t h20
  rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at this
  exact Option.some.inj this

/-- Table 20 of either AIR has no interaction on an `OkBus` bus. -/
theorem seg_t20_okBus (nloc ngl : Nat) :
    ((wasmBaseSegAir nloc ngl).tables[20]'(by simp [seg_air_len])).inters.all (fun i => !decide (OkBus i.bus)) = true := by
  rw [show (wasmBaseSegAir nloc ngl).tables[20]'(by simp [seg_air_len]) = Seg.Mpath.table from rfl]
  decide +kernel

theorem seg_t20_noBus (nloc ngl : Nat) {b : Nat} (hb : OkBus b) {ht : 20 < (wasmBaseSegAir nloc ngl).tables.length}
    {i : Inter} (hi : i ∈ ((wasmBaseSegAir nloc ngl).tables[20]'ht).inters) : i.bus ≠ b := by
  have := List.all_eq_true.mp (seg_t20_okBus nloc ngl) i hi
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
  intro h; exact this (h ▸ hb)

theorem segMP_t20_okBus :
    Seg.MpathMP.table.inters.all (fun i => !decide (OkBus i.bus)) = true := by
  decide +kernel

theorem filter_bus_nil {T : Table} (hT : T.inters.all (fun i => !decide (OkBus i.bus)) = true)
    {b : Nat} (hb : OkBus b) (tr : Trace) (pub : List F) (t : Nat) :
    ((List.range (tr.height t)).flatMap fun r =>
      T.inters.map fun i => ((i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat) : Occ)).filter
        (fun o : Occ => decide (o.1 = b)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro o ho
  obtain ⟨r, -, ho⟩ := List.mem_flatMap.mp ho
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ho
  have := List.all_eq_true.mp hT i hi
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
  simp only [decide_eq_true_eq]
  intro h; exact this (h ▸ hb)

theorem filter_inters_nil {T : Table} (hT : T.inters.all (fun i => !decide (OkBus i.bus)) = true)
    {b : Nat} (hb : OkBus b) : T.inters.filter (fun i => decide (i.bus = b)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro i hi
  have := List.all_eq_true.mp hT i hi
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
  simp only [decide_eq_true_eq]
  intro h; exact this (h ▸ hb)

/-- On an `OkBus` bus the two AIRs have the same occurrences. -/
theorem occs_filter_bus (nloc ngl : Nat) (tr : Trace) (pub : List F) {b : Nat} (hb : OkBus b) :
    (occs (wasmBaseSegAirMP nloc ngl) tr pub).filter (fun o => decide (o.1 = b)) =
      (occs (wasmBaseSegAir nloc ngl) tr pub).filter (fun o => decide (o.1 = b)) := by
  unfold occs
  rw [List.filter_flatMap, List.filter_flatMap]
  refine flatMap_zipIdx_congr _ _ _ _ 0 (segMP_len' nloc ngl) fun i h1 h2 => ?_
  simp only [Nat.zero_add]
  by_cases h20 : i = 20
  · subst h20
    have e1 : (wasmBaseSegAirMP nloc ngl).tables[20]'h1 = Seg.MpathMP.table := by
      have := segMP_t20 nloc ngl
      rw [List.getElem?_eq_getElem h1] at this
      exact Option.some.inj this
    rw [e1, filter_bus_nil segMP_t20_okBus hb, filter_bus_nil (seg_t20_okBus nloc ngl) hb]
  · rw [segMP_tab nloc ngl i h20 h1 h2]

theorem busNat_filter_bus (A : Air) (tr : Trace) (pub : List F) (b : Nat) (s : Bool) (m : List F) :
    busNat A tr pub b s m =
      ((((occs A tr pub).filter (fun o => decide (o.1 = b))).filter fun o => o.1 = b ∧ o.2.1 = s ∧ o.2.2.1 = m).map
        (·.2.2.2)).sum := by
  unfold busNat
  rw [List.filter_filter]
  congr 2
  apply List.filter_congr
  intro o _
  by_cases h : o.1 = b <;> simp [h]

theorem segMP_busNat (nloc ngl : Nat) (tr : Trace) (pub : List F) {b : Nat} (hb : OkBus b) (s : Bool) (m : List F) :
    busNat (wasmBaseSegAirMP nloc ngl) tr pub b s m = busNat (wasmBaseSegAir nloc ngl) tr pub b s m := by
  rw [busNat_filter_bus, busNat_filter_bus (wasmBaseSegAir nloc ngl), occs_filter_bus nloc ngl tr pub hb]

theorem segMP_busLoad (nloc ngl : Nat) (tr : Trace) {b : Nat} (hb : OkBus b) :
    busLoad (wasmBaseSegAirMP nloc ngl) tr b = busLoad (wasmBaseSegAir nloc ngl) tr b := by
  unfold busLoad
  congr 1
  refine map_zipIdx_congr _ _ _ _ 0 (segMP_len' nloc ngl) fun i h1 h2 => ?_
  simp only [Nat.zero_add]
  by_cases h20 : i = 20
  · subst h20
    have e1 : (wasmBaseSegAirMP nloc ngl).tables[20]'h1 = Seg.MpathMP.table := by
      have := segMP_t20 nloc ngl
      rw [List.getElem?_eq_getElem h1] at this
      exact Option.some.inj this
    rw [e1, filter_inters_nil segMP_t20_okBus hb, filter_inters_nil (seg_t20_okBus nloc ngl) hb]
  · rw [segMP_tab nloc ngl i h20 h1 h2]

/-- **The multiproof AIR implies `HoldsXS`.** -/
theorem HoldsX.toSMP {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr) :
    HoldsXS nloc ngl pub tr where
  pubLen := H.pubLen
  heightPos t ht := H.heightPos t (by rw [segMP_len']; exact ht)
  heightLe t ht := H.heightLe t (by rw [segMP_len']; exact ht)
  constr t ht h20 r hr e he := by
    have h20 := h20.ne20
    have ht' : t < (wasmBaseSegAirMP nloc ngl).tables.length := by rw [segMP_len']; exact ht
    rw [← segMP_tab nloc ngl t h20 ht' ht] at he
    exact H.constr t ht' r hr e he
  balance b m hb := by
    rw [← segMP_busNat nloc ngl tr pub hb, ← segMP_busNat nloc ngl tr pub hb]
    exact H.balance b m hb.2.2.2
  busBound b hb := by rw [← segMP_busLoad nloc ngl tr hb]; exact H.busBound b

/-! ## The generic `HoldsX` lemmas for `HoldsXS` -/

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

theorem table_constrXS {t : Nat} (ht : t < (wasmBaseSegAir nloc ngl).tables.length) [SegT t] {r : Nat}
    (hr : r < tr.height t) :
    ∀ e ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).constraints,
      e.eval (natRow (rowNat tr t r) (tr.row pub t r)) = 0 := by
  intro e he
  rw [← row_eq_natRow]
  exact H.constr t ht r hr e he

theorem table_constr_eqXS {t : Nat} (ht : t < (wasmBaseSegAir nloc ngl).tables.length) [SegT t]
    (T : Table) (hT : (wasmBaseSegAir nloc ngl).tables[t]'ht = T)
    {r : Nat} (hr : r < tr.height t) :
    ∀ e ∈ T.constraints, e.eval (natRow (rowNat tr t r) (tr.row pub t r)) = 0 := by
  intro e he
  rw [← hT] at he
  exact table_constrXS H ht hr e he

theorem busNat_ltXS (b : Nat) (s : Bool) (m : List F)
    (hbit : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = b → o.2.1 = s → o.2.2.2 ≤ 1)
    (hx : OkBus b := by decide) :
    busNat (wasmBaseSegAir nloc ngl) tr pub b s m < P := by
  have h1 : busNat (wasmBaseSegAir nloc ngl) tr pub b s m ≤ ((occs (wasmBaseSegAir nloc ngl) tr pub).filter fun o => o.1 = b ∧ o.2.1 = s ∧ o.2.2.1 = m).length := by
    unfold busNat
    have := sum_le_length (l := ((occs (wasmBaseSegAir nloc ngl) tr pub).filter fun o => o.1 = b ∧ o.2.1 = s ∧ o.2.2.1 = m).map (·.2.2.2))
      (by
        intro a ha
        obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ha
        obtain ⟨ho, hf⟩ := List.mem_filter.mp ho
        simp only [decide_eq_true_eq] at hf
        exact hbit o ho hf.1 hf.2.1)
    simpa using this
  have h2 : ((occs (wasmBaseSegAir nloc ngl) tr pub).filter fun o => o.1 = b ∧ o.2.1 = s ∧ o.2.2.1 = m).length ≤
      ((occs (wasmBaseSegAir nloc ngl) tr pub).filter fun o => o.1 = b ∧ o.2.1 = s).length := by
    apply length_filter_mono
    intro x hx; simp only [decide_eq_true_eq] at hx ⊢; exact ⟨hx.1, hx.2.1⟩
  have h3 := length_filter_occs_le (wasmBaseSegAir nloc ngl) tr pub b s
  have h4 := H.busBound b hx
  omega

theorem lookup_soundXS (b : Nat) (hx : OkBus b) (Q : List F → Prop)
    (hrecv : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = b → o.2.1 = false → o.2.2.2 ≠ 0 → Q o.2.2.1)
    (hsend : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = b → o.2.1 = true → o.2.2.2 ≤ 1)
    {o : Occ} (ho : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub) (hb : o.1 = b) (hs : o.2.1 = true)
    (hc : o.2.2.2 = 1) :
    Q o.2.2.1 := by
  refine Classical.byContradiction fun hq => ?_
  have h0 : busNat (wasmBaseSegAir nloc ngl) tr pub b false o.2.2.1 = 0 :=
    busNat_zero fun o' ho' hb' hs' hm' => Classical.byContradiction fun hc' => hq (hm' ▸ hrecv o' ho' hb' hs' hc')
  have hbal := H.balance b o.2.2.1 hx
  rw [h0] at hbal
  have hge := count_le_busNat ho hb hs rfl
  have hlt := busNat_ltXS H b true o.2.2.1 hsend hx
  rw [Nat.mod_eq_of_lt hlt, Nat.zero_mod] at hbal
  omega

theorem perm_exactXS (b : Nat) (hx : OkBus b)
    (hbit : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = b → o.2.2.2 ≤ 1) (m : List F) :
    busNat (wasmBaseSegAir nloc ngl) tr pub b true m = busNat (wasmBaseSegAir nloc ngl) tr pub b false m := by
  have h := H.balance b m hx
  rwa [Nat.mod_eq_of_lt (busNat_ltXS H b true m (fun o ho hb _ => hbit o ho hb) hx),
    Nat.mod_eq_of_lt (busNat_ltXS H b false m (fun o ho hb _ => hbit o ho hb) hx)] at h

theorem msgs_permXS (b : Nat) (hx : OkBus b)
    (hbit : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = b → o.2.2.2 ≤ 1) :
    (msgs (wasmBaseSegAir nloc ngl) tr pub b true).Perm (msgs (wasmBaseSegAir nloc ngl) tr pub b false) := by
  rw [List.perm_iff_count]
  intro m
  rw [← busNat_eq_count b true (fun o ho hb _ => hbit o ho hb),
    ← busNat_eq_count b false (fun o ho hb _ => hbit o ho hb)]
  exact perm_exactXS H b hx hbit m

theorem range16_valuesXS {t : Nat} (ht : t < (wasmBaseSegAir nloc ngl).tables.length) [SegT t] (hT : (wasmBaseSegAir nloc ngl).tables[t]'ht = Range16.table) :
    tr.height t = 65536 ∧ ∀ r, r < tr.height t → rowNat tr t r Range16.val = r := by
  have hc := fun r hr => table_constrXS H ht (r := r) hr
  rw [hT] at hc
  have hh := H.heightLe t ht
  have hpos := H.heightPos t ht
  unfold maxLogHeight at hh
  have hP' := P_val
  have hv : ∀ r, r < tr.height t → rowNat tr t r Range16.val = r := by
    simp only [Range16.val]
    intro r
    induction r with
    | zero =>
      intro h0
      have := hc 0 h0 (.first * v Range16.val) (by simp [Range16.table, Range16.constraints])
      simp only [Expr.eval, natRow, Trace.row, v, Range16.val, beq_self_eq_true, ite_true] at this
      exact natEq (by rw [show ((0 : Nat) : F) = 0 from rfl]; grind) (rowNat_lt _ _ _ _) (by decide)
    | succ r ih =>
      intro hr
      have ih' := ih (by omega)
      have := hc r (by omega) (.trans * (nv Range16.val - v Range16.val - 1))
        (by simp [Range16.table, Range16.constraints])
      have hne : (r + 1 == tr.height t) = false := by simp; omega
      simp only [Expr.eval, Expr.eval_sub', Expr.eval_nxt, Expr.eval_col, Expr.eval_ofNat', natRow, Trace.row, v, nv, Range16.val, Nat.mod_eq_of_lt hr, hne,
        Bool.false_eq_true, ite_false] at this
      have e : (tr.cell t (r + 1) 0) = ((r + 1 : Nat) : F) := by
        have h1 : ((rowNat tr t r 0 : Nat) : F) = (r : F) := by rw [ih']
        simp only [rowNat, Fp.cast_toNat] at h1
        rw [Lean.Grind.Semiring.natCast_add, ← h1]
        grind
      have := congrArg Fp.toNat e
      rw [Fp.toNat_cast_of_lt (by omega)] at this
      exact this
  refine ⟨?_, hv⟩
  have := hc (tr.height t - 1) (by omega) (.last * (v Range16.val - 65535))
    (by simp [Range16.table, Range16.constraints])
  simp only [Expr.eval, Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow, Trace.row, v, Range16.val, show tr.height t - 1 + 1 = tr.height t by omega,
    beq_self_eq_true, ite_true] at this
  have hv' := hv (tr.height t - 1) (by omega)
  have e : ((rowNat tr t (tr.height t - 1) 0 : Nat) : F) = ((65535 : Nat) : F) := by grind
  have := natEq e (rowNat_lt _ _ _ _) (by decide)
  simp only [Range16.val] at hv'
  omega

/-- `regG_r16_recv` for `HoldsXS`. -/
theorem regG_r16_recvXS {ti : Nat} (hA : RegAt (wasmBaseSegAir nloc ngl) ti) :
    ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = false →
      o.2.2.2 ≠ 0 → ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536 := by
  intro o ho hb hs hc
  obtain ⟨t, ht', r', hr', i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hb hs hc
  have hT : (wasmBaseSegAir nloc ngl).tables[t]'ht' = Range16.table := by
    rcases Classical.em ((wasmBaseSegAir nloc ngl).tables[t]'ht' = Range16.table) with he | hne
    · exact he
    · exact absurd (hA.r16only _ (List.getElem_mem _) hne i hi hb) (by simp [hs])
  have : SegT t := ⟨fun h => by
    subst h
    have e : Seg.Mpath.table = Range16.table := hT
    exact absurd (congrArg Table.name e) (by decide)⟩
  obtain ⟨hh, hv⟩ := range16_valuesXS H ht' hT
  rw [hT] at hi
  simp only [Range16.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
  subst hi
  refine ⟨((r' : Nat) : F), ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    rw [row_eq_natRow]
    simp only [v, Expr.eval_col, natRow, Range16.val]
    have e : rowNat tr t r' Range16.val = r' := hv r' hr'
    simp only [Range16.val] at e ⊢
    simpa using congrArg (fun n => ((n : Nat) : F)) e
  · rw [Fp.toNat_cast_of_lt (by rw [P_val]; omega)]; omega

/-- `lookup_r16G` for `HoldsXS` (R16 is an `OkBus`). -/
theorem lookup_r16GXS
    (hsend : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1)
    (hrecv : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = false →
      o.2.2.2 ≠ 0 → ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536)
    {o : Occ} (ho : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub) (hb : o.1 = busR16)
    (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536 :=
  lookup_soundXS H busR16 (by decide) (fun m => ∃ x : F, m = [x] ∧ x.toNat < 65536) hrecv
    (fun o' ho' hb' hs' => hsend o' ho' hb' hs') ho hb hs hc

end

end WasmBase
