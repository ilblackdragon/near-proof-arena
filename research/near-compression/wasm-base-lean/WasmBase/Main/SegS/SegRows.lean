import WasmBase.Main.SegRows
import WasmBase.Main.SegHoldsS
/-!
# WasmBase.Main.SegS.SegRows — `SegRows`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegRows.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips
open Seg
set_option linter.unusedSimpArgs false

/-- **`dep` counts the `k4` rows, on the trace.** -/
theorem cuto_depS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr) :
    ∀ r, r < tr.height 31 →
      rowNat tr 31 r 59 = ((List.range (r + 1)).map fun i => rowNat tr 31 i 53).sum := by
  have ht : 31 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hc := fun r hr => table_constr_eqXS H ht Cut.Out.table (seg_t31 nloc ngl) (r := r) hr
  have hh := H.heightLe 31 ht
  have hpos := H.heightPos 31 ht
  have hP' := P_val
  unfold maxLogHeight at hh
  have mem1 : Expr.first * (Cut.Out.c "dep" - Cut.Out.c "k4") ∈ Cut.Out.table.constraints := by
    simp [Cut.Out.table, Cut.Out.constraints]
  have mem2 : Expr.trans * (Cut.Out.n "dep" - Cut.Out.c "dep" - Cut.Out.n "k4") ∈ Cut.Out.table.constraints := by
    simp [Cut.Out.table, Cut.Out.constraints]
  have mem3 : Chips.bool (Cut.Out.c "k4") ∈ Cut.Out.table.constraints := by
    simp [Cut.Out.table, Cut.Out.constraints]
  have hk : ∀ r, r < tr.height 31 → rowNat tr 31 r 53 ≤ 1 := by
    intro r hr
    have e := hc r hr _ mem3
    simp only [Chips.bool, Cut.Out.c, Cut.c, cuto_ix_k4, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
      Local.natRow] at e
    have := bool_nat (rowNat_lt tr 31 r 53) e
    omega
  have hcell : ∀ r i, tr.cell 31 r i = ((rowNat tr 31 r i : Nat) : F) := fun r i => by
    simp only [rowNat, Fp.cast_toNat]
  have key := cut_dep (fun i => rowNat tr 31 i 53) (fun i => ((rowNat tr 31 i 59 : Nat) : F)) (tr.height 31)
    (by omega) hk ?_ ?_
  · intro r hr
    have := key r hr
    rwa [Fp.toNat_cast_of_lt (rowNat_lt tr 31 r 59)] at this
  · have e := hc 0 (by omega) _ mem1
    simp only [Cut.Out.c, Cut.c, cuto_ix_dep, cuto_ix_k4, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
      Local.natRow, Expr.eval, Trace.row] at e
    simp at e
    grind
  · intro r hr
    have e := hc r (by omega) _ mem2
    simp only [Cut.Out.c, Cut.Out.n, Cut.c, Cut.n, cuto_ix_dep, cuto_ix_k4, v, nv, Expr.eval_mul',
      Expr.eval_sub', Expr.eval_col, Expr.eval_nxt, Local.natRow, Expr.eval, Trace.row,
      Nat.mod_eq_of_lt hr, hcell] at e
    have : (r + 1 == tr.height 31) = false := by simp; omega
    simp only [this] at e
    simp at e
    grind

/-- A receive with count 1 on a bus whose receive counts are bits has a matching send with a
nonzero count (the mod-`p` balance cannot be met by sends of count 0). -/
theorem recv_has_sendS {nloc ngl : Nat} {tr : Trace} {pub : List F} (H : HoldsXS nloc ngl pub tr) (b : Nat)
    (hbit : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = b → o.2.1 = false → o.2.2.2 ≤ 1)
    {o : Occ} (ho : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub) (hb : o.1 = b) (hs : o.2.1 = false) (hc : o.2.2.2 = 1)
    (hx : OkBus b := by decide) :
    ∃ o' ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o'.1 = b ∧ o'.2.1 = true ∧ o'.2.2.1 = o.2.2.1 ∧ o'.2.2.2 ≠ 0 := by
  refine Classical.byContradiction fun hn => ?_
  have h0 : busNat (wasmBaseSegAir nloc ngl) tr pub b true o.2.2.1 = 0 :=
    busNat_zero fun o' ho' hb' hs' hm' =>
      Classical.byContradiction fun hc' => hn ⟨o', ho', hb', hs', hm', hc'⟩
  have hbal := H.balance b o.2.2.1 hx
  rw [h0] at hbal
  have hge := count_le_busNat ho hb hs rfl
  have hlt := busNat_ltXS H b false o.2.2.1 hbit hx
  rw [Nat.mod_eq_of_lt hlt, Nat.zero_mod] at hbal
  omega

/-- The constraints of a `DROP` row, as naturals: `act`, `isT` bits, `isT → act`, and a nonzero
multiplicity `m` only on a tomb row. -/
theorem drop_rowS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    {r : Nat} (hr : r < tr.height 18) :
    rowNat tr 18 r 0 ≤ 1 ∧ rowNat tr 18 r 1 ≤ 1 ∧ (rowNat tr 18 r 1 = 1 → rowNat tr 18 r 0 = 1) ∧
      (rowNat tr 18 r 3 ≠ 0 → rowNat tr 18 r 1 = 1 ∧ rowNat tr 18 r 0 = 1) := by
  have ht : 18 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hc := table_constr_eqXS H ht Seg.Drop.table (seg_t18 nloc ngl) hr
  obtain ⟨i0, i1, i2, i3⟩ := drop_ix
  simp only [Seg.Drop.table, Seg.Drop.constraints, Seg.Drop.c, i0, i1, i3, Chips.bool, v,
    List.forall_mem_cons, List.forall_mem_nil, and_true, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', Local.natRow] at hc
  obtain ⟨ba, bt, e1, e2, e3⟩ := hc
  have hP := rowNat_lt tr 18 r
  have a := bool_nat (hP 0) ba
  have t := bool_nat (hP 1) bt
  have one : ((1 : Nat) : F) = 1 := rfl
  refine ⟨by omega, by omega, fun h1 => ?_, fun hm => ?_⟩
  · rcases a with a | a
    · rw [a, h1] at e1; exact absurd e1 (by decide)
    · exact a
  · have hm' : ((rowNat tr 18 r 3 : Nat) : F) ≠ 0 := fun h0 =>
      hm (natEq (R := 0) h0 (hP 3) (by decide))
    have g2 : (1 : F) - ((rowNat tr 18 r 1 : Nat) : F) = 0 := by
      rw [one] at e2; grind
    have g3 : (1 : F) - ((rowNat tr 18 r 0 : Nat) : F) = 0 := by
      rw [one] at e3; grind
    rcases t with t | t
    · rw [t] at g2; exact absurd g2 (by decide)
    rcases a with a | a
    · rw [a] at g3; exact absurd g3 (by decide)
    exact ⟨t, a⟩

/-- Receive counts on buses 12 and 13 are bits (only `DROP` receives there, with `act·isT` and
`act·(1 − isT)`). -/
theorem tomb_recv_bitsS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    (b : Nat) (hb : b = 12 ∨ b = 13) :
    ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = b → o.2.1 = false → o.2.2.2 ≤ 1 := by
  intro o ho hob hos
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hob hos
  by_cases h14 : t = 14
  · subst h14
    rw [seg_t14] at hi
    have hm : i ∈ Seg.RetT.table.inters.filter (fun i => i.bus = 12 ∨ i.bus = 13) :=
      List.mem_filter.mpr ⟨hi, by simp; omega⟩
    rw [retT_tomb] at hm
    simp only [List.mem_singleton] at hm
    subst hm; simp at hos
  by_cases h18 : t = 18
  · subst h18
    rw [seg_t18] at hi
    obtain ⟨i0, i1, i2, i3⟩ := drop_ix
    obtain ⟨ba, bt, -, -⟩ := drop_rowS H hr
    rcases drop_inters_1213 i hi (by omega) with rfl | rfl | rfl
    · simp only [Seg.Drop.c, i0, i1, Expr.eval_mul', cell_eval]
      rw [bit_mul_toNat ba bt]; exact (by have := Nat.mul_le_mul ba bt; simpa using this)
    · simp at hos
    · simp only [Seg.Drop.c, i0, i1, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', cell_eval]
      have : ((1 : Nat) : F) = 1 := rfl
      rw [this, one_sub_bit bt, bit_mul_toNat ba (by omega)]; exact (by have := Nat.mul_le_mul ba (show 1 - rowNat tr 18 r 1 ≤ 1 by omega); simpa using this)
  · have := seg_tomb_tables nloc ngl t ht h14 h18 i hi; omega

/-- **DROP drops only tombstoned activations' locals.**  If `DROP` row `r` is a drop row (`act = 1`,
`isT = 0`; it consumes a CH message in space `16 + c`), then some `DROP` row `r'` is an active tomb
row with the same `c` — it receives `[c]` on bus 12 with count 1 — and some `RET` row sends the
tombstone `[c]` with a nonzero count `tk` and has `fr_cid = c`: activation `c` has returned. -/
theorem drop_only_tombstonedS {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) {r : Nat} (hr : r < tr.height 18)
    (hact : rowNat tr 18 r 0 = 1) (hisT : rowNat tr 18 r 1 = 0) :
    (∃ r', r' < tr.height 18 ∧ rowNat tr 18 r' 0 = 1 ∧ rowNat tr 18 r' 1 = 1 ∧
      rowNat tr 18 r' 2 = rowNat tr 18 r 2) ∧
    (∃ r'', r'' < tr.height 14 ∧ (Ret.tk.eval (tr.row pub 14 r'')).toNat ≠ 0 ∧
      rowNat tr 14 r'' Ret.kCid = rowNat tr 18 r 2) := by
  have ht18 : 18 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have ht14 : 14 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  obtain ⟨i0, i1, i2, i3⟩ := drop_ix
  have hP := rowNat_lt tr
  -- the drop row's bus-13 query
  let q : Inter := ⟨Seg.busDLook, false, Seg.Drop.c "act" * (1 - Seg.Drop.c "isT"), [Seg.Drop.c "c"]⟩
  have hq : q ∈ ((wasmBaseSegAir nloc ngl).tables[18]'ht18).inters := by
    rw [seg_t18]; simp [q, Seg.Drop.table, Seg.Drop.inters]
  have hocc := (mem_occs (A := wasmBaseSegAir nloc ngl) (tr := tr) (pub := pub)).mpr ⟨18, ht18, r, hr, q, hq, rfl⟩
  have hcnt : (q.count.eval (tr.row pub 18 r)).toNat = 1 := by
    simp only [q, Seg.Drop.c, i0, i1, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', cell_eval, hact, hisT]
    decide
  obtain ⟨o', ho', hb', hs', hm', hc'⟩ := recv_has_sendS H 13 (tomb_recv_bitsS H 13 (Or.inr rfl)) hocc rfl rfl hcnt
  obtain ⟨t', ht', r', hr', i', hi', rfl⟩ := mem_occs.mp ho'
  simp only at hb' hs' hm' hc'
  -- the sender is a DROP tomb row with the same `c`
  have ht18' : t' = 18 := by
    by_cases h14 : t' = 14
    · subst h14
      rw [seg_t14] at hi'
      have hm : i' ∈ Seg.RetT.table.inters.filter (fun i => i.bus = 12 ∨ i.bus = 13) :=
        List.mem_filter.mpr ⟨hi', by simp; omega⟩
      rw [retT_tomb] at hm
      simp only [List.mem_singleton] at hm
      subst hm; simp [Seg.busTomb] at hb'
    by_cases h18 : t' = 18
    · exact h18
    · have := seg_tomb_tables nloc ngl t' ht' h14 h18 i' hi'; omega
  subst ht18'
  rw [seg_t18] at hi'
  have hcc : rowNat tr 18 r' 2 = rowNat tr 18 r 2 := by
    rcases drop_inters_1213 i' hi' (by omega) with rfl | rfl | rfl
    · simp at hs'
    · simp only [Seg.Drop.c, i2, List.map_cons, List.map_nil, cell_eval, q, List.cons.injEq, and_true] at hm'
      exact natEq hm' (hP _ _ _) (hP _ _ _)
    · simp at hs'
  have hmult : rowNat tr 18 r' 3 ≠ 0 := by
    rcases drop_inters_1213 i' hi' (by omega) with rfl | rfl | rfl
    · simp at hs'
    · simp only [Seg.Drop.c, i3, cell_eval] at hc'
      intro h0; rw [h0] at hc'; exact hc' (by decide)
    · simp at hs'
  obtain ⟨t1, a1⟩ := (drop_rowS H hr').2.2.2 hmult
  refine ⟨⟨r', hr', a1, t1, hcc⟩, ?_⟩
  -- its tomb receive (bus 12, count `act·isT = 1`) has a RET sender
  let q2 : Inter := ⟨Seg.busTomb, false, Seg.Drop.c "act" * Seg.Drop.c "isT", [Seg.Drop.c "c"]⟩
  have hq2 : q2 ∈ ((wasmBaseSegAir nloc ngl).tables[18]'ht18).inters := by
    rw [seg_t18]; simp [q2, Seg.Drop.table, Seg.Drop.inters]
  have hocc2 := (mem_occs (A := wasmBaseSegAir nloc ngl) (tr := tr) (pub := pub)).mpr ⟨18, ht18, r', hr', q2, hq2, rfl⟩
  have hcnt2 : (q2.count.eval (tr.row pub 18 r')).toNat = 1 := by
    simp only [q2, Seg.Drop.c, i0, i1, Expr.eval_mul', cell_eval, a1, t1]
    decide
  obtain ⟨o'', ho'', hb'', hs'', hm'', hc''⟩ :=
    recv_has_sendS H 12 (tomb_recv_bitsS H 12 (Or.inl rfl)) hocc2 rfl rfl hcnt2
  obtain ⟨t'', ht'', r'', hr'', i'', hi'', rfl⟩ := mem_occs.mp ho''
  simp only at hb'' hs'' hm'' hc''
  have ht14' : t'' = 14 := by
    by_cases h14 : t'' = 14
    · exact h14
    by_cases h18 : t'' = 18
    · subst h18
      rw [seg_t18] at hi''
      rcases drop_inters_1213 i'' hi'' (by omega) with rfl | rfl | rfl
      · simp at hs''
      · simp [Seg.busDLook] at hb''
      · simp at hs''
    · have := seg_tomb_tables nloc ngl t'' ht'' h14 h18 i'' hi''; omega
  subst ht14'
  rw [seg_t14] at hi''
  have hm : i'' ∈ Seg.RetT.table.inters.filter (fun i => i.bus = 12 ∨ i.bus = 13) :=
    List.mem_filter.mpr ⟨hi'', by simp; omega⟩
  rw [retT_tomb] at hm
  simp only [List.mem_singleton] at hm
  subst hm
  refine ⟨r'', hr'', hc'', ?_⟩
  simp only [List.map_cons, List.map_nil, cell_eval, q2, Seg.Drop.c, i2, List.cons.injEq, and_true] at hm''
  rw [← hcc]
  exact natEq hm'' (hP _ _ _) (hP _ _ _)

end WasmBase
