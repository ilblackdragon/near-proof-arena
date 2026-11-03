import WasmBase.Main.MemInit
/-!
# WasmBase.Main.Exec — from `Holds` to the abstract execution theorem

Assembles the per-chip row facts (`ChipFacts`) into the hypotheses of `exec_of_rows`: the bus
messages of the whole trace decompose into the boundary's messages and those of the active
instruction rows; the STATE and CH buses are exact permutations (`msgs_perm`, bit counts); the
lookups hold (`looks_of`).
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-- The instruction table at index `t ∈ [1, 10]`. -/
def chipT : Nat → Table
  | 1 => Add.table | 2 => Bit.table | 3 => Mul.table | 4 => Shift.table | 5 => Cmp.table
  | 6 => Const.table | 7 => Stack.table | 8 => Ctrl.table | 9 => Local.table | 10 => Div.table
  | 11 => Load.table | 12 => Store.table | 13 => Call.table | 14 => Ret.table
  | _ => default

theorem chipT_eq (nloc ncode t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 14) :
    (wasmBaseAir nloc ncode).tables[t]'(by simp [air_len]; omega) = chipT t := by
  rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12
    ∨ t = 13 ∨ t = 14 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Decidable shape facts of every instruction chip: one STATE receive (`inters[0]`), one STATE
send (`inters[1]`) with the same count. -/
theorem chip_state (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 14) :
    (chipT t).inters.filter (fun i => i.bus = busState ∧ i.send = false) = [(chipT t).inters.getD 0 default] ∧
    (chipT t).inters.filter (fun i => i.bus = busState ∧ i.send = true) = [(chipT t).inters.getD 1 default] ∧
    ((chipT t).inters.getD 1 default).count = ((chipT t).inters.getD 0 default).count := by
  rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12
    ∨ t = 13 ∨ t = 14 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- What each instruction chip provides (proven per chip in `WasmBase.Main.Row*`). -/
structure ChipFacts (X : Ctx) (nloc ncode : Nat) (pub : List F) (tr : Trace) : Prop where
  counts : ∀ t, 1 ≤ t → t ≤ 14 → ∀ r, r < tr.height t → ∀ i ∈ (chipT t).inters,
    (i.count.eval (tr.row pub t r)).toNat ≤ 1
  inactive : ∀ t, 1 ≤ t → t ≤ 14 → ∀ r, r < tr.height t → ¬ rowAct (chipT t) tr pub t r →
    ∀ i ∈ (chipT t).inters, (i.count.eval (tr.row pub t r)).toNat ≠ 1
  rows : Looks X nloc ncode pub tr → PubOK X nloc ncode pub → ∀ t, 1 ≤ t → t ≤ 14 → ∀ r, r < tr.height t →
    rowAct (chipT t) tr pub t r →
    RowFacts2 X (rowIn (chipT t) tr pub t r) (rowOut (chipT t) tr pub t r) (rowCons (chipT t) tr pub t r)
      (rowProd (chipT t) tr pub t r)

/-! ## Count bits of the whole trace -/

theorem first_le (tr : Trace) (pub : List F) (t r : Nat) : (Expr.first.eval (tr.row pub t r)).toNat ≤ 1 := by
  simp only [Expr.eval, Trace.row]
  by_cases h : (r == 0) = true <;> simp only [h, ite_true, ite_false, Bool.false_eq_true] <;> decide

/-- **Count bits of the base AIR, from the row constraints alone.**

The per-table content is entirely local: each case reads one row's constraints and one public-input
fact.  Stating it against `hcon` (the constraints vanish on every row) rather than `Holds` of the base
AIR is what lets the REG AIR reuse it — a REG trace satisfies the constraints of tables 0–21 but not
the base AIR's bus balance. -/
theorem occ_bits_of {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (hpub : PubOK X nloc ncode pub)
    (hcounts : ∀ t, 1 ≤ t → t ≤ 14 → ∀ r, r < tr.height t → ∀ i ∈ (chipT t).inters,
      (i.count.eval (tr.row pub t r)).toNat ≤ 1)
    (hcon : ∀ t (ht : t < (wasmBaseAir nloc ncode).tables.length) r, r < tr.height t →
      ∀ e ∈ ((wasmBaseAir nloc ncode).tables[t]'ht).constraints,
        e.eval (natRow (rowNat tr t r) (tr.row pub t r)) = 0) :
    ∀ o ∈ occs (wasmBaseAir nloc ncode) tr pub, (o.2.1 = true ∨ o.1 = busState ∨ o.1 = busStk) → o.2.2.2 ≤ 1 := by
  intro o ho hk
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := occ_table ho
  simp only at hk ⊢
  rcases table_class nloc ncode t ht with ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ |
    ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨h1, h9, -⟩
  · rw [hT] at hi
    simp only [Boundary.table, Boundary.inters, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
      List.mem_flatMap, List.mem_map, List.mem_range] at hi
    rcases hi with (((rfl | rfl | rfl) | ⟨j, _, rfl | rfl⟩) | ⟨g, _, rfl⟩) | rfl
    · exact first_le tr pub 0 r
    · exact first_le tr pub 0 r
    · -- the result receive: count `first · nres · (2 − status)` with `nres = arity ≤ 1`, status ∈ {1, 2}
      have har := X.facts.results
      have hn := hpub.nres
      simp only [Boundary.pubNres] at hn
      have hst := hpub.status
      simp only [Boundary.pubStatus] at hst
      simp only [stkRecv, chRecv, Expr.eval, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', pv, Trace.row,
        Boundary.pubNres, Boundary.pubStatus, hn, X.facts.arity]
      rcases hst with hs | hs <;> rw [hs] <;> by_cases h : (r == 0) = true
      · simp only [h, ite_true]
        rw [show (1 : F) * ((X.pf.type.results.size : Nat) : F) * (((2 : Nat) : F) - ((1 : Nat) : F)) =
          ((X.pf.type.results.size : Nat) : F) by grind, Fp.toNat_cast_of_lt (by have := P_val; omega)]; omega
      · simp only [h, ite_false, Bool.false_eq_true]
        rw [show (0 : F) * ((X.pf.type.results.size : Nat) : F) * (((2 : Nat) : F) - ((1 : Nat) : F)) =
          ((0 : Nat) : F) by grind]; decide
      · simp only [h, ite_true]
        rw [show (1 : F) * ((X.pf.type.results.size : Nat) : F) * (((2 : Nat) : F) - ((2 : Nat) : F)) =
          ((0 : Nat) : F) by grind]; decide
      · simp only [h, ite_false, Bool.false_eq_true]
        rw [show (0 : F) * ((X.pf.type.results.size : Nat) : F) * (((2 : Nat) : F) - ((2 : Nat) : F)) =
          ((0 : Nat) : F) by grind]; decide
    · exact first_le tr pub 0 r
    · exact first_le tr pub 0 r
    · exact first_le tr pub 0 r
    · exact first_le tr pub 0 r
  · rw [hT] at hi
    simp only [Code.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst hi; simp [busFetch, busState, busStk] at hk
  · -- DRAIN: count `act`, a bit
    rw [hT] at hi
    simp only [Drain.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst hi
    have hd := hcon 18 (by simp [air_len]) r hr
    have hmem : Chips.bool (v Drain.act) ∈ Drain.table.constraints := by simp [Drain.table]
    rw [← hT] at hmem
    have hb := hd (Chips.bool (v Drain.act)) hmem
    simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow,
      Drain.act] at hb
    have hb' := bool_nat (rowNat_lt _ _ _ _) hb
    simp only [chRecv, v, Expr.eval_col, Trace.row, Drain.act]
    rw [cell_cast, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)]; omega
  · rw [hT] at hi
    simp only [Range16.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst hi; simp [busR16, busState, busStk] at hk
  · rw [hT] at hi
    simp only [Byte.table, Byte.inters, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simp [busByte, busState, busStk] at hk
  · -- MEMINIT: counts `act`, `act · zd`, `act · (1 − zd)` with `act`, `zd` bits
    rw [hT] at hi
    have hc19 : ∀ e ∈ MemInit.table.constraints,
        e.eval (natRow (rowNat tr 19 r) (tr.row pub 19 r)) = 0 := by
      rw [← hT]; exact hcon 19 (by simp [air_len]) r hr
    exact meminit_counts_of hc19 i hi
  · rw [hT] at hi
    simp only [Data.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst hi; simp [busData, busState, busStk] at hk
  · rw [hT] at hi
    simp only [Func.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst hi; simp [busFunc, busState, busStk] at hk
  · have := chipT_eq nloc ncode t h1 h9
    rw [this] at hi
    exact hcounts t h1 h9 r hr i hi

theorem occ_bits {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr)
    (hpub : PubOK X nloc ncode pub) (CF : ChipFacts X nloc ncode pub tr) :
    ∀ o ∈ occs (wasmBaseAir nloc ncode) tr pub, (o.2.1 = true ∨ o.1 = busState ∨ o.1 = busStk) → o.2.2.2 ≤ 1 :=
  occ_bits_of hpub CF.counts (fun t ht r hr => table_constr H ht hr)

/-! ## Bus messages of the trace, by row -/

instance (T : Table) (tr : Trace) (pub : List F) (t r : Nat) : Decidable (rowAct T tr pub t r) := by
  unfold rowAct; infer_instance

theorem flatMap_ite_single {α β : Type} (l : List α) (p : α → Prop) [DecidablePred p] (f : α → β) :
    (l.flatMap fun r => if p r then [f r] else []) = (l.filter fun r => decide (p r)).map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a
    · simp [h, ih]
    · simp [h, ih]

theorem air_flatMap {α : Type} (nloc ncode : Nat) (G : Table → Nat → List α) :
    ((wasmBaseAir nloc ncode).tables.zipIdx.flatMap fun x => G x.1 x.2) =
      G (Boundary.table nloc ncode) 0 ++ (G (chipT 1) 1 ++ (G (chipT 2) 2 ++ (G (chipT 3) 3 ++ (G (chipT 4) 4 ++
        (G (chipT 5) 5 ++ (G (chipT 6) 6 ++ (G (chipT 7) 7 ++ (G (chipT 8) 8 ++ (G (chipT 9) 9 ++
        (G (chipT 10) 10 ++ (G (chipT 11) 11 ++ (G (chipT 12) 12 ++ (G (chipT 13) 13 ++ (G (chipT 14) 14 ++
        (G Range16.table 15 ++ (G Byte.table 16 ++
        (G Code.table 17 ++ (G Drain.table 18 ++ (G MemInit.table 19 ++ (G Data.table 20 ++
        G Func.table 21)))))))))))))))))))) := by
  simp [wasmBaseAir, List.zipIdx_cons, chipT]

theorem chip_state_true {pub : List F} {tr : Trace} (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 14)
    (r : Nat) : rowMsgs (chipT t) tr pub t r busState true =
      if rowAct (chipT t) tr pub t r then [rowOut (chipT t) tr pub t r] else [] := by
  rw [rowMsgs_eq, (chip_state t h1 h9).2.1]
  simp only [List.filterMap_cons, List.filterMap_nil]
  rw [(chip_state t h1 h9).2.2]
  unfold rowAct rowOut
  split <;> simp_all

theorem chip_state_false {pub : List F} {tr : Trace} (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 14)
    (r : Nat) : rowMsgs (chipT t) tr pub t r busState false =
      if rowAct (chipT t) tr pub t r then [rowIn (chipT t) tr pub t r] else [] := by
  rw [rowMsgs_eq, (chip_state t h1 h9).1]
  simp only [List.filterMap_cons, List.filterMap_nil]
  unfold rowAct rowIn
  split <;> simp_all

theorem chip_ch_inactive {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (CF : ChipFacts X nloc ncode pub tr) (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 14) (r : Nat) (hr : r < tr.height t)
    (hna : ¬ rowAct (chipT t) tr pub t r) (b : Nat) (s : Bool) : rowMsgs (chipT t) tr pub t r b s = [] := by
  rw [rowMsgs_eq, List.filterMap_eq_nil_iff]
  intro i hi
  rw [List.mem_filter] at hi
  simp [CF.inactive t h1 h9 r hr hna i hi.1]

/-! ## The boundary's messages -/

theorem flatMap_single {α β : Type} (f : α → β) (l : List α) : (l.flatMap fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- The boundary's initial global sends (space 2, from the public values, at time 0). -/
def globSend (nloc g : Nat) : Inter :=
  chSend 2 (Expr.c g) (pv (Boundary.pubLoc + nloc + 5 * g))
    ((List.range 4).map fun i => pv (Boundary.pubLoc + nloc + 5 * g + 1 + i)) 0 .first

/-- The boundary's initial stack-budget send (space 5, from the public values, at time 0). -/
def budSend (nloc ngl : Nat) : Inter :=
  chSend 5 0 0 [pv (Boundary.pubLoc + nloc + 5 * ngl), pv (Boundary.pubLoc + nloc + 5 * ngl + 1), 0, 0] 0 .first

theorem bnd_filters (nloc ncode : Nat) :
    (Boundary.inters nloc ncode).filter (fun i => i.bus = busState ∧ i.send = true) = [stateOut 0 1 0 0 0 0 .first] ∧
    (Boundary.inters nloc ncode).filter (fun i => i.bus = busState ∧ i.send = false) =
      [⟨busState, false, .first, [v Boundary.pcf, pv Boundary.pubN, pv Boundary.pubS, pv Boundary.pubStatus,
        v Boundary.sbf, v Boundary.cidf]⟩] ∧
    (Boundary.inters nloc ncode).filter (fun i => i.bus = busStk ∧ i.send = true) =
      (List.range nloc).map (fun j => chSend 16 (Expr.c j) (pv (Boundary.pubLoc + j)) zeros4 0 .first) ++
        (List.range ncode).map (globSend nloc) ++ [budSend nloc ncode] ∧
    (Boundary.inters nloc ncode).filter (fun i => i.bus = busStk ∧ i.send = false) =
      stkRecv 0 (pv Boundary.pubTag) ((List.range 4).map fun i => pv (Boundary.pubR + i)) (v Boundary.tpr)
        (.first * pv Boundary.pubNres * (2 - pv Boundary.pubStatus)) ::
      (List.range nloc).map (fun j => chRecv 16 (Expr.c j) (v (Boundary.fin j))
        ((List.range 4).map fun i => v (Boundary.fin j + 1 + i)) (v (Boundary.fin j + 5)) .first) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold Boundary.inters <;>
    simp only [List.filter_append, List.filter_flatMap] <;>
    simp [stateOut, chSend, chRecv, stkRecv, busState, busStk, flatMap_single, globSend, budSend, List.filter_map,
      Function.comp_def]
  rw [List.filter_eq_self.mpr (fun _ _ => rfl)]; rfl

def initRaw (nloc : Nat) (pub : List F) : List (List F) :=
  (List.range nloc).map fun j => [((16 : Nat) : F), ((j : Nat) : F), pub.getD (Boundary.pubLoc + j) 0,
    ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F)]

def globRaw (nloc ngl : Nat) (pub : List F) : List (List F) :=
  (List.range ngl).map fun g => [((2 : Nat) : F), ((g : Nat) : F), pub.getD (Boundary.pubLoc + nloc + 5 * g) 0,
    pub.getD (Boundary.pubLoc + nloc + 5 * g + 1 + 0) 0, pub.getD (Boundary.pubLoc + nloc + 5 * g + 1 + 1) 0,
    pub.getD (Boundary.pubLoc + nloc + 5 * g + 1 + 2) 0, pub.getD (Boundary.pubLoc + nloc + 5 * g + 1 + 3) 0,
    ((0 : Nat) : F)]

def budRaw (nloc ngl : Nat) (pub : List F) : List (List F) :=
  [[((5 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), pub.getD (Boundary.pubLoc + nloc + 5 * ngl) 0,
    pub.getD (Boundary.pubLoc + nloc + 5 * ngl + 1) 0, ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F)]]

def resRaw (pub : List F) (tr : Trace) : List F :=
  [((0 : Nat) : F), ((0 : Nat) : F), pub.getD Boundary.pubTag 0, pub.getD (Boundary.pubR + 0) 0,
    pub.getD (Boundary.pubR + 1) 0, pub.getD (Boundary.pubR + 2) 0, pub.getD (Boundary.pubR + 3) 0,
    tr.cell 0 0 Boundary.tpr]

def finRaw (nloc : Nat) (tr : Trace) : List (List F) :=
  (List.range nloc).map fun j => [((16 : Nat) : F), ((j : Nat) : F), tr.cell 0 0 (Boundary.fin j),
    tr.cell 0 0 (Boundary.fin j + 1 + 0), tr.cell 0 0 (Boundary.fin j + 1 + 1), tr.cell 0 0 (Boundary.fin j + 1 + 2),
    tr.cell 0 0 (Boundary.fin j + 1 + 3), tr.cell 0 0 (Boundary.fin j + 5)]

theorem first_eval (tr : Trace) (pub : List F) (t r : Nat) :
    (Expr.first.eval (tr.row pub t r)).toNat = 1 ↔ r = 0 := by
  simp only [Expr.eval, Trace.row]
  by_cases h : r = 0
  · subst h; simp; rfl
  · have : (r == 0) = false := by simp [h]
    simp only [this, Bool.false_eq_true, ite_false, h, iff_false]; decide

theorem filterMap_some_of {α β : Type} (g : α → Option β) (f : α → β) (l : List α)
    (h : ∀ x ∈ l, g x = some (f x)) : l.filterMap g = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons, h a List.mem_cons_self, List.map_cons, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem filterMap_none_of {α β : Type} (g : α → Option β) (l : List α)
    (h : ∀ x ∈ l, g x = none) : l.filterMap g = [] := by
  rw [List.filterMap_eq_nil_iff]; exact h

theorem bnd_msgs {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace} (hpub : PubOK X nloc ncode pub) (r : Nat) :
    rowMsgs (Boundary.table nloc ncode) tr pub 0 r busState true = (if r = 0 then [stMsg 0 1 0 0 0 0] else []) ∧
    rowMsgs (Boundary.table nloc ncode) tr pub 0 r busState false =
      (if r = 0 then [[tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0,
        pub.getD Boundary.pubStatus 0, tr.cell 0 0 Boundary.sbf, tr.cell 0 0 Boundary.cidf]] else []) ∧
    rowMsgs (Boundary.table nloc ncode) tr pub 0 r busStk true =
      (if r = 0 then initRaw nloc pub ++ globRaw nloc ncode pub ++ budRaw nloc ncode pub else []) ∧
    rowMsgs (Boundary.table nloc ncode) tr pub 0 r busStk false =
      (if r = 0 then (if X.ck.arity = 1 ∧ pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F) then [resRaw pub tr]
        else []) ++ finRaw nloc tr else []) := by
  obtain ⟨f1, f2, f3, f4⟩ := bnd_filters nloc ncode
  have hfe := first_eval tr pub 0 r
  have h0 : r = 0 → (Expr.first.eval (tr.row pub 0 r)).toNat = 1 := hfe.mpr
  have h1 : r ≠ 0 → ¬ (Expr.first.eval (tr.row pub 0 r)).toNat = 1 := fun h e => h (hfe.mp e)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [rowMsgs_eq] <;> simp only [Boundary.table]
  · rw [f1]; simp only [List.filterMap_cons, List.filterMap_nil, stateOut]
    by_cases h : r = 0
    · simp only [h0 h, ite_true, h]; rfl
    · simp only [h1 h, ite_false, h]
  · rw [f2]; simp only [List.filterMap_cons, List.filterMap_nil]
    by_cases h : r = 0
    · simp only [h0 h, ite_true, h]
      subst h; rfl
    · simp only [h1 h, ite_false, h]
  · rw [f3, List.filterMap_append, List.filterMap_append, List.filterMap_map, List.filterMap_map]
    by_cases h : r = 0
    · simp only [h, ite_true, initRaw, globRaw, budRaw]
      subst h
      congr 1
      · congr 1
        · apply filterMap_some_of
          intro j _
          simp only [Function.comp, chSend, h0 rfl, ite_true]
          rfl
        · apply filterMap_some_of
          intro g _
          simp only [Function.comp, globSend, chSend, h0 rfl, ite_true]
          rfl
    · simp only [h, ite_false]
      rw [filterMap_none_of _ _ (fun j _ => by simp only [Function.comp, chSend, h1 h, ite_false]),
        filterMap_none_of _ _ (fun j _ => by simp only [Function.comp, globSend, chSend, h1 h, ite_false])]
      simp only [List.filterMap_cons, List.filterMap_nil, budSend, chSend, h1 h, ite_false]
      rfl
  · rw [f4, List.filterMap_cons, List.filterMap_map]
    have har := X.facts.results
    have harity := X.facts.arity
    by_cases h : r = 0
    · subst h
      have hres : ((Expr.first * pv Boundary.pubNres * (2 - pv Boundary.pubStatus)).eval (tr.row pub 0 0)).toNat = 1 ↔
          (X.ck.arity = 1 ∧ pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F)) := by
        simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval_pub, pv, Trace.row]
        rw [show pub.getD Boundary.pubNres 0 = ((X.ck.arity : Nat) : F) from hpub.nres]
        simp only [Expr.eval, beq_self_eq_true, ite_true]
        rcases hpub.status with hs | hs <;> rw [hs]
        · rw [show (1 : F) * ((X.ck.arity : Nat) : F) * (((2 : Nat) : F) - ((1 : Nat) : F)) = ((X.ck.arity : Nat) : F) by
            grind, Fp.toNat_cast_of_lt (by have := P_val; omega)]
          simp
        · rw [show (1 : F) * ((X.ck.arity : Nat) : F) * (((2 : Nat) : F) - ((2 : Nat) : F)) = ((0 : Nat) : F) by grind]
          constructor
          · intro h; exact absurd h (by decide)
          · rintro ⟨-, h⟩; exact absurd h (by decide)
      have hrest : (List.range nloc).filterMap (((fun i => if (i.count.eval (tr.row pub 0 0)).toNat = 1 then
          some (i.msg.map (·.eval (tr.row pub 0 0))) else none) ∘ fun j => chRecv 16 (Expr.c j) (v (Boundary.fin j))
          ((List.range 4).map fun i => v (Boundary.fin j + 1 + i)) (v (Boundary.fin j + 5)) .first)) = finRaw nloc tr := by
        apply filterMap_some_of
        intro j _
        simp only [Function.comp, chRecv, h0 rfl, ite_true]
        rfl
      rw [hrest]
      simp only [ite_true, stkRecv, chRecv]
      by_cases ha : X.ck.arity = 1 ∧ pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F)
      · simp only [hres.mpr ha, ha, ite_true, List.cons_append, List.nil_append, and_self]; rfl
      · simp only [show ¬ _ = 1 from fun h => ha (hres.mp h), ha, ite_false, List.nil_append]
    · simp only [h, ite_false]
      have hres : ¬ ((Expr.first * pv Boundary.pubNres * (2 - pv Boundary.pubStatus)).eval (tr.row pub 0 r)).toNat = 1 := by
        simp only [Expr.eval_mul', Expr.eval]
        have : (r == 0) = false := by simp [h]
        simp only [Trace.row, this, Bool.false_eq_true, ite_false]
        have z : ∀ x y : F, (0 : F) * x * y = ((0 : Nat) : F) := fun x y => by grind
        rw [z]; decide
      simp only [stkRecv, chRecv, hres, ite_false]
      apply filterMap_none_of
      intro j _
      simp only [Function.comp, chRecv, h1 h, ite_false]

/-! ## The whole trace's STATE and CH messages -/

def actRows (tr : Trace) (pub : List F) (t : Nat) : List Nat :=
  (List.range (tr.height t)).filter fun r => decide (rowAct (chipT t) tr pub t r)

/-- The active instruction rows `(table, row)`. -/
def actList (tr : Trace) (pub : List F) : List (Nat × Nat) :=
  (List.range 14).flatMap fun k => (actRows tr pub (k + 1)).map fun r => (k + 1, r)

theorem flatMap_range_first {α : Type} (h : Nat) (hh : 1 ≤ h) (L : List α) :
    ((List.range h).flatMap fun r => if r = 0 then L else []) = L := by
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  simp

theorem flatMap_filter_of_nil {α β : Type} (l : List α) (p : α → Prop) [DecidablePred p] (f : α → List β)
    (h : ∀ x ∈ l, ¬ p x → f x = []) : l.flatMap f = (l.filter fun x => decide (p x)).flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    by_cases ha : p a
    · simp [ha, ih']
    · simp [ha, h a List.mem_cons_self ha, ih']

theorem fixed_nil (tr : Trace) (pub : List F) (t r : Nat) (b : Nat) (hb : b = busState ∨ b = busStk) (s : Bool) :
    rowMsgs Range16.table tr pub t r b s = [] ∧ rowMsgs Byte.table tr pub t r b s = [] ∧
      rowMsgs Code.table tr pub t r b s = [] ∧ rowMsgs Data.table tr pub t r b s = [] ∧
      rowMsgs Func.table tr pub t r b s = [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [rowMsgs_eq] <;> rcases hb with rfl | rfl <;> cases s <;>
    simp [Range16.table, Byte.table, Byte.inters, Code.table, Data.table, Func.table, busState, busStk, busR16,
      busByte, busFetch, busData, busFunc]

theorem meminit_nil (tr : Trace) (pub : List F) (t r : Nat) (b : Nat) (s : Bool) (h : b = busState ∨ s = false) :
    rowMsgs MemInit.table tr pub t r b s = [] := by
  rw [rowMsgs_eq]
  rcases h with rfl | rfl
  · cases s <;> simp [MemInit.table, MemInit.inters, chSend, r16, busState, busStk, busR16, busData]
  · simp [MemInit.table, MemInit.inters, chSend, r16, busState, busStk, busR16, busData]

theorem chip_part_true {pub : List F} {tr : Trace} (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 14) :
    ((List.range (tr.height t)).flatMap fun r => rowMsgs (chipT t) tr pub t r busState true) =
      (actRows tr pub t).map (rowOut (chipT t) tr pub t) := by
  rw [show (fun r => rowMsgs (chipT t) tr pub t r busState true) =
    (fun r => if rowAct (chipT t) tr pub t r then [rowOut (chipT t) tr pub t r] else []) from
    funext (chip_state_true t h1 h9), flatMap_ite_single]
  rfl

theorem chip_part_false {pub : List F} {tr : Trace} (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 14) :
    ((List.range (tr.height t)).flatMap fun r => rowMsgs (chipT t) tr pub t r busState false) =
      (actRows tr pub t).map (rowIn (chipT t) tr pub t) := by
  rw [show (fun r => rowMsgs (chipT t) tr pub t r busState false) =
    (fun r => if rowAct (chipT t) tr pub t r then [rowIn (chipT t) tr pub t r] else []) from
    funext (chip_state_false t h1 h9), flatMap_ite_single]
  rfl

theorem chip_part_ch {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace} (CF : ChipFacts X nloc ncode pub tr)
    (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 14) (s : Bool) :
    ((List.range (tr.height t)).flatMap fun r => rowMsgs (chipT t) tr pub t r busStk s) =
      (actRows tr pub t).flatMap fun r => rowMsgs (chipT t) tr pub t r busStk s := by
  rw [actRows, ← flatMap_filter_of_nil]
  intro r hr hna
  exact chip_ch_inactive CF t h1 h9 r (List.mem_range.mp hr) hna busStk s

theorem actList_flatMap {β : Type} (tr : Trace) (pub : List F) (f : Nat × Nat → List β) :
    (actList tr pub).flatMap f =
      (actRows tr pub 1).flatMap (fun r => f (1, r)) ++ ((actRows tr pub 2).flatMap (fun r => f (2, r)) ++ ((actRows tr pub 3).flatMap (fun r => f (3, r)) ++ ((actRows tr pub 4).flatMap (fun r => f (4, r)) ++ ((actRows tr pub 5).flatMap (fun r => f (5, r)) ++ ((actRows tr pub 6).flatMap (fun r => f (6, r)) ++ ((actRows tr pub 7).flatMap (fun r => f (7, r)) ++ ((actRows tr pub 8).flatMap (fun r => f (8, r)) ++ ((actRows tr pub 9).flatMap (fun r => f (9, r)) ++ ((actRows tr pub 10).flatMap (fun r => f (10, r)) ++ ((actRows tr pub 11).flatMap (fun r => f (11, r)) ++ ((actRows tr pub 12).flatMap (fun r => f (12, r)) ++ ((actRows tr pub 13).flatMap (fun r => f (13, r)) ++ ((actRows tr pub 14).flatMap (fun r => f (14, r))))))))))))))) := by
  simp [actList, List.flatMap_assoc, List.range, List.range.loop, List.flatMap_map]

theorem actList_map {β : Type} (tr : Trace) (pub : List F) (f : Nat × Nat → β) :
    (actList tr pub).map f =
      (actRows tr pub 1).map (fun r => f (1, r)) ++ ((actRows tr pub 2).map (fun r => f (2, r)) ++ ((actRows tr pub 3).map (fun r => f (3, r)) ++ ((actRows tr pub 4).map (fun r => f (4, r)) ++ ((actRows tr pub 5).map (fun r => f (5, r)) ++ ((actRows tr pub 6).map (fun r => f (6, r)) ++ ((actRows tr pub 7).map (fun r => f (7, r)) ++ ((actRows tr pub 8).map (fun r => f (8, r)) ++ ((actRows tr pub 9).map (fun r => f (9, r)) ++ ((actRows tr pub 10).map (fun r => f (10, r)) ++ ((actRows tr pub 11).map (fun r => f (11, r)) ++ ((actRows tr pub 12).map (fun r => f (12, r)) ++ ((actRows tr pub 13).map (fun r => f (13, r)) ++ ((actRows tr pub 14).map (fun r => f (14, r))))))))))))))) := by
  simp only [actList, List.map_flatMap, List.range, List.range.loop, List.map_map, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, Nat.reduceAdd, Nat.zero_add]
  simp only [List.map_append, List.map_map]; rfl


theorem msgs_air (nloc ncode : Nat) (tr : Trace) (pub : List F) (b : Nat) (s : Bool) :
    msgs (wasmBaseAir nloc ncode) tr pub b s =
      part (Boundary.table nloc ncode) tr pub 0 b s ++ (part (chipT 1) tr pub 1 b s ++ (part (chipT 2) tr pub 2 b s ++
      (part (chipT 3) tr pub 3 b s ++ (part (chipT 4) tr pub 4 b s ++ (part (chipT 5) tr pub 5 b s ++
      (part (chipT 6) tr pub 6 b s ++ (part (chipT 7) tr pub 7 b s ++ (part (chipT 8) tr pub 8 b s ++
      (part (chipT 9) tr pub 9 b s ++ (part (chipT 10) tr pub 10 b s ++ (part (chipT 11) tr pub 11 b s ++
      (part (chipT 12) tr pub 12 b s ++ (part (chipT 13) tr pub 13 b s ++ (part (chipT 14) tr pub 14 b s ++
      (part Range16.table tr pub 15 b s ++
      (part Byte.table tr pub 16 b s ++ (part Code.table tr pub 17 b s ++ (part Drain.table tr pub 18 b s ++
      (part MemInit.table tr pub 19 b s ++ (part Data.table tr pub 20 b s ++
      part Func.table tr pub 21 b s)))))))))))))))))))) := by
  rw [msgs_flatMap]
  simp only [wasmBaseAir, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Nat.reduceAdd]
  rfl

theorem part_fixed (tr : Trace) (pub : List F) (b : Nat) (hb : b = busState ∨ b = busStk) (s : Bool) :
    part Range16.table tr pub 15 b s = [] ∧ part Byte.table tr pub 16 b s = [] ∧
      part Code.table tr pub 17 b s = [] ∧ part Data.table tr pub 20 b s = [] ∧
      part Func.table tr pub 21 b s = [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (unfold part; rw [List.flatMap_eq_nil_iff]; intro r _)
  · exact (fixed_nil tr pub 15 r b hb s).1
  · exact (fixed_nil tr pub 16 r b hb s).2.1
  · exact (fixed_nil tr pub 17 r b hb s).2.2.1
  · exact (fixed_nil tr pub 20 r b hb s).2.2.2.1
  · exact (fixed_nil tr pub 21 r b hb s).2.2.2.2

theorem part_meminit_nil (tr : Trace) (pub : List F) (b : Nat) (s : Bool) (h : b = busState ∨ s = false) :
    part MemInit.table tr pub 19 b s = [] := by
  unfold part; rw [List.flatMap_eq_nil_iff]; intro r _
  exact meminit_nil tr pub 19 r b s h

theorem part_drain_nil (tr : Trace) (pub : List F) (b : Nat) (s : Bool) (h : b = busState ∨ s = true) :
    part Drain.table tr pub 18 b s = [] := by
  unfold part; rw [List.flatMap_eq_nil_iff]; intro r _
  rw [rowMsgs_eq]
  rcases h with rfl | rfl
  · cases s <;> simp [Drain.table, chRecv, busState, busStk]
  · simp [Drain.table, chRecv, busStk]

def drainRaw (tr : Trace) (pub : List F) : List (List F) := part Drain.table tr pub 18 busStk false


theorem msgs_state {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (hpub : PubOK X nloc ncode pub) :
    msgs (wasmBaseAir nloc ncode) tr pub busState true =
      stMsg 0 1 0 0 0 0 :: (actList tr pub).map (fun ρ => rowOut (chipT ρ.1) tr pub ρ.1 ρ.2) ∧
    msgs (wasmBaseAir nloc ncode) tr pub busState false =
      [tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0, pub.getD Boundary.pubStatus 0,
        tr.cell 0 0 Boundary.sbf, tr.cell 0 0 Boundary.cidf] ::
        (actList tr pub).map (fun ρ => rowIn (chipT ρ.1) tr pub ρ.1 ρ.2) := by
  have h0 : 1 ≤ tr.height 0 := by have := H.heightPos 0 (by simp [air_len]); omega
  obtain ⟨n1, n2, n1', nd1, nf1⟩ := part_fixed tr pub busState (Or.inl rfl) true
  obtain ⟨n3, n4, n3', nd2, nf2⟩ := part_fixed tr pub busState (Or.inl rfl) false
  have d1 := part_drain_nil tr pub busState true (Or.inl rfl)
  have d2 := part_drain_nil tr pub busState false (Or.inl rfl)
  have m1 := part_meminit_nil tr pub busState true (Or.inl rfl)
  have m2 := part_meminit_nil tr pub busState false (Or.inl rfl)
  constructor
  · rw [msgs_air, n1, n2, n1', d1, m1, nd1, nf1, actList_map]
    have hb : part (Boundary.table nloc ncode) tr pub 0 busState true = [stMsg 0 1 0 0 0 0] := by
      unfold part
      rw [show (fun r => rowMsgs (Boundary.table nloc ncode) tr pub 0 r busState true) =
        (fun r => if r = 0 then [stMsg 0 1 0 0 0 0] else []) from funext fun r => (bnd_msgs hpub r).1]
      exact flatMap_range_first _ h0 _
    rw [hb]
    simp only [part, chip_part_true 1 (by omega) (by omega), chip_part_true 2 (by omega) (by omega), chip_part_true 3 (by omega) (by omega), chip_part_true 4 (by omega) (by omega), chip_part_true 5 (by omega) (by omega), chip_part_true 6 (by omega) (by omega), chip_part_true 7 (by omega) (by omega), chip_part_true 8 (by omega) (by omega), chip_part_true 9 (by omega) (by omega), chip_part_true 10 (by omega) (by omega), chip_part_true 11 (by omega) (by omega), chip_part_true 12 (by omega) (by omega), chip_part_true 13 (by omega) (by omega), chip_part_true 14 (by omega) (by omega), List.append_nil, List.cons_append, List.nil_append]
  · rw [msgs_air, n3, n4, n3', d2, m2, nd2, nf2, actList_map]
    have hb : part (Boundary.table nloc ncode) tr pub 0 busState false =
        [[tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0,
          pub.getD Boundary.pubStatus 0, tr.cell 0 0 Boundary.sbf, tr.cell 0 0 Boundary.cidf]] := by
      unfold part
      rw [show (fun r => rowMsgs (Boundary.table nloc ncode) tr pub 0 r busState false) =
        (fun r => if r = 0 then [[tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0,
          pub.getD Boundary.pubStatus 0, tr.cell 0 0 Boundary.sbf, tr.cell 0 0 Boundary.cidf]] else [])
          from funext fun r => (bnd_msgs hpub r).2.1]
      exact flatMap_range_first _ h0 _
    rw [hb]
    simp only [part, chip_part_false 1 (by omega) (by omega), chip_part_false 2 (by omega) (by omega), chip_part_false 3 (by omega) (by omega), chip_part_false 4 (by omega) (by omega), chip_part_false 5 (by omega) (by omega), chip_part_false 6 (by omega) (by omega), chip_part_false 7 (by omega) (by omega), chip_part_false 8 (by omega) (by omega), chip_part_false 9 (by omega) (by omega), chip_part_false 10 (by omega) (by omega), chip_part_false 11 (by omega) (by omega), chip_part_false 12 (by omega) (by omega), chip_part_false 13 (by omega) (by omega), chip_part_false 14 (by omega) (by omega), List.append_nil, List.cons_append, List.nil_append]

theorem msgs_ch {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (hpub : PubOK X nloc ncode pub) (CF : ChipFacts X nloc ncode pub tr) :
    msgs (wasmBaseAir nloc ncode) tr pub busStk true =
      initRaw nloc pub ++ (globRaw nloc ncode pub ++ (budRaw nloc ncode pub ++ (actList tr pub).flatMap (fun ρ => rowMsgs (chipT ρ.1) tr pub ρ.1 ρ.2 busStk true) ++
        memRaw tr pub)) ∧
    msgs (wasmBaseAir nloc ncode) tr pub busStk false =
      (((if X.ck.arity = 1 ∧ pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F) then [resRaw pub tr] else []) ++
        finRaw nloc tr) ++
        (actList tr pub).flatMap (fun ρ => rowMsgs (chipT ρ.1) tr pub ρ.1 ρ.2 busStk false)) ++ drainRaw tr pub := by
  have h0 : 1 ≤ tr.height 0 := by have := H.heightPos 0 (by simp [air_len]); omega
  obtain ⟨n1, n2, n1', nd1, nf1⟩ := part_fixed tr pub busStk (Or.inr rfl) true
  obtain ⟨n3, n4, n3', nd2, nf2⟩ := part_fixed tr pub busStk (Or.inr rfl) false
  have d1 := part_drain_nil tr pub busStk true (Or.inr rfl)
  have m2 := part_meminit_nil tr pub busStk false (Or.inr rfl)
  constructor
  · rw [msgs_air, n1, n2, n1', d1, nd1, nf1, actList_flatMap]
    have hb : part (Boundary.table nloc ncode) tr pub 0 busStk true =
        initRaw nloc pub ++ globRaw nloc ncode pub ++ budRaw nloc ncode pub := by
      unfold part
      rw [show (fun r => rowMsgs (Boundary.table nloc ncode) tr pub 0 r busStk true) =
        (fun r => if r = 0 then initRaw nloc pub ++ globRaw nloc ncode pub ++ budRaw nloc ncode pub else []) from
          funext fun r => (bnd_msgs hpub r).2.2.1]
      exact flatMap_range_first _ h0 _
    rw [hb]
    simp only [part, chip_part_ch CF 1 (by omega) (by omega), chip_part_ch CF 2 (by omega) (by omega), chip_part_ch CF 3 (by omega) (by omega), chip_part_ch CF 4 (by omega) (by omega), chip_part_ch CF 5 (by omega) (by omega), chip_part_ch CF 6 (by omega) (by omega), chip_part_ch CF 7 (by omega) (by omega), chip_part_ch CF 8 (by omega) (by omega), chip_part_ch CF 9 (by omega) (by omega), chip_part_ch CF 10 (by omega) (by omega), chip_part_ch CF 11 (by omega) (by omega), chip_part_ch CF 12 (by omega) (by omega), chip_part_ch CF 13 (by omega) (by omega), chip_part_ch CF 14 (by omega) (by omega), List.append_nil, List.nil_append, memRaw, List.append_assoc]
  · rw [msgs_air, n3, n4, n3', m2, nd2, nf2, actList_flatMap]
    have hb : part (Boundary.table nloc ncode) tr pub 0 busStk false =
        (if X.ck.arity = 1 ∧ pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F) then [resRaw pub tr] else []) ++
          finRaw nloc tr := by
      unfold part
      rw [show (fun r => rowMsgs (Boundary.table nloc ncode) tr pub 0 r busStk false) =
        (fun r => if r = 0 then (if X.ck.arity = 1 ∧ pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F) then
          [resRaw pub tr] else []) ++ finRaw nloc tr else []) from funext fun r => (bnd_msgs hpub r).2.2.2]
      exact flatMap_range_first _ h0 _
    rw [hb]
    simp only [part, chip_part_ch CF 1 (by omega) (by omega), chip_part_ch CF 2 (by omega) (by omega), chip_part_ch CF 3 (by omega) (by omega), chip_part_ch CF 4 (by omega) (by omega), chip_part_ch CF 5 (by omega) (by omega), chip_part_ch CF 6 (by omega) (by omega), chip_part_ch CF 7 (by omega) (by omega), chip_part_ch CF 8 (by omega) (by omega), chip_part_ch CF 9 (by omega) (by omega), chip_part_ch CF 10 (by omega) (by omega), chip_part_ch CF 11 (by omega) (by omega), chip_part_ch CF 12 (by omega) (by omega), chip_part_ch CF 13 (by omega) (by omega), chip_part_ch CF 14 (by omega) (by omega), List.append_nil, List.nil_append, drainRaw, List.append_assoc]

/-! ## The initial state (function entry with an empty operand stack) -/

theorem init_rel {X : Ctx} {nloc ncode : Nat} {pub : List F} (hpub : PubOK X nloc ncode pub)
    {s0 : St} {f0 : Frame} (hfr : s0.frames = [f0]) (hfn : f0.fn = X.fn) (hpc : f0.pc = 0)
    (hlab : f0.labels = [rootLabel X.pf]) (hbase : f0.base = 0) (hloc : f0.locals = X.pf.locals.map Val.default)
    (hstk : s0.stack = #[]) (hg : s0.gas.g = X.g0)
    (M : List Msg) (hM3 : ∀ x ∈ M, x.space ≠ 0 ∧ x.space ≠ 4 ∧ x.space < 16) (hheap : HeapOK ⟨0, 0, [], (· ∈ M), 0⟩ s0 1)
    (hrem : s0.stackRem < 2 ^ 30) (hbud : ∀ x, x.space = 5 → (x ∈ M ↔ x = budMsg s0.stackRem 0))
    (hg64 : X.g0 < 2 ^ 64) :
    RelW X ⟨0, 0, [], (· ∈ M), 0⟩ s0 f0 (fun _ => 0) (fun _ => 0) 1 0 0
      (· ∈ (initRaw nloc pub).map decMsg ++ M) 0 X.g0 := by
  have CF := X.facts
  have hP' := P_val
  have hcode : 0 < X.pf.code.size := by
    have := CF.h0; rw [← CF.hsize]
    rcases h : X.ck.heights[0]? with _ | x
    · rw [h] at this; simp at this
    · exact (Array.getElem?_eq_some_iff.mp h).1
  have hnl : f0.locals.size = X.pf.locals.size := by rw [hloc]; simp
  have hp0 : X.pf.type.params = #[] := Array.eq_empty_of_size_eq_zero X.entry_params
  have hdef : ∀ j, j < X.pf.locals.size → (X.pf.locals[j]?.getD default = VT.i32 ∨ X.pf.locals[j]?.getD default = VT.i64) := by
    intro j hj
    have := CF.locTypes (X.pf.locals[j]'hj) (Array.getElem_mem_toList hj)
    rw [Array.getElem?_eq_getElem hj]; simpa using this
  refine ⟨hfr, X.nf_pos, by rw [hfn, X.fnOf_zero], hpc, hcode, ⟨_, CF.l0, by rw [hlab]; exact (shiftLabels_zero _).symm⟩, hbase,
    Nat.zero_le _, by rw [hstk]; exact CF.h0, by rw [hnl]; show _ = X.pf.type.params.size + _; rw [X.entry_params, Nat.zero_add]; rfl, by simp [hg, Ctx.R], Nat.zero_le _, hg64, by simp [hstk], ?_, by simp [hstk],
    fun _ _ => by decide, fun x h => by have := hM3 x h; simp only [Env.lsp]; omega,
    fun _ => ⟨rfl, rfl⟩, by show 0 < 2 ^ 28; decide, by show 0 < 2 ^ 28; decide, hheap,
    ⟨Nat.zero_lt_one, ⟨[], ⟨rfl, rfl⟩, fun x h => by simp [chainMsgs] at h, fun x h hs => by
      have := hM3 x h; omega, by simp [chainCharge]; exact hrem⟩, ⟨0, by decide, hbud⟩⟩, ?_⟩
  · intro j hj
    rw [hnl] at hj
    rw [hloc, Array.getElem?_map, Array.getElem?_eq_getElem hj]
    simp only [Option.map_some, Option.getD_some]
    rcases hdef j hj with h | h <;> rw [Array.getElem?_eq_getElem hj] at h <;> simp only [Option.getD_some] at h <;>
      rw [h] <;> trivial
  · intro x
    suffices e : (initRaw nloc pub).map decMsg = localView 16 f0.locals (fun _ => 0) by
      simp only [List.mem_append, e]
      simp [hstk, stackView, Env.lsp]
    unfold initRaw localView
    rw [hnl, ← hpub.hnloc, List.map_map]
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    have hj' : j < X.pf.locals.size := hpub.hnloc ▸ hj
    have ht := hpub.locTags j hj
    simp only [Function.comp, decMsg, List.getD_cons_zero, List.getD_cons_succ, ht]
    rw [hloc, Array.getElem?_map, Array.getElem?_eq_getElem hj']
    simp only [Option.map_some, Option.getD_some]
    rcases hdef j hj' with h | h <;> rw [Array.getElem?_eq_getElem hj'] at h <;> simp only [Option.getD_some] at h
    · have : X.ck.localTags.getD j 0 = 0 := by
        rw [CF.localTags, hp0]; simp [List.getD_eq_getElem?_getD, hj', h, vtTag]; decide
      have hn := CF.nloc
      rw [this]; simp only [h, enc, Val.default, vTag, vNum, Msg.mk.injEq]
      refine ⟨Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega), ?_⟩
      simp; rfl
    · have : X.ck.localTags.getD j 0 = 1 := by
        rw [CF.localTags, hp0]; simp [List.getD_eq_getElem?_getD, hj', h, vtTag]; decide
      have hn := CF.nloc
      rw [this]; simp only [h, enc, Val.default, vTag, vNum, Msg.mk.injEq]
      refine ⟨Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega), ?_⟩
      simp; rfl

/-! ## Counting the steps from the STATE chain -/

theorem chain_len {ρ : Type} [DecidableEq ρ] (act : List ρ) (inS outS : ρ → List F) (pcf N Sf hf sbf cidf : F)
    (hts : ∀ r ∈ act, lvl (outS r) = lvl (inS r) + 1)
    (hst : (stMsg 0 1 0 0 0 0 :: act.map outS).Perm ([pcf, N, Sf, hf, sbf, cidf] :: act.map inS))
    (hlen : act.length < 2 ^ 28) : act.length + 1 = N.toNat := by
  have hP' := P_val
  let g : ρ → List F × List F := fun r => (inS r, outS r)
  have hE1 : (act.map g).map Prod.snd = act.map outS := by simp [g, List.map_map]
  have hE2 : (act.map g).map Prod.fst = act.map inS := by simp [g, List.map_map]
  have hstepE : ∀ e ∈ act.map g, lvl e.2 = lvl e.1 + 1 := by
    intro e he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    exact hts r hr
  obtain ⟨es, hes, hpath⟩ := chain (act.map g) (stMsg 0 1 0 0 0 0) [pcf, N, Sf, hf, sbf, cidf] lvl
    (by rw [hE1, hE2]; exact hst) hstepE (by simp; omega)
  obtain ⟨-, lfin⟩ := path_levels lvl es _ _ hpath (fun e he => hstepE e (hes.subset he))
  have hl : es.length = act.length := by rw [hes.length_eq]; simp
  have e : lvl [pcf, N, Sf, hf, sbf, cidf] = N := rfl
  have l0 : lvl (stMsg 0 1 0 0 0 0) = 1 := rfl
  rw [e, l0, hl] at lfin
  rw [lfin, show (1 : F) + ((act.length : Nat) : F) = ((act.length + 1 : Nat) : F) by
    rw [Lean.Grind.Semiring.natCast_add, cast_one]; grind, Fp.toNat_cast_of_lt (by omega)]

/-! ## The active rows -/

theorem mem_actList {tr : Trace} {pub : List F} {ρ : Nat × Nat} (h : ρ ∈ actList tr pub) :
    1 ≤ ρ.1 ∧ ρ.1 ≤ 14 ∧ ρ.2 < tr.height ρ.1 ∧ rowAct (chipT ρ.1) tr pub ρ.1 ρ.2 := by
  simp only [actList, actRows, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq] at h
  obtain ⟨k, hk, r, ⟨hr, ha⟩, rfl⟩ := h
  exact ⟨by simp, by simp; omega, hr, ha⟩

theorem actList_length {nloc ncode : Nat} {pub : List F} {tr : Trace} (H : Holds (wasmBaseAir nloc ncode) pub tr) :
    (actList tr pub).length < 2 ^ 28 := by
  have hb : ∀ t, 1 ≤ t → t ≤ 14 → (actRows tr pub t).length ≤ 2 ^ 24 := by
    intro t h1 h9
    have := H.heightLe t (by simp [air_len]; omega)
    unfold maxLogHeight at this
    exact Nat.le_trans (List.length_filter_le _ _) (by simp; exact this)
  have e := congrArg List.length (actList_map tr pub id)
  simp only [List.map_id, List.length_append, List.length_map] at e
  rw [e]
  have := hb 1 (by omega) (by omega); have := hb 2 (by omega) (by omega); have := hb 3 (by omega) (by omega)
  have := hb 4 (by omega) (by omega); have := hb 5 (by omega) (by omega); have := hb 6 (by omega) (by omega)
  have := hb 7 (by omega) (by omega); have := hb 8 (by omega) (by omega); have := hb 9 (by omega) (by omega)
  have := hb 10 (by omega) (by omega); have := hb 11 (by omega) (by omega); have := hb 12 (by omega) (by omega)
  have := hb 13 (by omega) (by omega); have := hb 14 (by omega) (by omega)
  omega

theorem nodup_map_on {α β : Type} (f : α → β) : ∀ (l : List α), (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) →
    l.Nodup → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a l ih =>
    intro hinj hnd
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) hnd.2⟩
    intro hm
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
    have := hinj b (List.mem_cons_of_mem _ hb) a List.mem_cons_self he
    subst this; exact hnd.1 hb

theorem init_facts {X : Ctx} {nloc ncode : Nat} {pub : List F} (hpub : PubOK X nloc ncode pub) :
    ((initRaw nloc pub).map decMsg).Nodup ∧ ∀ x ∈ (initRaw nloc pub).map decMsg, x.tp = 0 := by
  have hn := X.facts.nloc
  have hP' := P_val
  rw [← hpub.hnloc] at hn
  constructor
  · unfold initRaw
    rw [List.map_map]
    have hslot : ∀ j, j < nloc → (decMsg [((16 : Nat) : F), ((j : Nat) : F), pub.getD (Boundary.pubLoc + j) 0,
        ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F)]).slot = j := by
      intro j hj; simp only [decMsg, List.getD_cons_succ, List.getD_cons_zero]; exact Fp.toNat_cast_of_lt (by omega)
    refine nodup_map_on _ _ ?_ List.nodup_range
    intro a ha b hb hab
    rw [List.mem_range] at ha hb
    have := congrArg Msg.slot hab
    simp only [Function.comp] at this
    rw [hslot a ha, hslot b hb] at this; exact this
  · intro x hx
    simp only [initRaw, List.map_map, List.mem_map, List.mem_range] at hx
    obtain ⟨j, _, rfl⟩ := hx
    rfl

/-! ## The execution theorem -/

theorem val4_limbs (n : Nat) (hn : n < 2 ^ 64) :
    val4 (n % 65536) (n / 65536 % 65536) (n / 2 ^ 32 % 65536) (n / 2 ^ 48 % 65536) = n := by
  unfold val4; omega

theorem vNum_lt64 (v : Val) : vNum v < 2 ^ 64 := by
  cases v with
  | i32 x => have := x.toNat_lt; simp only [vNum]; omega
  | i64 x => exact x.toNat_lt
  | f32 x => have := x.toNat_lt; simp only [vNum]; omega
  | f64 x => exact x.toNat_lt
  | ref _ => simp [vNum]

/-- After a normal return (status 1) DRAIN only consumes messages outside space 0 (memory). -/
theorem drain_space_of_status1 {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr)
    (hs : pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F)) : ∀ x ∈ (drainRaw tr pub).map decMsg, x.space ≠ 0 := by
  intro x hx
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  unfold drainRaw part at hm
  obtain ⟨r, hr, hm⟩ := List.mem_flatMap.mp hm
  rw [List.mem_range] at hr
  rw [rowMsgs_eq] at hm
  have hfilt : Drain.table.inters.filter (fun i => i.bus = busStk ∧ i.send = false) = Drain.table.inters := by decide
  rw [hfilt] at hm
  simp only [Drain.table, chRecv, List.filterMap_cons, List.filterMap_nil] at hm
  by_cases hc : ((v Drain.act).eval (tr.row pub 18 r)).toNat = 1
  · rw [if_pos hc] at hm
    simp only [List.mem_singleton] at hm
    subst hm
    have hcon : ∀ e ∈ Drain.table.constraints, e.eval (tr.row pub 18 r) = 0 := by
      intro e he; exact H.constr 18 (by simp [air_len]) r hr e he
    have h2 := hcon (v Drain.act * (1 - v Drain.space * v Drain.inv) * (pv Boundary.pubStatus - 2))
      (by simp [Drain.table])
    simp only [v, pv, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_pub, Expr.eval_ofNat', Trace.row,
      Drain.act, Drain.space, Drain.inv, hs] at h2 hc
    have ha : tr.cell 18 r 0 = 1 := by
      have := Fp.cast_toNat (tr.cell 18 r 0); rw [hc] at this; rw [← this]; rfl
    rw [ha] at h2
    simp only [decMsg, List.getD_cons_zero, List.map_cons, List.append_assoc, List.cons_append,
      v, Expr.eval_col, Trace.row, Drain.space]
    intro h0
    have hz : tr.cell 18 r 1 = 0 := by
      have := Fp.cast_toNat (tr.cell 18 r 1); rw [h0] at this; rw [← this]; rfl
    rw [hz] at h2
    exact absurd (show (1 : F) = 0 by grind) (by decide)
  · rw [if_neg hc] at hm; simp at hm

theorem perm_swap3 {α : Type} (A C D : List α) : ((A ++ C) ++ D).Perm ((A ++ D) ++ C) := by
  rw [List.append_assoc, List.append_assoc]; exact List.Perm.append_left A List.perm_append_comm

theorem final_stack {X : Ctx} {pub : List F} {tr : Trace} {sN : St} {tps tpl : Nat → Nat}
    {locs : Array Val} {G : Msg → Prop} (hG : ∀ x, G x → x.space ≠ 0 ∧ x.space ≠ 16)
    (Fs : List Msg) (hFs : ∀ x ∈ Fs, x.space ≠ 0)
    (hfin : ∀ x, x ∈ (if X.ck.arity = 1 then [resRaw pub tr] else []).map decMsg ++ Fs ↔
      x ∈ stackView sN.stack tps ∨ x ∈ localView 16 locs tpl ∨ G x) :
    sN.stack.size = X.ck.arity ∧
      (X.ck.arity = 1 → ∃ v, sN.stack[0]? = some v ∧ vTag v = (pub.getD Boundary.pubTag 0).toNat ∧
        vNum v = val4 (pub.getD (Boundary.pubR + 0) 0).toNat (pub.getD (Boundary.pubR + 1) 0).toNat
          (pub.getD (Boundary.pubR + 2) 0).toNat (pub.getD (Boundary.pubR + 3) 0).toNat) := by
  have har := X.facts.results
  have harity := X.facts.arity
  have hres : (decMsg (resRaw pub tr)).space = 0 ∧ (decMsg (resRaw pub tr)).slot = 0 := ⟨rfl, rfl⟩
  have hstk1 : ∀ i, i < sN.stack.size → X.ck.arity = 1 ∧ i = 0 ∧
      enc 0 i (sN.stack[i]?.getD default) (tps i) = decMsg (resRaw pub tr) := by
    intro i hi
    have hm : enc 0 i (sN.stack[i]?.getD default) (tps i) ∈ stackView sN.stack tps :=
      mem_stackView.mpr ⟨i, hi, rfl⟩
    have := (hfin _).mpr (Or.inl hm)
    rw [List.mem_append] at this
    rcases this with h | h
    · by_cases ha : X.ck.arity = 1
      · simp only [ha, ite_true] at h
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at h
        refine ⟨ha, ?_, h⟩
        have := congrArg Msg.slot h; simp only [enc] at this; rw [this]; exact hres.2
      · simp only [ha, ite_false] at h; simp at h
    · exact absurd (by simp [enc]) (hFs _ h)
  by_cases ha : X.ck.arity = 1
  · -- the result message is a live stack message, at slot 0
    have hm : decMsg (resRaw pub tr) ∈ (if X.ck.arity = 1 then [resRaw pub tr] else []).map decMsg ++ Fs := by
      simp only [ha, ite_true]; simp
    rcases (hfin _).mp hm with h | h
    · obtain ⟨i, hi, he⟩ := mem_stackView.mp h
      have hsz : sN.stack.size = 1 := by
        rcases Nat.lt_or_ge 1 sN.stack.size with h2 | h2
        · have := (hstk1 1 h2).2.1; omega
        · omega
      have hi0 : i = 0 := by omega
      subst hi0
      refine ⟨by rw [hsz, ha], fun _ => ⟨sN.stack[0]?.getD default, ?_, ?_, ?_⟩⟩
      · rw [Array.getElem?_eq_getElem (by omega)]; rfl
      · have := congrArg Msg.tag he; simp only [enc] at this; rw [← this]; rfl
      · have hv := vNum_lt64 (sN.stack[0]?.getD default)
        have e1 := congrArg Msg.l0 he; have e2 := congrArg Msg.l1 he
        have e3 := congrArg Msg.l2 he; have e4 := congrArg Msg.l3 he
        simp only [enc] at e1 e2 e3 e4
        rw [← val4_limbs _ hv, ← e1, ← e2, ← e3, ← e4]; rfl
    · rcases h with h | h
      · obtain ⟨j, _, he⟩ := mem_localView.mp h
        have := congrArg Msg.space he; simp only [enc] at this
        rw [hres.1] at this; exact absurd this (by decide)
      · exact absurd hres.1 (hG _ h).1
  · have hsz : sN.stack.size = 0 := by
      rcases Nat.eq_zero_or_pos sN.stack.size with h | h
      · exact h
      · exact absurd (hstk1 0 h).1 ha
    exact ⟨by rw [hsz]; omega, fun h => absurd h ha⟩


/-- **Explicit domain condition on the initial globals**: there are `ngl ≤ 2^16` globals, all
numeric, and the public values `[tag, l0, l1, l2, l3]` at `pubLoc + nloc + 5 g` encode global `g`. -/
def GlobOK (nloc ngl : Nat) (pub : List F) (s0 : St) : Prop :=
  s0.globals.size = ngl ∧ ngl ≤ 2 ^ 16 ∧ ∀ g, g < ngl → isNum (s0.globals[g]?.getD default) ∧
    pub.getD (Boundary.pubLoc + nloc + 5 * g) 0 = ((vTag (s0.globals[g]?.getD default) : Nat) : F) ∧
    pub.getD (Boundary.pubLoc + nloc + 5 * g + 1 + 0) 0 = ((vNum (s0.globals[g]?.getD default) % 65536 : Nat) : F) ∧
    pub.getD (Boundary.pubLoc + nloc + 5 * g + 1 + 1) 0 =
      ((vNum (s0.globals[g]?.getD default) / 65536 % 65536 : Nat) : F) ∧
    pub.getD (Boundary.pubLoc + nloc + 5 * g + 1 + 2) 0 =
      ((vNum (s0.globals[g]?.getD default) / 2 ^ 32 % 65536 : Nat) : F) ∧
    pub.getD (Boundary.pubLoc + nloc + 5 * g + 1 + 3) 0 =
      ((vNum (s0.globals[g]?.getD default) / 2 ^ 48 % 65536 : Nat) : F)

theorem vTag_le (v : Val) : vTag v ≤ 1 := by cases v <;> simp [vTag]

/-- **Explicit domain condition on the stack budget**: `stackRem < 2^30`, and the two public values
after the globals are its 16-bit limbs. -/
def BudOK (nloc ngl : Nat) (pub : List F) (s0 : St) : Prop :=
  s0.stackRem < 2 ^ 30 ∧ pub.getD (Boundary.pubLoc + nloc + 5 * ngl) 0 = ((s0.stackRem % 65536 : Nat) : F) ∧
    pub.getD (Boundary.pubLoc + nloc + 5 * ngl + 1) 0 = ((s0.stackRem / 65536 : Nat) : F)

theorem bud_view {nloc ngl : Nat} {pub : List F} {s0 : St} (h : BudOK nloc ngl pub s0) :
    (budRaw nloc ngl pub).map decMsg = [budMsg s0.stackRem 0] := by
  obtain ⟨hr, e0, e1⟩ := h
  have hP' := P_val
  simp only [budRaw, List.map_cons, List.map_nil, decMsg, List.getD_cons_zero, List.getD_cons_succ, e0, e1,
    budMsg, List.cons.injEq, and_true]
  have : s0.stackRem % 65536 < 65536 := Nat.mod_lt _ (by decide)
  simp only [Msg.mk.injEq]
  exact ⟨Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega),
    Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega),
    Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega)⟩

/-- The boundary's global sends are exactly the globals view of the initial state at time 0. -/
theorem glob_view {nloc ngl : Nat} {pub : List F} {s0 : St} (h : GlobOK nloc ngl pub s0) :
    (globRaw nloc ngl pub).map decMsg = globView s0.globals (fun _ => 0) := by
  obtain ⟨hsz, hle, hg⟩ := h
  have hP' := P_val
  have hm : ∀ n, n % 65536 < P := fun n => by have := Nat.mod_lt n (show 65536 > 0 by decide); omega
  unfold globRaw globView
  rw [List.map_map, hsz]
  apply List.map_congr_left
  intro g hg'
  rw [List.mem_range] at hg'
  obtain ⟨_, e0, e1, e2, e3, e4⟩ := hg g hg'
  simp only [Function.comp, decMsg, List.getD_cons_zero, List.getD_cons_succ, e0, e1, e2, e3, e4, enc, Msg.mk.injEq]
  have := vTag_le (s0.globals[g]?.getD default)
  exact ⟨Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega),
    Fp.toNat_cast_of_lt (hm _), Fp.toNat_cast_of_lt (hm _), Fp.toNat_cast_of_lt (hm _), Fp.toNat_cast_of_lt (hm _),
    Fp.toNat_cast_of_lt (by omega)⟩

theorem globView_nodup (gs : Array Val) (tpg : Nat → Nat) : (globView gs tpg).Nodup := by
  unfold globView
  refine nodup_map_on _ _ (fun a _ b _ hab => ?_) List.nodup_range
  have := congrArg Msg.slot hab; simpa [enc] using this

/-- **Base-faithful execution theorem.**  If the AIR relation holds for `wasmBaseAir` with the
public inputs the verifier derives from the checker (`PubOK`), the cached CODE table is the checked
code (`CodeOK`), every instruction chip satisfies its row lemma (`ChipFacts`), and the explicit
domain conditions on the public values hold, then the spec `run` from function entry ends after
exactly `N - 1` steps, having charged `R · S` gas: with status 1 it returns with the operand stack
equal to the public result; with status 2 it traps. -/
theorem wasm_base_exec (X : Ctx) {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (hpub : PubOK X nloc ncode pub)
    (CF : ChipFacts X nloc ncode pub tr) (hcode : CodeOK X tr) (hfunc : FuncOK X tr)
    (hfeeN : (pub.getD Boundary.pubN 0).toNat * (X.maxFee + 1) < P)
    (hgas : X.R * (pub.getD Boundary.pubS 0).toNat ≤ X.g0) (hg64 : X.g0 < 2 ^ 64)
    {s0 : St} {f0 : Frame} (hfr : s0.frames = [f0]) (hfn : f0.fn = X.fn) (hpc : f0.pc = 0)
    (hlab : f0.labels = [rootLabel X.pf]) (hbase : f0.base = 0) (hloc : f0.locals = X.pf.locals.map Val.default)
    (hstk : s0.stack = #[]) (hg : s0.gas.g = X.g0) (hpok : PagesOK s0)
    (hdata : DataOK s0 tr) (hM : pub.getD Boundary.pubMem 0 = ((memBytes s0 : Nat) : F))
    (hMle : memBytes s0 ≤ 2 ^ 27) (hDE : (pub.getD Boundary.pubDataEnd 0).toNat ≤ 2 ^ 27)
    (hzero : ∀ a, (pub.getD Boundary.pubDataEnd 0).toNat ≤ a → readByte s0 a = 0)
    (hglob : GlobOK nloc ncode pub s0) (hbudg : BudOK nloc ncode pub s0) :
    (pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F) →
      ∃ sN, run X.cfg X.p ((pub.getD Boundary.pubN 0).toNat - 1) s0 = .fin sN ∧ sN.frames = [] ∧
        X.R * (pub.getD Boundary.pubS 0).toNat + sN.gas.g = X.g0 ∧
        sN.stack.size = X.ck.arity ∧
        (X.ck.arity = 1 → ∃ v, sN.stack[0]? = some v ∧ vTag v = (pub.getD Boundary.pubTag 0).toNat ∧
          vNum v = val4 (pub.getD (Boundary.pubR + 0) 0).toNat (pub.getD (Boundary.pubR + 1) 0).toNat
            (pub.getD (Boundary.pubR + 2) 0).toNat (pub.getD (Boundary.pubR + 3) 0).toNat)) ∧
    (pub.getD Boundary.pubStatus 0 = ((2 : Nat) : F) →
      ∃ sN e, run X.cfg X.p ((pub.getD Boundary.pubN 0).toNat - 1) s0 = .abort sN e ∧
        X.R * (pub.getD Boundary.pubS 0).toNat + sN.gas.g = X.g0) := by
  have hP' := P_val
  have hbits := occ_bits H hpub CF
  have L := looks_of H hcode hfunc (fun o ho hs => hbits o ho (Or.inl hs))
  obtain ⟨ms1, ms2⟩ := msgs_state H hpub
  have hstP := msgs_perm H busState (fun o ho hb => hbits o ho (Or.inr (Or.inl hb)))
  rw [ms1, ms2] at hstP
  obtain ⟨mc1, mc2⟩ := msgs_ch H hpub CF
  have hchP := (msgs_perm H busStk (fun o ho hb => hbits o ho (Or.inr (Or.inr hb)))).map decMsg
  rw [mc1, mc2] at hchP
  simp only [List.map_append, List.map_flatMap] at hchP
  -- initial memory messages next to the initial locals; drained messages next to the final ones
  have hsend : ∀ o ∈ occs (wasmBaseAir nloc ncode) tr pub, o.2.1 = true → o.2.2.2 ≤ 1 :=
    fun o ho hs => hbits o ho (Or.inl hs)
  obtain ⟨mnd, mtp, mT, mtpm, mTnd, mTlt, mTtp, mview⟩ := meminit_init H L hdata hsend hM hMle hDE hzero
  have hgv := glob_view hglob
  have hbv := bud_view hbudg
  have gsp : ∀ x ∈ (globRaw nloc ncode pub).map decMsg, x.space = 2 ∧ x.tp = 0 := by
    intro x hx; rw [hgv] at hx; obtain ⟨g, _, rfl⟩ := mem_globView.mp hx; exact ⟨rfl, rfl⟩
  have bsp : ∀ x ∈ (budRaw nloc ncode pub).map decMsg, x.space = 5 ∧ x.tp = 0 := by
    intro x hx; rw [hbv, List.mem_singleton] at hx; subst hx; exact ⟨rfl, rfl⟩
  have gnd : ((globRaw nloc ncode pub).map decMsg).Nodup := by rw [hgv]; exact globView_nodup _ _
  have bnd : ((budRaw nloc ncode pub).map decMsg).Nodup := by rw [hbv]; simp
  have hheap : HeapOK ⟨0, 0, [], (· ∈ (globRaw nloc ncode pub).map decMsg ++ ((budRaw nloc ncode pub).map decMsg ++
      (memRaw tr pub).map decMsg)), 0⟩ s0 1 := by
    refine ⟨hpok, ⟨mT, mtpm, mTnd, mTlt, mTtp, fun x hx => ?_⟩,
      ⟨fun _ => 0, fun g hg => ⟨Nat.zero_lt_one, (hglob.2.2 g (by rw [← hglob.1]; exact hg)).1⟩, fun x hx => ?_⟩⟩
    · show x ∈ _ ++ (_ ++ _) ↔ _
      rw [List.mem_append, List.mem_append, ← mview x hx]
      constructor
      · rintro (h | h | h)
        · have := (gsp x h).1; omega
        · have := (bsp x h).1; omega
        · exact h
      · exact fun h => Or.inr (Or.inr h)
    · show x ∈ _ ++ (_ ++ _) ↔ _
      rw [List.mem_append, List.mem_append, ← hgv]
      constructor
      · rintro (h | h | h)
        · exact h
        · have := (bsp x h).1; omega
        · have := (mtp x h).2; omega
      · exact Or.inl
  have hL : ((initRaw nloc pub).map decMsg ++ ((globRaw nloc ncode pub).map decMsg ++ ((budRaw nloc ncode pub).map decMsg ++
      ((actList tr pub).flatMap (fun a => (rowMsgs (chipT a.1) tr pub a.1 a.2 busStk true).map decMsg) ++
        (memRaw tr pub).map decMsg)))).Perm
      (((initRaw nloc pub).map decMsg ++ ((globRaw nloc ncode pub).map decMsg ++ ((budRaw nloc ncode pub).map decMsg ++
        (memRaw tr pub).map decMsg))) ++
        (actList tr pub).flatMap (fun a => (rowMsgs (chipT a.1) tr pub a.1 a.2 busStk true).map decMsg)) := by
    simp only [List.append_assoc]
    exact List.Perm.append_left _ (List.Perm.append_left _ (List.Perm.append_left _ List.perm_append_comm))
  have hchP' := hL.symm.trans (hchP.trans (perm_swap3 _ _ _))
  have hrows : ∀ ρ ∈ actList tr pub, RowFacts2 X (rowIn (chipT ρ.1) tr pub ρ.1 ρ.2)
      (rowOut (chipT ρ.1) tr pub ρ.1 ρ.2) (rowCons (chipT ρ.1) tr pub ρ.1 ρ.2) (rowProd (chipT ρ.1) tr pub ρ.1 ρ.2) := by
    intro ρ hρ
    obtain ⟨h1, h9, hr, ha⟩ := mem_actList hρ
    exact CF.rows L hpub ρ.1 h1 h9 ρ.2 hr ha
  have hlen := actList_length H
  obtain ⟨hnd0, htp0⟩ := init_facts hpub
  have hsp16 : ∀ x ∈ (initRaw nloc pub).map decMsg, x.space = 16 := by
    intro x hx
    simp only [initRaw, List.map_map, List.mem_map, List.mem_range] at hx
    obtain ⟨j, _, rfl⟩ := hx; exact Fp.toNat_cast_of_lt (by rw [P_val]; omega)
  have hMsp : ∀ x ∈ (globRaw nloc ncode pub).map decMsg ++ ((budRaw nloc ncode pub).map decMsg ++
      (memRaw tr pub).map decMsg), x.space ≠ 0 ∧ x.space ≠ 4 ∧ x.space < 16 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · have := (gsp x h).1; omega
    · rcases List.mem_append.mp h with h | h
      · have := (bsp x h).1; omega
      · have := (mtp x h).2; omega
  have hnd : ((initRaw nloc pub).map decMsg ++ ((globRaw nloc ncode pub).map decMsg ++
      ((budRaw nloc ncode pub).map decMsg ++ (memRaw tr pub).map decMsg))).Nodup := by
    rw [List.nodup_append, List.nodup_append, List.nodup_append]
    refine ⟨hnd0, ⟨gnd, ⟨bnd, mnd, fun x hx y hy hxy => ?_⟩, fun x hx y hy hxy => ?_⟩, fun x hx y hy hxy => ?_⟩
    · subst hxy; have := (bsp x hx).1; have := (mtp x hy).2; omega
    · subst hxy; have := (gsp x hx).1
      rcases List.mem_append.mp hy with h | h
      · have := (bsp x h).1; omega
      · have := (mtp x h).2; omega
    · subst hxy; have := hsp16 x hx; have := (hMsp x hy).2.2; omega
  have htp : ∀ x ∈ (initRaw nloc pub).map decMsg ++ ((globRaw nloc ncode pub).map decMsg ++
      ((budRaw nloc ncode pub).map decMsg ++ (memRaw tr pub).map decMsg)), x.tp = 0 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact htp0 x h
    · rcases List.mem_append.mp h with h | h
      · exact (gsp x h).2
      · rcases List.mem_append.mp h with h | h
        · exact (bsp x h).2
        · exact (mtp x h).1
  have h0 := init_rel hpub hfr hfn hpc hlab hbase hloc hstk hg
    ((globRaw nloc ncode pub).map decMsg ++ ((budRaw nloc ncode pub).map decMsg ++ (memRaw tr pub).map decMsg))
    hMsp hheap hbudg.1 (fun x hx => by
      rw [List.mem_append, List.mem_append, hbv, List.mem_singleton]
      constructor
      · rintro (h | h | h)
        · have := (gsp x h).1; omega
        · exact h
        · have := (mtp x h).2; omega
      · exact fun h => Or.inr (Or.inl h)) hg64
  have run_eq : ∀ r, run X.cfg X.p (actList tr pub).length s0 = r →
      (actList tr pub).length + 1 = (pub.getD Boundary.pubN 0).toNat →
      run X.cfg X.p ((pub.getD Boundary.pubN 0).toNat - 1) s0 = r := by
    intro r hr hN; rw [show (pub.getD Boundary.pubN 0).toNat - 1 = (actList tr pub).length by omega]; exact hr
  constructor
  · intro hs
    rw [hs] at hstP
    have hN := chain_len (actList tr pub) (fun ρ => rowIn (chipT ρ.1) tr pub ρ.1 ρ.2)
      (fun ρ => rowOut (chipT ρ.1) tr pub ρ.1 ρ.2) _ _ _ _ _ _ (fun ρ hρ => (hrows ρ hρ).tsOut) hstP hlen
    have hfee : ((actList tr pub).length + 1) * (X.maxFee + 1) < P := by rw [hN]; exact hfeeN
    obtain ⟨-, h1, -⟩ := exec_of_rows X (actList tr pub) (fun ρ => rowIn (chipT ρ.1) tr pub ρ.1 ρ.2)
      (fun ρ => rowOut (chipT ρ.1) tr pub ρ.1 ρ.2) (fun ρ => rowCons (chipT ρ.1) tr pub ρ.1 ρ.2)
      (fun ρ => rowProd (chipT ρ.1) tr pub ρ.1 ρ.2) _ _ _ _ _ 1 (Or.inl rfl) hrows _ _ hstP hchP' hnd htp hlen hfee
      0 X.g0 (by simp) hgas hg64 (by exact ⟨rfl, rfl, rfl⟩) h0
    obtain ⟨sN, tps, tpl, locs, hrun, hfrN, hgasN, G, hG, hfin⟩ := h1 rfl
    refine ⟨sN, run_eq _ hrun hN, hfrN, hgasN, ?_⟩
    have hdr := drain_space_of_status1 H hs
    simp only [hs, and_true, List.append_assoc] at hfin
    refine final_stack hG ((finRaw nloc tr).map decMsg ++ (drainRaw tr pub).map decMsg) ?_ hfin
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · have : x.space = 16 := by
        simp only [finRaw, List.map_map, List.mem_map, List.mem_range] at h
        obtain ⟨j, _, rfl⟩ := h; exact Fp.toNat_cast_of_lt (by rw [P_val]; omega)
      omega
    · exact hdr x h
  · intro hs
    rw [hs] at hstP
    have hN := chain_len (actList tr pub) (fun ρ => rowIn (chipT ρ.1) tr pub ρ.1 ρ.2)
      (fun ρ => rowOut (chipT ρ.1) tr pub ρ.1 ρ.2) _ _ _ _ _ _ (fun ρ hρ => (hrows ρ hρ).tsOut) hstP hlen
    have hfee : ((actList tr pub).length + 1) * (X.maxFee + 1) < P := by rw [hN]; exact hfeeN
    obtain ⟨-, -, h2⟩ := exec_of_rows X (actList tr pub) (fun ρ => rowIn (chipT ρ.1) tr pub ρ.1 ρ.2)
      (fun ρ => rowOut (chipT ρ.1) tr pub ρ.1 ρ.2) (fun ρ => rowCons (chipT ρ.1) tr pub ρ.1 ρ.2)
      (fun ρ => rowProd (chipT ρ.1) tr pub ρ.1 ρ.2) _ _ _ _ _ 2 (Or.inr rfl) hrows _ _ hstP hchP' hnd htp hlen hfee
      0 X.g0 (by simp) hgas hg64 (by exact ⟨rfl, rfl, rfl⟩) h0
    obtain ⟨sN, e, hrun, hgasN⟩ := h2 rfl
    exact ⟨sN, e, run_eq _ hrun hN, hgasN⟩

end WasmBase
