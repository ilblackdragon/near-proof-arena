import WasmBase.Main.Abstract
import WasmBase.Extract.Row
import WasmBase.Extract.Byte
import WasmBase.Extract.Occ
/-!
# WasmBase.Main.Lookups — what the lookup buses (FETCH, R16, BYTE) guarantee

From `Holds` alone (lookup soundness, `WasmBase.Bus.lookup_sound`) and bit-valued query counts:
every FETCH query with count 1 is one of the public code records, every R16 query is a value
`< 2^16`, and every BYTE query `[k, x, y, z]` has bytes `x, y` and `z = byteF k x y`.
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-- Global code record `j` of the checked module, as field elements. -/
def codeRec (X : Ctx) (j : Nat) : List F := (X.M.records[j]?.getD []).map fun x => ((x : Nat) : F)

/-- **Statement binding of the cached CODE table.**  V_d recomputes `code_root` from the contract code
(`code_hash`) as the commitment to the canonical CODE matrix (the records in pc order, padded by
repeating the last record) and checks it equals the cached commitment the proof carries; so, under
the binding of the commitment, every CODE row's record columns are a record of the checked code.
This is the one hypothesis the commitment contributes. -/
def CodeOK (X : Ctx) (tr : Trace) : Prop :=
  ∀ r, r < tr.height 17 → ∃ j, j < X.M.codeSize ∧
    (List.range Boundary.recWidth).map (fun k => tr.cell 17 r k) = codeRec X j

/-- Function-table row `k` of the checked module, as field elements. -/
def funcRec (X : Ctx) (k : Nat) : List F := (X.M.funcs.getD k []).map fun x => ((x : Nat) : F)

/-- **Statement binding of the cached FUNC table** (like CODE): every FUNC row's columns are the
function-table row of a checked function. -/
def FuncOK (X : Ctx) (tr : Trace) : Prop :=
  ∀ r, r < tr.height 21 → ∃ k, k < X.nf ∧ (List.range 8).map (fun i => tr.cell 21 r i) = funcRec X k

/-! ## Which tables receive on the lookup buses (decidable) -/

theorem recv_only_gen {b : Nat} {L : List Table}
    (h : L.all (fun T => T.inters.all fun i => i.bus != b || i.send) = true) :
    ∀ T ∈ L, ∀ i ∈ T.inters, i.bus = b → i.send = true := by
  intro T hT i hi hb
  have := List.all_eq_true.mp (List.all_eq_true.mp h T hT) i hi
  simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h | h
  · exact absurd hb h
  · exact h

theorem recv_only_code_fetch :
    ∀ T ∈ [Add.table, Bit.table, Mul.table, Shift.table, Cmp.table, Const.table, Stack.table, Ctrl.table,
      Local.table, Div.table, Load.table, Store.table, Call.table, Ret.table, Range16.table, Byte.table,
      Drain.table, MemInit.table, Data.table, Func.table], ∀ i ∈ T.inters, i.bus = busFetch → i.send = true :=
  recv_only_gen (by decide)

theorem recv_only_range16 :
    ∀ T ∈ [Add.table, Bit.table, Mul.table, Shift.table, Cmp.table, Const.table, Stack.table, Ctrl.table,
      Local.table, Div.table, Load.table, Store.table, Call.table, Ret.table, Byte.table, Code.table, Drain.table,
      MemInit.table, Data.table, Func.table], ∀ i ∈ T.inters, i.bus = busR16 → i.send = true :=
  recv_only_gen (by decide)

theorem recv_only_byte :
    ∀ T ∈ [Add.table, Bit.table, Mul.table, Shift.table, Cmp.table, Const.table, Stack.table, Ctrl.table,
      Local.table, Div.table, Load.table, Store.table, Call.table, Ret.table, Range16.table, Code.table,
      Drain.table, MemInit.table, Data.table, Func.table], ∀ i ∈ T.inters, i.bus = busByte → i.send = true :=
  recv_only_gen (by decide)

theorem recv_only_data :
    ∀ T ∈ [Add.table, Bit.table, Mul.table, Shift.table, Cmp.table, Const.table, Stack.table, Ctrl.table,
      Local.table, Div.table, Load.table, Store.table, Call.table, Ret.table, Range16.table, Byte.table,
      Code.table, Drain.table, MemInit.table, Func.table], ∀ i ∈ T.inters, i.bus = busData → i.send = true :=
  recv_only_gen (by decide)

theorem recv_only_func :
    ∀ T ∈ [Add.table, Bit.table, Mul.table, Shift.table, Cmp.table, Const.table, Stack.table, Ctrl.table,
      Local.table, Div.table, Load.table, Store.table, Call.table, Ret.table, Range16.table, Byte.table,
      Code.table, Drain.table, MemInit.table, Data.table], ∀ i ∈ T.inters, i.bus = busFunc → i.send = true :=
  recv_only_gen (by decide)

theorem boundary_lookups (nloc ncode : Nat) :
    ∀ i ∈ Boundary.inters nloc ncode, i.bus ≠ busR16 ∧ i.bus ≠ busByte ∧ i.bus ≠ busFetch ∧ i.bus ≠ busData ∧
      i.bus ≠ busFunc := by
  intro i hi
  simp only [Boundary.inters, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_flatMap,
    List.mem_map, List.mem_range] at hi
  rcases hi with (((rfl | rfl | rfl) | ⟨j, _, rfl | rfl⟩) | ⟨g, _, rfl⟩) | rfl <;>
    simp [stateOut, chSend, chRecv, stkRecv, busState, busStk, busR16, busByte, busFetch, busData, busFunc]

/-! ## Lookup consequences -/

/-- The occurrence list splits by table index. -/
theorem occ_table {nloc ncode : Nat} {tr : Trace} {pub : List F} {o : Occ}
    (ho : o ∈ occs (wasmBaseAir nloc ncode) tr pub) :
    ∃ t, ∃ ht : t < 22, ∃ r, r < tr.height t ∧
      ∃ i ∈ ((wasmBaseAir nloc ncode).tables[t]'(by simp [air_len]; exact ht)).inters,
        o = (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat) := by
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  exact ⟨t, by simpa [air_len] using ht, r, hr, i, hi, rfl⟩

structure Looks (X : Ctx) (nloc ncode : Nat) (pub : List F) (tr : Trace) : Prop where
  fetch : ∀ o ∈ occs (wasmBaseAir nloc ncode) tr pub, o.1 = busFetch → o.2.1 = true → o.2.2.2 = 1 →
    ∃ j, j < X.M.codeSize ∧ o.2.2.1 = codeRec X j
  r16 : ∀ o ∈ occs (wasmBaseAir nloc ncode) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 = 1 →
    ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536
  byte : ∀ o ∈ occs (wasmBaseAir nloc ncode) tr pub, o.1 = busByte → o.2.1 = true → o.2.2.2 = 1 →
    ∃ k x y, k < 4 ∧ x < 256 ∧ y < 256 ∧
      o.2.2.1 = [((k : Nat) : F), ((x : Nat) : F), ((y : Nat) : F), ((byteF k x y : Nat) : F)]
  func : ∀ o ∈ occs (wasmBaseAir nloc ncode) tr pub, o.1 = busFunc → o.2.1 = true → o.2.2.2 = 1 →
    ∃ k, k < X.nf ∧ o.2.2.1 = funcRec X k

/-! ## The BYTE table rows answer exactly `byteF` -/

theorem byte_row_msgs {A : Air} {pub : List F} {tr : Trace} (H : Holds A pub tr) {t : Nat}
    (ht : t < A.tables.length) (hT : A.tables[t]'ht = Byte.table) {r : Nat} (hr : r < tr.height t) :
    ∀ i ∈ Byte.inters, ∃ k x y, k < 4 ∧ x < 256 ∧ y < 256 ∧
      i.msg.map (·.eval (tr.row pub t r)) =
        [((k : Nat) : F), ((x : Nat) : F), ((y : Nat) : F), ((byteF k x y : Nat) : F)] := by
  have hb := byte_bits H ht hT hr
  have hx := bits8_lt (fun i => rowNat tr t r i) (fun i hi => hb i (by omega))
  have hy := bits8_lt (fun i => rowNat tr t r (8 + i)) (fun i hi => hb (8 + i) (by omega))
  have eX : Byte.X.eval (natRow (rowNat tr t r) (tr.row pub t r)) = ((bits8 fun i => rowNat tr t r i : Nat) : F) := by
    simp only [Byte.X, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add', Expr.eval_mul',
      Expr.eval_c, Expr.eval_col, natRow, v, Byte.xb, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat']
    exact cast_bits8 _
  have eY : Byte.Y.eval (natRow (rowNat tr t r) (tr.row pub t r)) = ((bits8 fun i => rowNat tr t r (8 + i) : Nat) : F) := by
    simp only [Byte.Y, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add', Expr.eval_mul',
      Expr.eval_c, Expr.eval_col, natRow, v, Byte.yb, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat']
    exact cast_bits8 (fun i => rowNat tr t r (8 + i))
  have hb' : ∀ i, i < 16 → rowNat tr t r i ≤ 1 := hb
  have hop : ∀ (op : Nat → Nat → Nat) (fb : Bool → Bool → Bool),
      (∀ x y i, (op x y).testBit i = fb (x.testBit i) (y.testBit i)) → (∀ a b, a ≤ 1 → b ≤ 1 → op a b ≤ 1) →
      bits8 (fun i => op (rowNat tr t r i) (rowNat tr t r (8 + i))) =
        op (bits8 fun i => rowNat tr t r i) (bits8 fun i => rowNat tr t r (8 + i)) := fun op fb h1 h2 =>
    (bits8_op fb op h1 h2 _ _ (fun i hi => hb i (by omega)) (fun i hi => hb (8 + i) (by omega))).symm
  have eAnd : Byte.andE.eval (natRow (rowNat tr t r) (tr.row pub t r)) =
      (((bits8 fun i => rowNat tr t r i) &&& (bits8 fun i => rowNat tr t r (8 + i)) : Nat) : F) := by
    rw [← hop (· &&& ·) (· && ·) (fun x y i => Nat.testBit_and x y i)
      (fun a b ha hb => by rw [and_bit ha hb]; rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> simp <;> omega)]
    simp only [Byte.andE, Byte.bitsum, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add',
      Expr.eval_mul', Expr.eval_c, Expr.eval_col, natRow, v, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat']
    simp only [Nat.reduceAdd, cast_and_bit (hb 0 (by decide)) (hb 8 (by decide)), cast_and_bit (hb 1 (by decide)) (hb 9 (by decide)), cast_and_bit (hb 2 (by decide)) (hb 10 (by decide)), cast_and_bit (hb 3 (by decide)) (hb 11 (by decide)), cast_and_bit (hb 4 (by decide)) (hb 12 (by decide)), cast_and_bit (hb 5 (by decide)) (hb 13 (by decide)), cast_and_bit (hb 6 (by decide)) (hb 14 (by decide)), cast_and_bit (hb 7 (by decide)) (hb 15 (by decide))]
    exact cast_bits8 (fun i => rowNat tr t r i &&& rowNat tr t r (8 + i))
  have eOr : Byte.orE.eval (natRow (rowNat tr t r) (tr.row pub t r)) =
      (((bits8 fun i => rowNat tr t r i) ||| (bits8 fun i => rowNat tr t r (8 + i)) : Nat) : F) := by
    rw [← hop (· ||| ·) (· || ·) (fun x y i => Nat.testBit_or x y i)
      (fun a b ha hb => by rw [or_bit ha hb]; rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> simp <;> omega)]
    simp only [Byte.orE, Byte.bitsum, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add',
      Expr.eval_mul', Expr.eval_sub', Expr.eval_c, Expr.eval_col, natRow, v, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat']
    simp only [Nat.reduceAdd, cast_or_bit (hb 0 (by decide)) (hb 8 (by decide)), cast_or_bit (hb 1 (by decide)) (hb 9 (by decide)), cast_or_bit (hb 2 (by decide)) (hb 10 (by decide)), cast_or_bit (hb 3 (by decide)) (hb 11 (by decide)), cast_or_bit (hb 4 (by decide)) (hb 12 (by decide)), cast_or_bit (hb 5 (by decide)) (hb 13 (by decide)), cast_or_bit (hb 6 (by decide)) (hb 14 (by decide)), cast_or_bit (hb 7 (by decide)) (hb 15 (by decide))]
    exact cast_bits8 (fun i => rowNat tr t r i ||| rowNat tr t r (8 + i))
  have eXor : Byte.xorE.eval (natRow (rowNat tr t r) (tr.row pub t r)) =
      (((bits8 fun i => rowNat tr t r i) ^^^ (bits8 fun i => rowNat tr t r (8 + i)) : Nat) : F) := by
    rw [← hop (· ^^^ ·) (fun a b => a ^^ b) (fun x y i => Nat.testBit_xor x y i)
      (fun a b ha hb => by rw [xor_bit ha hb]; rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> simp <;> omega)]
    simp only [Byte.xorE, Byte.bitsum, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add',
      Expr.eval_mul', Expr.eval_sub', Expr.eval_c, Expr.eval_col, natRow, v, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat']
    simp only [Nat.reduceAdd, cast_xor_bit (hb 0 (by decide)) (hb 8 (by decide)), cast_xor_bit (hb 1 (by decide)) (hb 9 (by decide)), cast_xor_bit (hb 2 (by decide)) (hb 10 (by decide)), cast_xor_bit (hb 3 (by decide)) (hb 11 (by decide)), cast_xor_bit (hb 4 (by decide)) (hb 12 (by decide)), cast_xor_bit (hb 5 (by decide)) (hb 13 (by decide)), cast_xor_bit (hb 6 (by decide)) (hb 14 (by decide)), cast_xor_bit (hb 7 (by decide)) (hb 15 (by decide))]
    exact cast_bits8 (fun i => rowNat tr t r i ^^^ rowNat tr t r (8 + i))
  intro i hi
  rw [row_eq_natRow]
  simp only [Byte.inters, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · refine ⟨0, _, _, by decide, hx, hy, ?_⟩
    simp only [List.map_cons, List.map_nil, eX, eY, Expr.eval_ofNat', byteF]; rfl
  · refine ⟨1, _, _, by decide, hx, hy, ?_⟩
    simp only [List.map_cons, List.map_nil, eX, eY, eAnd, Expr.eval_ofNat', byteF]; rfl
  · refine ⟨2, _, _, by decide, hx, hy, ?_⟩
    simp only [List.map_cons, List.map_nil, eX, eY, eOr, Expr.eval_ofNat', byteF]; rfl
  · refine ⟨3, _, _, by decide, hx, hy, ?_⟩
    simp only [List.map_cons, List.map_nil, eX, eY, eXor, Expr.eval_ofNat', byteF]; rfl

/-! ## The lookup facts from `Holds` -/

def instrTables : List Table :=
  [Add.table, Bit.table, Mul.table, Shift.table, Cmp.table, Const.table, Stack.table, Ctrl.table, Local.table,
    Div.table, Load.table, Store.table, Call.table, Ret.table]

theorem table_class (nloc ncode t : Nat) (ht : t < 22) :
    (t = 0 ∧ (wasmBaseAir nloc ncode).tables[t]'(by simp [air_len]; exact ht) = Boundary.table nloc ncode) ∨
    (t = 17 ∧ (wasmBaseAir nloc ncode).tables[t]'(by simp [air_len]; exact ht) = Code.table) ∨
    (t = 18 ∧ (wasmBaseAir nloc ncode).tables[t]'(by simp [air_len]; exact ht) = Drain.table) ∨
    (t = 15 ∧ (wasmBaseAir nloc ncode).tables[t]'(by simp [air_len]; exact ht) = Range16.table) ∨
    (t = 16 ∧ (wasmBaseAir nloc ncode).tables[t]'(by simp [air_len]; exact ht) = Byte.table) ∨
    (t = 19 ∧ (wasmBaseAir nloc ncode).tables[t]'(by simp [air_len]; exact ht) = MemInit.table) ∨
    (t = 20 ∧ (wasmBaseAir nloc ncode).tables[t]'(by simp [air_len]; exact ht) = Data.table) ∨
    (t = 21 ∧ (wasmBaseAir nloc ncode).tables[t]'(by simp [air_len]; exact ht) = Func.table) ∨
    (1 ≤ t ∧ t ≤ 14 ∧ (wasmBaseAir nloc ncode).tables[t]'(by simp [air_len]; exact ht) ∈ instrTables) := by
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11
    ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 ∨ t = 20 ∨ t = 21 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
  simp [wasmBaseAir, instrTables]

theorem instr_fetch {T : Table} (h : T ∈ instrTables) :
    T ∈ [Add.table, Bit.table, Mul.table, Shift.table, Cmp.table, Const.table, Stack.table, Ctrl.table,
      Local.table, Div.table, Load.table, Store.table, Call.table, Ret.table, Range16.table, Byte.table,
      Drain.table, MemInit.table, Data.table, Func.table] := by
  simp only [instrTables, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]

theorem instr_r16 {T : Table} (h : T ∈ instrTables) :
    T ∈ [Add.table, Bit.table, Mul.table, Shift.table, Cmp.table, Const.table, Stack.table, Ctrl.table,
      Local.table, Div.table, Load.table, Store.table, Call.table, Ret.table, Byte.table, Code.table, Drain.table,
      MemInit.table, Data.table, Func.table] := by
  simp only [instrTables, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]

theorem instr_byte {T : Table} (h : T ∈ instrTables) :
    T ∈ [Add.table, Bit.table, Mul.table, Shift.table, Cmp.table, Const.table, Stack.table, Ctrl.table,
      Local.table, Div.table, Load.table, Store.table, Call.table, Ret.table, Range16.table, Code.table,
      Drain.table, MemInit.table, Data.table, Func.table] := by
  simp only [instrTables, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]

theorem instr_data {T : Table} (h : T ∈ instrTables) :
    T ∈ [Add.table, Bit.table, Mul.table, Shift.table, Cmp.table, Const.table, Stack.table, Ctrl.table,
      Local.table, Div.table, Load.table, Store.table, Call.table, Ret.table, Range16.table, Byte.table,
      Code.table, Drain.table, MemInit.table, Func.table] := by
  simp only [instrTables, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]

theorem instr_func {T : Table} (h : T ∈ instrTables) :
    T ∈ [Add.table, Bit.table, Mul.table, Shift.table, Cmp.table, Const.table, Stack.table, Ctrl.table,
      Local.table, Div.table, Load.table, Store.table, Call.table, Ret.table, Range16.table, Byte.table,
      Code.table, Drain.table, MemInit.table, Data.table] := by
  simp only [instrTables, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]


theorem looks_of {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace} (H : Holds (wasmBaseAir nloc ncode) pub tr)
    (hcode : CodeOK X tr) (hfunc : FuncOK X tr)
    (hsend : ∀ o ∈ occs (wasmBaseAir nloc ncode) tr pub, o.2.1 = true → o.2.2.2 ≤ 1) :
    Looks X nloc ncode pub tr := by
  have hP' := P_val
  refine ⟨fun o ho hb hs hc => ?_, fun o ho hb hs hc => ?_, fun o ho hb hs hc => ?_, fun o ho hb hs hc => ?_⟩
  · refine lookup_sound H busFetch (fun m => ∃ j, j < X.M.codeSize ∧ m = codeRec X j) ?_
      (fun o' ho' _ hs' => hsend o' ho' hs') ho hb hs hc
    intro o' ho' hb' hs' _
    obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := occ_table ho'
    simp only at hb' hs' ⊢
    rcases table_class nloc ncode t ht with ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ |
      ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨_, _, hT⟩
    · rw [hT] at hi; exact absurd hb' (boundary_lookups nloc ncode i hi).2.2.1
    · rw [hT] at hi
      simp only [Code.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
      subst hi
      obtain ⟨j, hj, he⟩ := hcode r hr
      refine ⟨j, hj, ?_⟩
      rw [← he]
      simp [List.map_map, Function.comp, v, Expr.eval_col, Trace.row, Boundary.recWidth]
    all_goals first
      | (rw [hT] at hi; exact absurd (recv_only_code_fetch _ (by simp) i hi hb') (by simp [hs']))
      | exact absurd (recv_only_code_fetch _ (instr_fetch hT) i hi hb') (by simp [hs'])
  · refine lookup_sound H busR16 (fun m => ∃ x : F, m = [x] ∧ x.toNat < 65536) ?_
      (fun o' ho' _ hs' => hsend o' ho' hs') ho hb hs hc
    intro o' ho' hb' hs' _
    obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := occ_table ho'
    simp only at hb' hs' ⊢
    rcases table_class nloc ncode t ht with ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ |
      ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨_, _, hT⟩
    · rw [hT] at hi; exact absurd hb' (boundary_lookups nloc ncode i hi).1
    · rw [hT] at hi; exact absurd (recv_only_range16 _ (by simp) i hi hb') (by simp [hs'])
    · rw [hT] at hi; exact absurd (recv_only_range16 _ (by simp) i hi hb') (by simp [hs'])
    · have hT' := hT
      rw [hT] at hi
      simp only [Range16.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
      subst hi
      obtain ⟨hh, hv⟩ := range16_values H (by simp [air_len]) hT'
      refine ⟨_, rfl, ?_⟩
      have := hv r hr
      simp only [rowNat, Range16.val] at this
      simp only [v, Expr.eval_col, Trace.row, Range16.val]
      omega
    all_goals first
      | (rw [hT] at hi; exact absurd (recv_only_range16 _ (by simp) i hi hb') (by simp [hs']))
      | exact absurd (recv_only_range16 _ (instr_r16 hT) i hi hb') (by simp [hs'])
  · refine lookup_sound H busByte (fun m => ∃ k x y, k < 4 ∧ x < 256 ∧ y < 256 ∧
      m = [((k : Nat) : F), ((x : Nat) : F), ((y : Nat) : F), ((byteF k x y : Nat) : F)]) ?_
      (fun o' ho' _ hs' => hsend o' ho' hs') ho hb hs hc
    intro o' ho' hb' hs' _
    obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := occ_table ho'
    simp only at hb' hs' ⊢
    rcases table_class nloc ncode t ht with ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ |
      ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨_, _, hT⟩
    · rw [hT] at hi; exact absurd hb' (boundary_lookups nloc ncode i hi).2.1
    · rw [hT] at hi; exact absurd (recv_only_byte _ (by simp) i hi hb') (by simp [hs'])
    · rw [hT] at hi; exact absurd (recv_only_byte _ (by simp) i hi hb') (by simp [hs'])
    · rw [hT] at hi; exact absurd (recv_only_byte _ (by simp) i hi hb') (by simp [hs'])
    · have hT' := hT
      rw [hT] at hi
      exact byte_row_msgs H (by simp [air_len]) hT' hr i hi
    all_goals first
      | (rw [hT] at hi; exact absurd (recv_only_byte _ (by simp) i hi hb') (by simp [hs']))
      | exact absurd (recv_only_byte _ (instr_byte hT) i hi hb') (by simp [hs'])
  · refine lookup_sound H busFunc (fun m => ∃ k, k < X.nf ∧ m = funcRec X k) ?_
      (fun o' ho' _ hs' => hsend o' ho' hs') ho hb hs hc
    intro o' ho' hb' hs' _
    obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := occ_table ho'
    simp only at hb' hs' ⊢
    rcases table_class nloc ncode t ht with ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ |
      ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨_, _, hT⟩
    · rw [hT] at hi; exact absurd hb' (boundary_lookups nloc ncode i hi).2.2.2.2
    · rw [hT] at hi; exact absurd (recv_only_func _ (by simp) i hi hb') (by simp [hs'])
    · rw [hT] at hi; exact absurd (recv_only_func _ (by simp) i hi hb') (by simp [hs'])
    · rw [hT] at hi; exact absurd (recv_only_func _ (by simp) i hi hb') (by simp [hs'])
    · rw [hT] at hi; exact absurd (recv_only_func _ (by simp) i hi hb') (by simp [hs'])
    · rw [hT] at hi; exact absurd (recv_only_func _ (by simp) i hi hb') (by simp [hs'])
    · rw [hT] at hi; exact absurd (recv_only_func _ (by simp) i hi hb') (by simp [hs'])
    · rw [hT] at hi
      simp only [Func.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
      subst hi
      obtain ⟨k, hk, he⟩ := hfunc r hr
      refine ⟨k, hk, ?_⟩
      rw [← he]
      simp [List.map_map, Function.comp, v, Expr.eval_col, Trace.row]
    · exact absurd (recv_only_func _ (instr_func hT) i hi hb') (by simp [hs'])

end WasmBase
