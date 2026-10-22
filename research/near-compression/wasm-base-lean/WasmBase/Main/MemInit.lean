import WasmBase.Main.Rows
import WasmBase.StepMem
/-!
# WasmBase.Main.MemInit — the MEMINIT rows (table 19)

Counts are bits; every active row's message is an initial memory byte at an address `< 2^27`
and `< mem`, with value given by the DATA lookup (`zd = 0`) or 0 beyond the data image (`zd = 1`);
the active rows are a prefix and their addresses strictly increase (so the initial memory messages
are distinct).
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-- The bus messages of table `t` (all rows). -/
def part (T : Table) (tr : Trace) (pub : List F) (t b : Nat) (s : Bool) : List (List F) :=
  (List.range (tr.height t)).flatMap fun r => rowMsgs T tr pub t r b s

/-- The initial memory messages (MEMINIT sends). -/
def memRaw (tr : Trace) (pub : List F) : List (List F) := part MemInit.table tr pub 19 busStk true

theorem meminit_bits_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ MemInit.table.constraints, e.eval (natRow (rowNat tr 19 r) (tr.row pub 19 r)) = 0) :
    (rowNat tr 19 r 0 = 0 ∨ rowNat tr 19 r 0 = 1) ∧ (rowNat tr 19 r 3 = 0 ∨ rowNat tr 19 r 3 = 1) := by
  simp only [MemInit.table, MemInit.constraints, List.forall_mem_cons, List.forall_mem_nil, and_true] at hcon
  obtain ⟨bA, bZ, -⟩ := hcon
  simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow,
    MemInit.act, MemInit.zd] at bA bZ
  exact ⟨bool_nat (rowNat_lt _ _ _ _) bA, bool_nat (rowNat_lt _ _ _ _) bZ⟩

theorem meminit_counts_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ MemInit.table.constraints, e.eval (natRow (rowNat tr 19 r) (tr.row pub 19 r)) = 0) :
    ∀ i ∈ MemInit.inters, (i.count.eval (tr.row pub 19 r)).toNat ≤ 1 := by
  obtain ⟨hA, hZ⟩ := meminit_bits_of hcon
  have hc : ∀ i ∈ MemInit.inters, i.count = v MemInit.act ∨ i.count = v MemInit.act * v MemInit.zd ∨
      i.count = v MemInit.act * (1 - v MemInit.zd) := by
    intro i hi
    have := List.all_eq_true.mp (show MemInit.inters.all (fun i => decide (i.count = v MemInit.act) ||
      decide (i.count = v MemInit.act * v MemInit.zd) || decide (i.count = v MemInit.act * (1 - v MemInit.zd))) = true
      by decide) i hi
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    rcases this with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  intro i hi
  have ea : (v MemInit.act).eval (tr.row pub 19 r) = ((rowNat tr 19 r 0 : Nat) : F) := by
    simp only [v, Expr.eval_col, Trace.row, MemInit.act, cell_cast]
  have ez : (v MemInit.zd).eval (tr.row pub 19 r) = ((rowNat tr 19 r 3 : Nat) : F) := by
    simp only [v, Expr.eval_col, Trace.row, MemInit.zd, cell_cast]
  rcases hc i hi with h | h | h <;> rw [h]
  · rw [ea, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)]; omega
  · rw [Expr.eval_mul', ea, ez]
    rcases hA with e | e <;> rcases hZ with e' | e' <;> rw [e, e'] <;> decide
  · rw [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', ea, ez]
    rcases hA with e | e <;> rcases hZ with e' | e' <;> rw [e, e'] <;> decide

theorem meminit_bits {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 19) :
    (rowNat tr 19 r 0 = 0 ∨ rowNat tr 19 r 0 = 1) ∧ (rowNat tr 19 r 3 = 0 ∨ rowNat tr 19 r 3 = 1) :=
  meminit_bits_of (table_constr H (by simp [air_len]) hr)

theorem meminit_counts {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 19) :
    ∀ i ∈ MemInit.inters, (i.count.eval (tr.row pub 19 r)).toNat ≤ 1 :=
  meminit_counts_of (table_constr H (by simp [air_len]) hr)

/-- **Statement binding of the cached DATA table.**  V_d recomputes `data_root` from the contract
code as the commitment to the canonical DATA matrix (`(a, image[a])` for `a < dataEnd`, padded by
repeating the last row) of the initial memory `s0`; under the binding, every DATA row is an address
`< 2^27` with its initial byte. -/
def DataOK (s0 : St) (tr : Trace) : Prop :=
  ∀ r, r < tr.height 20 → ∃ a, a < 2 ^ 27 ∧ tr.cell 20 r 0 = ((a : Nat) : F) ∧
    tr.cell 20 r 1 = (((readByte s0 a).toNat : Nat) : F)

/-- Every DATA query with count 1 is an initial memory byte. -/
theorem data_lookup {nloc ncode : Nat} {pub : List F} {tr : Trace} {s0 : St}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (hdata : DataOK s0 tr)
    (hsend : ∀ o ∈ occs (wasmBaseAir nloc ncode) tr pub, o.2.1 = true → o.2.2.2 ≤ 1)
    {o : Occ} (ho : o ∈ occs (wasmBaseAir nloc ncode) tr pub) (hb : o.1 = busData) (hs : o.2.1 = true)
    (hc : o.2.2.2 = 1) :
    ∃ a, a < 2 ^ 27 ∧ o.2.2.1 = [((a : Nat) : F), (((readByte s0 a).toNat : Nat) : F)] := by
  refine lookup_sound H busData (fun m => ∃ a, a < 2 ^ 27 ∧ m = [((a : Nat) : F), (((readByte s0 a).toNat : Nat) : F)])
    ?_ (fun o' ho' _ hs' => hsend o' ho' hs') ho hb hs hc
  intro o' ho' hb' hs' _
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := occ_table ho'
  simp only at hb' hs' ⊢
  rcases table_class nloc ncode t ht with ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ |
      ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨_, _, hT⟩
  · rw [hT] at hi; exact absurd hb' (boundary_lookups nloc ncode i hi).2.2.2.1
  · rw [hT] at hi; exact absurd (recv_only_data _ (by simp) i hi hb') (by simp [hs'])
  · rw [hT] at hi; exact absurd (recv_only_data _ (by simp) i hi hb') (by simp [hs'])
  · rw [hT] at hi; exact absurd (recv_only_data _ (by simp) i hi hb') (by simp [hs'])
  · rw [hT] at hi; exact absurd (recv_only_data _ (by simp) i hi hb') (by simp [hs'])
  · rw [hT] at hi; exact absurd (recv_only_data _ (by simp) i hi hb') (by simp [hs'])
  · rw [hT] at hi
    simp only [Data.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst hi
    obtain ⟨a, ha, e0, e1⟩ := hdata r hr
    exact ⟨a, ha, by simp [v, Expr.eval_col, Trace.row, e0, e1]⟩
  · rw [hT] at hi; exact absurd (recv_only_data _ (by simp) i hi hb') (by simp [hs'])
  · exact absurd (recv_only_data _ (instr_data hT) i hi hb') (by simp [hs'])

/-- An R16 lookup `[e]` of a row (count 1) bounds the field value of `e`. -/
theorem row_r16 {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace} (L : Looks X nloc ncode pub tr)
    {t : Nat} (ht : t < (wasmBaseAir nloc ncode).tables.length) {r : Nat} (hr : r < tr.height t) (e cnt : Expr)
    (hm : r16 e cnt ∈ ((wasmBaseAir nloc ncode).tables[t]'ht).inters)
    (hc : (cnt.eval (tr.row pub t r)).toNat = 1) :
    (e.eval (tr.row pub t r)).toNat < 65536 := by
  have h := row_occ ht hr hm (pub := pub)
  simp only [r16] at h
  rw [hc] at h
  obtain ⟨x, hx, hxl⟩ := L.r16 _ h rfl rfl rfl
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hx
  rw [hx]; exact hxl

/-- `lo + 2^16·hi` with `lo` and `32·hi` 16-bit is an exact natural `< 2^27 + 2^16`. -/
theorem split27 {x lo hi : F} (h : x = lo + ((65536 : Nat) : F) * hi) (hl : lo.toNat < 65536)
    (hh : (((32 : Nat) : F) * hi).toNat < 65536) :
    x.toNat = lo.toNat + 2048 * (((32 : Nat) : F) * hi).toNat := by
  have hP' := P_val
  have e : x = ((lo.toNat + 2048 * (((32 : Nat) : F) * hi).toNat : Nat) : F) := by
    rw [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul, Fp.cast_toNat, Fp.cast_toNat, h]
    rw [show ((65536 : Nat) : F) = ((2048 : Nat) : F) * ((32 : Nat) : F) by rw [← Lean.Grind.Semiring.natCast_mul]]
    grind
  rw [e, Fp.toNat_cast_of_lt (by omega)]

/-- **An active MEMINIT row** produces an initial memory byte: address `< 2^28` and `< mem`, value
the initial byte (DATA lookup, or 0 beyond the data image). -/
theorem meminit_row {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace} {s0 : St}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hdata : DataOK s0 tr)
    (hsend : ∀ o ∈ occs (wasmBaseAir nloc ncode) tr pub, o.2.1 = true → o.2.2.2 ≤ 1)
    (hM : pub.getD Boundary.pubMem 0 = ((memBytes s0 : Nat) : F)) (hMle : memBytes s0 ≤ 2 ^ 27)
    (hDE : (pub.getD Boundary.pubDataEnd 0).toNat ≤ 2 ^ 27)
    (hzero : ∀ a, (pub.getD Boundary.pubDataEnd 0).toNat ≤ a → readByte s0 a = 0)
    {r : Nat} (hr : r < tr.height 19) (hact : rowNat tr 19 r 0 = 1) :
    rowNat tr 19 r 1 < 2 ^ 28 ∧ rowNat tr 19 r 1 < memBytes s0 ∧
      rowNat tr 19 r 2 = (readByte s0 (rowNat tr 19 r 1)).toNat := by
  have hP' := P_val
  have ht : 19 < (wasmBaseAir nloc ncode).tables.length := by simp [air_len]
  have hcon : ∀ e ∈ MemInit.constraints, e.eval (tr.row pub 19 r) = 0 := by
    intro e he; exact H.constr 19 ht r hr e he
  obtain ⟨-, hZ⟩ := meminit_bits H hr
  simp only [MemInit.constraints, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hcon
  obtain ⟨-, -, hzb, -, -, hA, hMc, hDc⟩ := hcon
  simp only [v, pv, Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_col, Expr.eval_pub, Expr.eval_ofNat',
    Trace.row, MemInit.act, MemInit.ad, MemInit.bv, MemInit.zd, MemInit.alo, MemInit.ahi, MemInit.mlo, MemInit.mhi,
    MemInit.dlo, MemInit.dhi, cell_cast, hact] at hzb hA hMc hDc
  have hT : (wasmBaseAir nloc ncode).tables[19]'ht = MemInit.table := rfl
  have cA : ((v MemInit.act).eval (tr.row pub 19 r)).toNat = 1 := by
    simp only [v, Expr.eval_col, Trace.row, MemInit.act, cell_cast, hact]; rfl
  have r16of := fun (e cnt : Expr) (hm : r16 e cnt ∈ MemInit.inters) (hc : (cnt.eval (tr.row pub 19 r)).toNat = 1) =>
    row_r16 L ht hr e cnt (by rw [hT]; exact hm) hc
  have bAlo := r16of (v MemInit.alo) (v MemInit.act) (by simp [MemInit.inters]) cA
  have bAhi := r16of (32 * v MemInit.ahi) (v MemInit.act) (by simp [MemInit.inters]) cA
  have bMlo := r16of (v MemInit.mlo) (v MemInit.act) (by simp [MemInit.inters]) cA
  have bMhi := r16of (32 * v MemInit.mhi) (v MemInit.act) (by simp [MemInit.inters]) cA
  simp only [v, Expr.eval_mul', Expr.eval_col, Expr.eval_ofNat', Trace.row, MemInit.alo, MemInit.ahi, MemInit.mlo,
    MemInit.mhi, cell_cast, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)] at bAlo bAhi bMlo bMhi
  -- the address: exact, < 2^28
  have hadF : ((rowNat tr 19 r 1 : Nat) : F) =
      ((rowNat tr 19 r 6 : Nat) : F) + ((65536 : Nat) : F) * ((rowNat tr 19 r 7 : Nat) : F) := by grind
  have had := split27 hadF (by rw [Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)]; omega) bAhi
  rw [Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _), Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)] at had
  have hA28 : rowNat tr 19 r 1 < 2 ^ 28 := by omega
  refine ⟨hA28, ?_, ?_⟩
  · -- `mem − 1 − ad = mlo + 2^16 mhi`
    rw [hM] at hMc
    have e1 : ((memBytes s0 : Nat) : F) = ((rowNat tr 19 r 1 + 1 + (rowNat tr 19 r 8 +
        2048 * (((32 : Nat) : F) * ((rowNat tr 19 r 9 : Nat) : F)).toNat) : Nat) : F) := by
      rw [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_add,
        Lean.Grind.Semiring.natCast_mul, Fp.cast_toNat, cast_one]
      rw [show ((65536 : Nat) : F) = ((2048 : Nat) : F) * ((32 : Nat) : F) by rw [← Lean.Grind.Semiring.natCast_mul]] at hMc
      grind
    have := natEq e1 (by omega) (by omega)
    omega
  · rcases hZ with hz | hz
    · -- in the data image: the DATA lookup
      have cD : ((v MemInit.act * (1 - v MemInit.zd)).eval (tr.row pub 19 r)).toNat = 1 := by
        simp only [v, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval_col, Trace.row, MemInit.act,
          MemInit.zd, cell_cast, hact, hz]; rfl
      have ho := row_occ ht hr (pub := pub) (show (⟨busData, true, v MemInit.act * (1 - v MemInit.zd),
        [v MemInit.ad, v MemInit.bv]⟩ : Inter) ∈ ((wasmBaseAir nloc ncode).tables[19]'ht).inters by
          rw [hT]; simp [MemInit.table, MemInit.inters])
      rw [cD] at ho
      obtain ⟨a, ha, he⟩ := data_lookup H hdata hsend ho rfl rfl rfl
      simp only [List.map_cons, List.map_nil, v, Expr.eval_col, Trace.row, MemInit.ad, MemInit.bv, cell_cast,
        List.cons.injEq, and_true] at he
      have ea := natEq he.1 (rowNat_lt _ _ _ _) (by omega)
      subst ea
      exact natEq he.2 (rowNat_lt _ _ _ _) (by have := (readByte s0 (rowNat tr 19 r 1)).toNat_lt; omega)
    · -- beyond the data image: the byte is 0 and `ad ≥ dataEnd`
      rw [hz] at hzb hDc
      have hb0 : rowNat tr 19 r 2 = 0 := by
        have : ((1 : Nat) : F) * ((rowNat tr 19 r 2 : Nat) : F) = 0 := hzb
        have : ((rowNat tr 19 r 2 : Nat) : F) = ((0 : Nat) : F) := by grind
        exact natEq this (rowNat_lt _ _ _ _) (by omega)
      have cZ : ((v MemInit.act * v MemInit.zd).eval (tr.row pub 19 r)).toNat = 1 := by
        simp only [v, Expr.eval_mul', Expr.eval_col, Trace.row, MemInit.act, MemInit.zd, cell_cast, hact, hz]; rfl
      have bDlo := r16of (v MemInit.dlo) (v MemInit.act * v MemInit.zd) (by simp [MemInit.inters]) cZ
      have bDhi := r16of (32 * v MemInit.dhi) (v MemInit.act * v MemInit.zd) (by simp [MemInit.inters]) cZ
      simp only [v, Expr.eval_mul', Expr.eval_col, Expr.eval_ofNat', Trace.row, MemInit.dlo, MemInit.dhi, cell_cast,
        Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)] at bDlo bDhi
      have e1 : ((rowNat tr 19 r 1 : Nat) : F) = (((pub.getD Boundary.pubDataEnd 0).toNat +
          (rowNat tr 19 r 10 + 2048 * (((32 : Nat) : F) * ((rowNat tr 19 r 11 : Nat) : F)).toNat) : Nat) : F) := by
        rw [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul,
          Fp.cast_toNat, Fp.cast_toNat]
        rw [show ((65536 : Nat) : F) = ((2048 : Nat) : F) * ((32 : Nat) : F) by rw [← Lean.Grind.Semiring.natCast_mul]] at hDc
        simp only [Boundary.pubDataEnd] at hDc ⊢
        grind
      have := natEq e1 (rowNat_lt _ _ _ _) (by omega)
      rw [hb0, hzero _ (by omega)]; rfl

/-- Consecutive MEMINIT rows: activity is a prefix, and addresses strictly increase. -/
theorem meminit_succ {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace} {s0 : St}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hdata : DataOK s0 tr)
    (hsend : ∀ o ∈ occs (wasmBaseAir nloc ncode) tr pub, o.2.1 = true → o.2.2.2 ≤ 1)
    (hM : pub.getD Boundary.pubMem 0 = ((memBytes s0 : Nat) : F)) (hMle : memBytes s0 ≤ 2 ^ 27)
    (hDE : (pub.getD Boundary.pubDataEnd 0).toNat ≤ 2 ^ 27)
    (hzero : ∀ a, (pub.getD Boundary.pubDataEnd 0).toNat ≤ a → readByte s0 a = 0)
    {r : Nat} (hr : r + 1 < tr.height 19) (hact : rowNat tr 19 (r + 1) 0 = 1) :
    rowNat tr 19 r 0 = 1 ∧ rowNat tr 19 r 1 < rowNat tr 19 (r + 1) 1 := by
  have hP' := P_val
  have ht : 19 < (wasmBaseAir nloc ncode).tables.length := by simp [air_len]
  have hcon : ∀ e ∈ MemInit.constraints, e.eval (tr.row pub 19 r) = 0 := by
    intro e he; exact H.constr 19 ht r (by omega) e he
  obtain ⟨hA, -⟩ := meminit_bits H (r := r) (by omega)
  simp only [MemInit.constraints, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hcon
  obtain ⟨-, -, -, hpre, hgap, -⟩ := hcon
  have hmod : (r + 1) % tr.height 19 = r + 1 := Nat.mod_eq_of_lt hr
  have hlast : (r + 1 == tr.height 19) = false := by simp; omega
  simp only [v, nv, Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_col, Expr.eval_nxt, Expr.eval_ofNat',
    Expr.eval, Trace.row, hmod, hlast, MemInit.act, MemInit.ad, MemInit.glo, MemInit.ghi, cell_cast, hact,
    Bool.false_eq_true, ite_false] at hpre hgap
  have hA1 : rowNat tr 19 r 0 = 1 := by
    rcases hA with h | h
    · rw [h] at hpre
      exact absurd (show ((1 : Nat) : F) = 0 by grind) (by decide)
    · exact h
  refine ⟨hA1, ?_⟩
  obtain ⟨a28, -, -⟩ := meminit_row H L hdata hsend hM hMle hDE hzero (r := r) (by omega) hA1
  obtain ⟨b28, -, -⟩ := meminit_row H L hdata hsend hM hMle hDE hzero hr hact
  -- the gap lookups of row r + 1
  have hT : (wasmBaseAir nloc ncode).tables[19]'ht = MemInit.table := rfl
  have cA : ((v MemInit.act).eval (tr.row pub 19 (r + 1))).toNat = 1 := by
    simp only [v, Expr.eval_col, Trace.row, MemInit.act, cell_cast, hact]; rfl
  have bGlo := row_r16 L ht hr (v MemInit.glo) (v MemInit.act) (by rw [hT]; simp [MemInit.table, MemInit.inters]) cA
  have bGhi := row_r16 L ht hr (32 * v MemInit.ghi) (v MemInit.act) (by rw [hT]; simp [MemInit.table, MemInit.inters]) cA
  simp only [v, Expr.eval_mul', Expr.eval_col, Expr.eval_ofNat', Trace.row, MemInit.glo, MemInit.ghi, cell_cast,
    Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)] at bGlo bGhi
  have e1 : ((rowNat tr 19 (r + 1) 1 : Nat) : F) = ((rowNat tr 19 r 1 + 1 + (rowNat tr 19 (r + 1) 4 +
      2048 * (((32 : Nat) : F) * ((rowNat tr 19 (r + 1) 5 : Nat) : F)).toNat) : Nat) : F) := by
    rw [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_add,
      Lean.Grind.Semiring.natCast_mul, Fp.cast_toNat, cast_one]
    rw [show ((65536 : Nat) : F) = ((2048 : Nat) : F) * ((32 : Nat) : F) by rw [← Lean.Grind.Semiring.natCast_mul]] at hgap
    grind
  have := natEq e1 (rowNat_lt _ _ _ _) (by omega)
  omega

/-- Along the MEMINIT table, an active row has only active rows before it, with smaller addresses. -/
theorem meminit_mono {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace} {s0 : St}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hdata : DataOK s0 tr)
    (hsend : ∀ o ∈ occs (wasmBaseAir nloc ncode) tr pub, o.2.1 = true → o.2.2.2 ≤ 1)
    (hM : pub.getD Boundary.pubMem 0 = ((memBytes s0 : Nat) : F)) (hMle : memBytes s0 ≤ 2 ^ 27)
    (hDE : (pub.getD Boundary.pubDataEnd 0).toNat ≤ 2 ^ 27)
    (hzero : ∀ a, (pub.getD Boundary.pubDataEnd 0).toNat ≤ a → readByte s0 a = 0) :
    ∀ d r, r + d + 1 < tr.height 19 → rowNat tr 19 (r + d + 1) 0 = 1 →
      rowNat tr 19 r 0 = 1 ∧ rowNat tr 19 r 1 < rowNat tr 19 (r + d + 1) 1 := by
  intro d
  induction d with
  | zero => intro r hr ha; exact meminit_succ H L hdata hsend hM hMle hDE hzero hr ha
  | succ d ih =>
    intro r hr ha
    obtain ⟨h1, h2⟩ := meminit_succ H L hdata hsend hM hMle hDE hzero (r := r + d + 1) (by omega) (by simpa [Nat.add_assoc] using ha)
    obtain ⟨h3, h4⟩ := ih r (by omega) h1
    refine ⟨h3, ?_⟩
    have : r + (d + 1) + 1 = r + d + 1 + 1 := by omega
    rw [this]; omega

/-- The decoded initial memory messages. -/
theorem memRaw_eq (tr : Trace) (pub : List F) :
    (memRaw tr pub).map decMsg = ((List.range (tr.height 19)).filter fun r => rowNat tr 19 r 0 = 1).map
      fun r => encB (rowNat tr 19 r 1) (rowNat tr 19 r 2) 0 := by
  have hP' := P_val
  unfold memRaw part
  rw [List.map_flatMap]
  induction (List.range (tr.height 19)) with
  | nil => rfl
  | cons r l ih =>
    rw [List.flatMap_cons, ih, List.filter_cons]
    rw [rowMsgs_eq]
    simp only [MemInit.table, MemInit.inters, List.filter_cons, List.filter_nil, chSend, r16, busStk, busR16,
      busData, List.cons_append, List.nil_append]
    simp only [show (2 : Nat) = 2 ↔ True by decide, show (3 : Nat) = 2 ↔ False by decide,
      show (5 : Nat) = 2 ↔ False by decide, true_and, false_and, decide_true, decide_false, ite_true, ite_false,
      Bool.false_eq_true, List.filterMap_cons, List.filterMap_nil, and_self]
    have ea : ((v MemInit.act).eval (tr.row pub 19 r)).toNat = rowNat tr 19 r 0 := by
      simp only [v, Expr.eval_col, Trace.row, MemInit.act]; rfl
    rw [ea]
    by_cases h : rowNat tr 19 r 0 = 1
    · simp only [h, ite_true, decide_true, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      simp only [decMsg, encB, List.getD_cons_zero, List.getD_cons_succ, v, Expr.eval_col, Expr.eval_ofNat',
        Trace.row, MemInit.ad, MemInit.bv, cell_cast, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)]
      rfl
    · simp only [h, ite_false, decide_false, List.map_nil, List.nil_append, Bool.false_eq_true]

/-- **The initial memory messages**: distinct, at time 0, in space 3, and exactly the memory view of
the initial state over the touched addresses (the outer live set of the entry environment). -/
theorem meminit_init {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace} {s0 : St}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hdata : DataOK s0 tr)
    (hsend : ∀ o ∈ occs (wasmBaseAir nloc ncode) tr pub, o.2.1 = true → o.2.2.2 ≤ 1)
    (hM : pub.getD Boundary.pubMem 0 = ((memBytes s0 : Nat) : F)) (hMle : memBytes s0 ≤ 2 ^ 27)
    (hDE : (pub.getD Boundary.pubDataEnd 0).toNat ≤ 2 ^ 27)
    (hzero : ∀ a, (pub.getD Boundary.pubDataEnd 0).toNat ≤ a → readByte s0 a = 0) :
    ((memRaw tr pub).map decMsg).Nodup ∧ (∀ x ∈ (memRaw tr pub).map decMsg, x.tp = 0 ∧ x.space = 3) ∧
      ∃ (T : List Nat) (tpm : Nat → Nat), T.Nodup ∧ (∀ a ∈ T, a < memBytes s0) ∧ (∀ a ∈ T, tpm a < 1) ∧
        ∀ x, x.space = 3 → (x ∈ (memRaw tr pub).map decMsg ↔ x ∈ memView T s0 tpm) := by
  rw [memRaw_eq]
  let rows := (List.range (tr.height 19)).filter fun r => rowNat tr 19 r 0 = 1
  have hrow : ∀ r ∈ rows, r < tr.height 19 ∧ rowNat tr 19 r 0 = 1 := by
    intro r hr
    simp only [rows, List.mem_filter, List.mem_range, decide_eq_true_eq] at hr
    exact hr
  have hfacts := fun r (hr : r ∈ rows) => meminit_row H L hdata hsend hM hMle hDE hzero (hrow r hr).1 (hrow r hr).2
  -- the addresses strictly increase along the rows
  have hpw : rows.Pairwise (fun r r' => rowNat tr 19 r 1 < rowNat tr 19 r' 1) := by
    have h0 : rows.Pairwise (· < ·) := (List.pairwise_lt_range).filter _
    refine List.Pairwise.imp_of_mem ?_ h0
    intro r r' _ hr' hlt
    obtain ⟨h1, h2⟩ := hrow r' hr'
    have := meminit_mono H L hdata hsend hM hMle hDE hzero (r' - r - 1) r (by omega)
      (by rw [show r + (r' - r - 1) + 1 = r' by omega]; exact h2)
    rw [show r + (r' - r - 1) + 1 = r' by omega] at this
    exact this.2
  have hT : (rows.map fun r => rowNat tr 19 r 1).Nodup :=
    (List.pairwise_map.mpr hpw).imp Nat.ne_of_lt
  have heq : rows.map (fun r => encB (rowNat tr 19 r 1) (rowNat tr 19 r 2) 0) =
      memView (rows.map fun r => rowNat tr 19 r 1) s0 (fun _ => 0) := by
    simp only [memView, List.map_map]
    refine List.map_congr_left fun r hr => ?_
    simp only [Function.comp, (hfacts r hr).2.2]
  refine ⟨?_, ?_, rows.map fun r => rowNat tr 19 r 1, fun _ => 0, hT, ?_, fun _ _ => by simp, ?_⟩
  · refine List.pairwise_map.mpr (hpw.imp fun h e => ?_)
    have := congrArg Msg.slot e
    simp only [encB_slot] at this
    omega
  · intro x hx
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
    exact ⟨rfl, rfl⟩
  · intro a ha
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    exact (hfacts r hr).2.1
  · intro x _
    rw [heq]

end WasmBase
