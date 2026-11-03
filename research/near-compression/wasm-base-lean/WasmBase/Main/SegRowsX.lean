import WasmBase.Main.SegBus

/-!
# WasmBase.Main.SegRowsX — instruction-row facts of a segment trace (E2E M4b, S4)

**`seg_rowfacts`**: every active instruction row (tables 1–14, IF 26, CONV 28, UNREACH 29) of a
`HoldsX (wasmBaseSegAir …)` trace has `RowFacts2` for the M2 context — the segment analogue of
`m2_rowfacts`, from `HoldsX` and the CODE/FUNC commitment bindings (`CodeOK`, `FuncOK`) only.

* **Tables 1–14** (`seg_base_rowfacts`): the base per-chip lemmas (`chipFactsC … |>.rows`) applied to
  the base view `segBase tr` (`Main/SegBus.lean`) under a public-value list `pubOf X` that satisfies
  `PubOK` (`pubOK_of`).  This is sound because the base row lemmas never read `PubOK` (it is passed as
  `_hpub`) and the kept base tables mention no public value (`Table.noPub`, `base_noPub`, by
  `decide`), so rows, messages, counts and constraints are the same under `pub` and `pubOf X`
  (`rowIn_noPub` …).  The base `Looks` (FETCH, R16, BYTE, FUNC) on `segBase tr` come from the
  segment AIR's own lookups (`seg_looks`): every base occurrence on `segBase tr` is a segment
  occurrence on `tr` (`base_occ_seg`), and on the segment AIR only CODE/RANGE16/BYTE/FUNC receive on
  those buses (`seg_recv_fetch`, `seg_recv_func`, S2's `seg_byte_recv_tables`, `regAt_seg`) with
  every send counted by a bit (`seg_hsend_ff`, `seg_hsend_r16`, `SegSha.seg_hsend_byte`).
* **IF / CONV / UNREACH** (`if_rowfacts_seg`, `conv_rowfacts_seg`, `unreach_rowfacts_seg`): the M2
  proofs verbatim over `HoldsX (wasmBaseSegAir …)` (same tables at the same indices), with the
  segment lookups `seg_fetchM2`, `seg_r16`, `seg_time_chk`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-! ## Public-value independence -/

/-- `e` mentions no public value. -/
def Expr.noPub : Expr → Bool
  | .pub _ => false
  | .add a b => a.noPub && b.noPub
  | .sub a b => a.noPub && b.noPub
  | .mul a b => a.noPub && b.noPub
  | _ => true

theorem Expr.eval_noPub (tr : Trace) (pub pub' : List F) (t r : Nat) :
    ∀ e : Expr, e.noPub = true → e.eval (tr.row pub t r) = e.eval (tr.row pub' t r)
  | .c _, _ => rfl
  | .col _, _ => rfl
  | .nxt _, _ => rfl
  | .pub _, h => by simp [Expr.noPub] at h
  | .first, _ => rfl
  | .last, _ => rfl
  | .trans, _ => rfl
  | .add a b, h => by
    simp only [Expr.noPub, Bool.and_eq_true] at h
    simp only [Expr.eval, Expr.eval_noPub tr pub pub' t r a h.1, Expr.eval_noPub tr pub pub' t r b h.2]
  | .sub a b, h => by
    simp only [Expr.noPub, Bool.and_eq_true] at h
    simp only [Expr.eval, Expr.eval_noPub tr pub pub' t r a h.1, Expr.eval_noPub tr pub pub' t r b h.2]
  | .mul a b, h => by
    simp only [Expr.noPub, Bool.and_eq_true] at h
    simp only [Expr.eval, Expr.eval_noPub tr pub pub' t r a h.1, Expr.eval_noPub tr pub pub' t r b h.2]

def Inter.noPub (i : Inter) : Bool := i.count.noPub && i.msg.all Expr.noPub

/-- The table's constraints and interactions mention no public value (nor does the default
interaction, which `rowIn`/`rowOut` fall back to). -/
def Table.noPub (T : Table) : Bool :=
  T.constraints.all Expr.noPub && T.inters.all Inter.noPub && Inter.noPub default

theorem filterMap_congrNP {α β : Type} {f g : α → Option β} :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.filterMap_cons, h x List.mem_cons_self,
      filterMap_congrNP l (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem Inter.msg_noPub (tr : Trace) (pub pub' : List F) (t r : Nat) {i : Inter} (h : i.noPub = true) :
    i.msg.map (·.eval (tr.row pub t r)) = i.msg.map (·.eval (tr.row pub' t r)) := by
  simp only [Inter.noPub, Bool.and_eq_true, List.all_eq_true] at h
  exact List.map_congr_left fun e he => Expr.eval_noPub tr pub pub' t r e (h.2 e he)

section
variable {T : Table} (hT : T.noPub = true) (tr : Trace) (pub pub' : List F) (t r : Nat)
include hT

theorem noPub_inters : ∀ i ∈ T.inters, i.noPub = true := by
  simp only [Table.noPub, Bool.and_eq_true, List.all_eq_true] at hT; exact hT.1.2

theorem noPub_cons : ∀ e ∈ T.constraints, e.noPub = true := by
  simp only [Table.noPub, Bool.and_eq_true, List.all_eq_true] at hT; exact hT.1.1

omit hT in
theorem Inter.count_noPub {i : Inter} (h : i.noPub = true) :
    i.count.eval (tr.row pub t r) = i.count.eval (tr.row pub' t r) := by
  simp only [Inter.noPub, Bool.and_eq_true] at h
  exact Expr.eval_noPub tr pub pub' t r _ h.1

theorem noPub_getD (k : Nat) : (T.inters.getD k default).noPub = true := by
  rw [List.getD_eq_getElem?_getD]
  cases h : T.inters[k]? with
  | none => simp only [Table.noPub, Bool.and_eq_true] at hT; exact hT.2
  | some i => exact noPub_inters hT i (List.mem_of_getElem? h)

theorem rowIn_noPub : rowIn T tr pub t r = rowIn T tr pub' t r := by
  have := noPub_getD hT 0
  unfold rowIn; simp only [Inter.noPub, Bool.and_eq_true, List.all_eq_true] at this
  exact List.map_congr_left fun e he => Expr.eval_noPub tr pub pub' t r e (this.2 e he)

theorem rowOut_noPub : rowOut T tr pub t r = rowOut T tr pub' t r := by
  have := noPub_getD hT 1
  unfold rowOut; simp only [Inter.noPub, Bool.and_eq_true, List.all_eq_true] at this
  exact List.map_congr_left fun e he => Expr.eval_noPub tr pub pub' t r e (this.2 e he)

theorem rowAct_noPub : rowAct T tr pub t r ↔ rowAct T tr pub' t r := by
  unfold rowAct; rw [Inter.count_noPub tr pub pub' t r (noPub_getD hT 0)]

theorem rowMsgs_noPub (b : Nat) (s : Bool) : rowMsgs T tr pub t r b s = rowMsgs T tr pub' t r b s := by
  rw [rowMsgs_eq, rowMsgs_eq]
  refine filterMap_congrNP _ fun i hi => ?_
  have h := noPub_inters hT i (List.mem_filter.mp hi).1
  rw [Inter.count_noPub tr pub pub' t r h, Inter.msg_noPub tr pub pub' t r h]

theorem rowCons_noPub : rowCons T tr pub t r = rowCons T tr pub' t r := by
  unfold rowCons; rw [rowMsgs_noPub hT]
theorem rowProd_noPub : rowProd T tr pub t r = rowProd T tr pub' t r := by
  unfold rowProd; rw [rowMsgs_noPub hT]

end

/-- The base tables 1–21 do not depend on `nloc`/`ngl`. -/
theorem base_table_indep (a b c d t : Nat) (ht : t < 22) (h0 : t ≠ 0) :
    (wasmBaseAir a b).tables[t]'(by rw [air_len]; exact ht) =
      (wasmBaseAir c d).tables[t]'(by rw [air_len]; exact ht) := by
  rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨
    t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 ∨ t = 20 ∨ t = 21 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> rfl

/-- The base tables kept by `segBase` (1–17, 21) mention no public value. -/
theorem base_noPub (nloc ngl t : Nat) (ht : t < 22) (hg : ¬ baseGone t) :
    ((wasmBaseAir nloc ngl).tables[t]'(by rw [air_len]; exact ht)).noPub = true := by
  have h0 : ∀ t (ht : t < (wasmBaseAir 0 0).tables.length), ¬ baseGone t →
      ((wasmBaseAir 0 0).tables[t]'ht).noPub = true := by decide +kernel
  rw [base_table_indep nloc ngl 0 0 t ht (by unfold baseGone at hg; omega)]
  exact h0 t _ hg

/-- A kept base table's interactions are interactions of the segment table at the same index. -/
theorem base_inters_sub (a b nloc ngl t : Nat) (ht : t < 22) (hg : ¬ baseGone t) :
    ∀ i ∈ ((wasmBaseAir a b).tables[t]'(by rw [air_len]; exact ht)).inters,
      i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'(by simp [seg_air_len]; omega)).inters := by
  unfold baseGone at hg
  rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨
    t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 21 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | (intro i hi; exact hi) | (intro i hi; exact List.mem_append_left _ hi)

/-! ## The base view of a segment trace, under other publics -/

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- A segment trace satisfies the base AIR's constraints on `segBase tr`, for any `nloc'`, `ngl'`
and any public values (the kept tables mention none). -/
theorem seg_base_holdsC' (nloc' ngl' : Nat) (pub' : List F) :
    HoldsC (wasmBaseAir nloc' ngl') pub' (segBase tr) := by
  refine ⟨fun t ht r hr e he => ?_⟩
  have h22 : t < 22 := by rwa [air_len] at ht
  by_cases hg : baseGone t
  · simp [segBase, hg] at hr
  · have h0 : t ≠ 0 := by unfold baseGone at hg; omega
    rw [segBase_height hg] at hr
    rw [segBase_row hg]
    have hnp := base_noPub nloc' ngl' t h22 hg
    rw [← Expr.eval_noPub tr pub pub' t r e (noPub_cons hnp e he)]
    rw [base_table_indep nloc' ngl' nloc ngl t h22 h0, seg_base_constraints nloc ngl t h22 hg] at he
    exact H.constr t _ r hr e he

omit H in
/-- Every occurrence of the base AIR on `segBase tr` (any publics) is an occurrence of the segment
AIR on `tr`. -/
theorem base_occ_seg {nloc' ngl' : Nat} {pub' : List F} {o : Occ}
    (ho : o ∈ occs (wasmBaseAir nloc' ngl') (segBase tr) pub') : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub := by
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  have h22 : t < 22 := by rwa [air_len] at ht
  by_cases hg : baseGone t
  · simp [segBase, hg] at hr
  · rw [segBase_height hg] at hr
    have hnp := base_noPub nloc' ngl' t h22 hg
    have hin := noPub_inters hnp i hi
    refine mem_occs.mpr ⟨t, by simp [seg_air_len]; omega, r, hr, i, base_inters_sub nloc' ngl' nloc ngl t h22 hg i hi, ?_⟩
    rw [segBase_row hg, Inter.msg_noPub tr pub pub' t r hin, Inter.count_noPub tr pub pub' t r hin]

end

/-! ## Lookups of the segment AIR: FETCH, FUNC, BYTE, R16 -/

theorem seg_sendsOkFF (nloc ngl : Nat) :
    ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length), ¬ (1 ≤ t ∧ t ≤ 14) →
      SegSha.SendsOkB busFetch ((wasmBaseSegAir nloc ngl).tables[t]'ht) = true ∧
      SegSha.SendsOkB busFunc ((wasmBaseSegAir nloc ngl).tables[t]'ht) = true := by
  have e : (wasmBaseSegAir nloc ngl).tables = (wasmBaseSegAir 0 0).tables := rfl
  have h0 : ∀ t (ht : t < (wasmBaseSegAir 0 0).tables.length), ¬ (1 ≤ t ∧ t ≤ 14) →
      SegSha.SendsOkB busFetch ((wasmBaseSegAir 0 0).tables[t]'ht) = true ∧
      SegSha.SendsOkB busFunc ((wasmBaseSegAir 0 0).tables[t]'ht) = true := by
    decide +kernel
  simp only [e]; exact h0

/-- Only table `tb` receives on bus `b` (decidable form). -/
def RecvOnly (A : Air) (b tb : Nat) : Prop :=
  ∀ t (ht : t < A.tables.length), t ≠ tb → ∀ i ∈ (A.tables[t]'ht).inters, i.bus = b → i.send = true

theorem recvOnly_of_all {A : Air} {b tb : Nat}
    (h : ∀ t (ht : t < A.tables.length), t ≠ tb → (A.tables[t]'ht).inters.all (fun i => decide (i.bus ≠ b) || i.send) = true) :
    RecvOnly A b tb := by
  intro t ht htb i hi hb
  have := List.all_eq_true.mp (h t ht htb) i hi
  simpa [hb] using this

theorem seg_recv_fetch (nloc ngl : Nat) : RecvOnly (wasmBaseSegAir nloc ngl) busFetch 17 := by
  have e : wasmBaseSegAir nloc ngl = wasmBaseSegAir 0 0 := rfl
  rw [e]; exact recvOnly_of_all (by decide +kernel)

theorem seg_recv_func (nloc ngl : Nat) : RecvOnly (wasmBaseSegAir nloc ngl) busFunc 21 := by
  have e : wasmBaseSegAir nloc ngl = wasmBaseSegAir 0 0 := rfl
  rw [e]; exact recvOnly_of_all (by decide +kernel)

theorem seg_t17 (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[17]'(by simp [seg_air_len]) = Code.table := rfl
theorem seg_t21 (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[21]'(by simp [seg_air_len]) = Func.table := rfl

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- **The FETCH/FUNC send bounds of `wasmBaseSegAir`.** -/
theorem seg_hsend_ff {b : Nat} (hb : b = busFetch ∨ b = busFunc) :
    ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = b → o.2.1 = true → o.2.2.2 ≤ 1 := by
  intro o ho hbo hs
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hbo hs ⊢
  by_cases hc : 1 ≤ t ∧ t ≤ 13
  · have hT := seg_chipT nloc ngl t hc.1 hc.2
    have hcon := table_constr_eqX H ht (chipT t) hT hr
    rw [hT] at hi
    obtain ⟨h1, h13⟩ := hc
    rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨
      t = 11 ∨ t = 12 ∨ t = 13 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  by_cases h14 : t = 14
  · subst h14
    have hcon : ∀ e ∈ Ret.table.constraints, e.eval (Local.natRow (rowNat tr 14 r) (tr.row pub 14 r)) = 0 :=
      table_constr_eqX H ht RetT.table (seg_t14' nloc ngl) hr
    rw [seg_t14'] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ret_counts_of hcon i hi
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      subst hi; rcases hb with rfl | rfl <;> exact absurd hbo (by decide)
  · have hok := seg_sendsOkFF nloc ngl t ht (by omega)
    rcases hb with rfl | rfl
    · exact SegSha.le_of_sendsOkB H.toC ht hok.1 hr hi hbo hs
    · exact SegSha.le_of_sendsOkB H.toC ht hok.2 hr hi hbo hs

/-- **FETCH lookup soundness on the segment AIR.** -/
theorem seg_fetch (X : Ctx) (hcode : CodeOK X tr) {o : Occ} (ho : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub)
    (hb : o.1 = busFetch) (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ j, j < X.M.codeSize ∧ o.2.2.1 = codeRec X j := by
  refine lookup_soundX H busFetch (by decide) (fun m => ∃ j, j < X.M.codeSize ∧ m = codeRec X j) ?_
    (seg_hsend_ff H (Or.inl rfl)) ho hb hs hc
  intro o' ho' hb' hs' _
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho'
  simp only at hb' hs' ⊢
  by_cases h17 : t = 17
  · subst h17
    rw [seg_t17] at hi
    simp only [Code.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst hi
    obtain ⟨j, hj, he⟩ := hcode r hr
    refine ⟨j, hj, ?_⟩
    rw [← he]
    simp [List.map_map, Function.comp, v, Expr.eval_col, Trace.row, Boundary.recWidth]
  · exact absurd (seg_recv_fetch nloc ngl t ht h17 i hi hb') (by simp [hs'])

/-- **FUNC lookup soundness on the segment AIR.** -/
theorem seg_func (X : Ctx) (hfunc : FuncOK X tr) {o : Occ} (ho : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub)
    (hb : o.1 = busFunc) (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ k, k < X.nf ∧ o.2.2.1 = funcRec X k := by
  refine lookup_soundX H busFunc (by decide) (fun m => ∃ k, k < X.nf ∧ m = funcRec X k) ?_
    (seg_hsend_ff H (Or.inr rfl)) ho hb hs hc
  intro o' ho' hb' hs' _
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho'
  simp only at hb' hs' ⊢
  by_cases h21 : t = 21
  · subst h21
    rw [seg_t21] at hi
    simp only [Func.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
    subst hi
    obtain ⟨k, hk, he⟩ := hfunc r hr
    refine ⟨k, hk, ?_⟩
    rw [← he]
    simp [List.map_map, Function.comp, v, Expr.eval_col, Trace.row]
  · exact absurd (seg_recv_func nloc ngl t ht h21 i hi hb') (by simp [hs'])

/-- **R16 lookup soundness on the segment AIR.** -/
theorem seg_r16 {o : Occ} (ho : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub) (hb : o.1 = busR16)
    (hs : o.2.1 = true) (hc : o.2.2.2 = 1) : ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536 :=
  lookup_r16GX H (seg_hsend_r16 H) (regG_r16_recvX H (regAt_seg nloc ngl)) ho hb hs hc

/-- The BYTE table rows of a segment trace answer exactly `byteF`. -/
theorem seg_byte_row_msgs {r : Nat} (hr : r < tr.height 16) :
    ∀ i ∈ Byte.inters, ∃ k x y, k < 4 ∧ x < 256 ∧ y < 256 ∧
      i.msg.map (·.eval (tr.row pub 16 r)) =
        [((k : Nat) : F), ((x : Nat) : F), ((y : Nat) : F), ((byteF k x y : Nat) : F)] := by
  have hb := SegSha.byte_bitsX H hr
  have hx := bits8_lt (fun i => rowNat tr 16 r i) (fun i hi => hb i (by omega))
  have hy := bits8_lt (fun i => rowNat tr 16 r (8 + i)) (fun i hi => hb (8 + i) (by omega))
  have eX : Byte.X.eval (natRow (rowNat tr 16 r) (tr.row pub 16 r)) = ((bits8 fun i => rowNat tr 16 r i : Nat) : F) := by
    simp only [Byte.X, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add', Expr.eval_mul',
      Expr.eval_c, Expr.eval_col, natRow, v, Byte.xb, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat']
    exact cast_bits8 _
  have eY : Byte.Y.eval (natRow (rowNat tr 16 r) (tr.row pub 16 r)) = ((bits8 fun i => rowNat tr 16 r (8 + i) : Nat) : F) := by
    simp only [Byte.Y, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add', Expr.eval_mul',
      Expr.eval_c, Expr.eval_col, natRow, v, Byte.yb, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat']
    exact cast_bits8 (fun i => rowNat tr 16 r (8 + i))
  have hop : ∀ (op : Nat → Nat → Nat) (fb : Bool → Bool → Bool),
      (∀ x y i, (op x y).testBit i = fb (x.testBit i) (y.testBit i)) → (∀ a b, a ≤ 1 → b ≤ 1 → op a b ≤ 1) →
      bits8 (fun i => op (rowNat tr 16 r i) (rowNat tr 16 r (8 + i))) =
        op (bits8 fun i => rowNat tr 16 r i) (bits8 fun i => rowNat tr 16 r (8 + i)) := fun op fb h1 h2 =>
    (bits8_op fb op h1 h2 _ _ (fun i hi => hb i (by omega)) (fun i hi => hb (8 + i) (by omega))).symm
  have eAnd : Byte.andE.eval (natRow (rowNat tr 16 r) (tr.row pub 16 r)) =
      (((bits8 fun i => rowNat tr 16 r i) &&& (bits8 fun i => rowNat tr 16 r (8 + i)) : Nat) : F) := by
    rw [← hop (· &&& ·) (· && ·) (fun x y i => Nat.testBit_and x y i)
      (fun a b ha hb => by rw [and_bit ha hb]; rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> simp <;> omega)]
    simp only [Byte.andE, Byte.bitsum, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add',
      Expr.eval_mul', Expr.eval_c, Expr.eval_col, natRow, v, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat']
    simp only [Nat.reduceAdd, cast_and_bit (hb 0 (by decide)) (hb 8 (by decide)), cast_and_bit (hb 1 (by decide)) (hb 9 (by decide)), cast_and_bit (hb 2 (by decide)) (hb 10 (by decide)), cast_and_bit (hb 3 (by decide)) (hb 11 (by decide)), cast_and_bit (hb 4 (by decide)) (hb 12 (by decide)), cast_and_bit (hb 5 (by decide)) (hb 13 (by decide)), cast_and_bit (hb 6 (by decide)) (hb 14 (by decide)), cast_and_bit (hb 7 (by decide)) (hb 15 (by decide))]
    exact cast_bits8 (fun i => rowNat tr 16 r i &&& rowNat tr 16 r (8 + i))
  have eOr : Byte.orE.eval (natRow (rowNat tr 16 r) (tr.row pub 16 r)) =
      (((bits8 fun i => rowNat tr 16 r i) ||| (bits8 fun i => rowNat tr 16 r (8 + i)) : Nat) : F) := by
    rw [← hop (· ||| ·) (· || ·) (fun x y i => Nat.testBit_or x y i)
      (fun a b ha hb => by rw [or_bit ha hb]; rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> simp <;> omega)]
    simp only [Byte.orE, Byte.bitsum, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add',
      Expr.eval_mul', Expr.eval_sub', Expr.eval_c, Expr.eval_col, natRow, v, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat']
    simp only [Nat.reduceAdd, cast_or_bit (hb 0 (by decide)) (hb 8 (by decide)), cast_or_bit (hb 1 (by decide)) (hb 9 (by decide)), cast_or_bit (hb 2 (by decide)) (hb 10 (by decide)), cast_or_bit (hb 3 (by decide)) (hb 11 (by decide)), cast_or_bit (hb 4 (by decide)) (hb 12 (by decide)), cast_or_bit (hb 5 (by decide)) (hb 13 (by decide)), cast_or_bit (hb 6 (by decide)) (hb 14 (by decide)), cast_or_bit (hb 7 (by decide)) (hb 15 (by decide))]
    exact cast_bits8 (fun i => rowNat tr 16 r i ||| rowNat tr 16 r (8 + i))
  have eXor : Byte.xorE.eval (natRow (rowNat tr 16 r) (tr.row pub 16 r)) =
      (((bits8 fun i => rowNat tr 16 r i) ^^^ (bits8 fun i => rowNat tr 16 r (8 + i)) : Nat) : F) := by
    rw [← hop (· ^^^ ·) (fun a b => a ^^ b) (fun x y i => Nat.testBit_xor x y i)
      (fun a b ha hb => by rw [xor_bit ha hb]; rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> simp <;> omega)]
    simp only [Byte.xorE, Byte.bitsum, List.range, List.range.loop, List.map, List.foldl, Expr.eval_add',
      Expr.eval_mul', Expr.eval_sub', Expr.eval_c, Expr.eval_col, natRow, v, Nat.reducePow, Nat.reduceAdd, Expr.eval_ofNat']
    simp only [Nat.reduceAdd, cast_xor_bit (hb 0 (by decide)) (hb 8 (by decide)), cast_xor_bit (hb 1 (by decide)) (hb 9 (by decide)), cast_xor_bit (hb 2 (by decide)) (hb 10 (by decide)), cast_xor_bit (hb 3 (by decide)) (hb 11 (by decide)), cast_xor_bit (hb 4 (by decide)) (hb 12 (by decide)), cast_xor_bit (hb 5 (by decide)) (hb 13 (by decide)), cast_xor_bit (hb 6 (by decide)) (hb 14 (by decide)), cast_xor_bit (hb 7 (by decide)) (hb 15 (by decide))]
    exact cast_bits8 (fun i => rowNat tr 16 r i ^^^ rowNat tr 16 r (8 + i))
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

/-- **BYTE lookup soundness on the segment AIR** (the full answer `byteF`). -/
theorem seg_byte {o : Occ} (ho : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub) (hb : o.1 = busByte)
    (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ k x y, k < 4 ∧ x < 256 ∧ y < 256 ∧
      o.2.2.1 = [((k : Nat) : F), ((x : Nat) : F), ((y : Nat) : F), ((byteF k x y : Nat) : F)] := by
  refine lookup_soundX H busByte (by decide) (fun m => ∃ k x y, k < 4 ∧ x < 256 ∧ y < 256 ∧
      m = [((k : Nat) : F), ((x : Nat) : F), ((y : Nat) : F), ((byteF k x y : Nat) : F)]) ?_
    (SegSha.seg_hsend_byte H) ho hb hs hc
  intro o' ho' hb' hs' _
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho'
  simp only at hb' hs' ⊢
  by_cases h16 : t = 16
  · subst h16
    rw [SegSha.seg_t16] at hi
    exact seg_byte_row_msgs H hr i hi
  · exact absurd (SegSha.seg_byte_recv_tables nloc ngl t ht h16 i hi hb') (by simp [hs'])

/-- **The base `Looks` facts on the base view of a segment trace**, for any `nloc'`, `ngl'`, publics. -/
theorem seg_looks (X : Ctx) (hcode : CodeOK X tr) (hfunc : FuncOK X tr) (nloc' ngl' : Nat) (pub' : List F) :
    Looks X nloc' ngl' pub' (segBase tr) :=
  ⟨fun _o ho hb hs hc => seg_fetch H X hcode (base_occ_seg ho) hb hs hc,
   fun _o ho hb hs hc => seg_r16 H (base_occ_seg ho) hb hs hc,
   fun _o ho hb hs hc => seg_byte H (base_occ_seg ho) hb hs hc,
   fun _o ho hb hs hc => seg_func H X hfunc (base_occ_seg ho) hb hs hc⟩

end

/-! ## A public-value list satisfying `PubOK`

The base row lemmas take `PubOK` but never read it (it is passed as `_hpub` to `fetch_pc`/`fetch_rec`);
the instruction chips mention no public value.  So the base row facts can be taken under any `pub'`
satisfying `PubOK` and transported back (`rowIn_noPub` …).  `pubOK_of` builds one. -/

def pubVal (X : Ctx) (i : Nat) : F :=
  if i = Boundary.pubNres then ((X.ck.arity : Nat) : F)
  else if i = Boundary.pubTag then ((X.ck.resTag : Nat) : F)
  else if i = Boundary.pubStatus then ((1 : Nat) : F)
  else if Boundary.pubLoc ≤ i then ((X.ck.localTags.getD (i - Boundary.pubLoc) 0 : Nat) : F)
  else 0

def pubOf (X : Ctx) : List F :=
  List.ofFn (n := Boundary.pubLoc + X.pf.locals.size + 5 * 0 + 2) fun i => pubVal X i.val

theorem pubOf_getD (X : Ctx) {i : Nat} (hi : i < Boundary.pubLoc + X.pf.locals.size + 5 * 0 + 2) :
    (pubOf X).getD i 0 = pubVal X i := by
  unfold pubOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi]; rfl

theorem pubOK_of (X : Ctx) : PubOK X X.pf.locals.size 0 (pubOf X) where
  hnloc := rfl
  len := by simp [pubOf]
  locTags := by
    intro j hj
    rw [pubOf_getD X (by omega)]
    unfold pubVal
    have a : ¬ (Boundary.pubLoc + j = Boundary.pubNres) := by simp only [Boundary.pubLoc, Boundary.pubNres]; omega
    have b : ¬ (Boundary.pubLoc + j = Boundary.pubTag) := by simp only [Boundary.pubLoc, Boundary.pubTag]; omega
    have c : ¬ (Boundary.pubLoc + j = Boundary.pubStatus) := by
      simp only [Boundary.pubLoc, Boundary.pubStatus]; omega
    rw [if_neg a, if_neg b, if_neg c, if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  nres := by
    rw [pubOf_getD X (by simp only [Boundary.pubNres, Boundary.pubLoc]; omega)]
    simp [pubVal]
  status := by
    left
    rw [pubOf_getD X (by simp only [Boundary.pubStatus, Boundary.pubLoc]; omega)]
    simp [pubVal, Boundary.pubNres, Boundary.pubTag, Boundary.pubStatus]
  rtag := by
    rw [pubOf_getD X (by simp only [Boundary.pubTag, Boundary.pubLoc]; omega)]
    simp [pubVal, Boundary.pubNres, Boundary.pubTag]

/-! ## The base instruction rows (tables 1–14) of a segment trace -/

theorem chipT_noPub (t : Nat) (h1 : 1 ≤ t) (h14 : t ≤ 14) : (chipT t).noPub = true := by
  have := base_noPub 0 0 t (by omega) (by unfold baseGone; omega)
  rwa [chipT_eq 0 0 t h1 h14] at this

/-- **`RowFacts2` of an active base instruction row (tables 1–14) of a segment trace.** -/
theorem seg_base_rowfacts (X : Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hcode : CodeOK X tr) (hfunc : FuncOK X tr)
    {t r : Nat} (h1 : 1 ≤ t) (h14 : t ≤ 14) (hr : r < tr.height t) (ha : rowAct (chipT t) tr pub t r) :
    RowFacts2 X (rowIn (chipT t) tr pub t r) (rowOut (chipT t) tr pub t r)
      (rowCons (chipT t) tr pub t r) (rowProd (chipT t) tr pub t r) := by
  have hg : ¬ baseGone t := by unfold baseGone; omega
  have hnp := chipT_noPub t h1 h14
  have HC := seg_base_holdsC' H X.pf.locals.size 0 (pubOf X)
  have L := seg_looks H X hcode hfunc X.pf.locals.size 0 (pubOf X)
  have h := (chipFactsC X HC).rows L (pubOK_of X) t h1 h14 r (by rw [segBase_height hg]; exact hr)
    (by rw [segBase_rowAct hg, rowAct_noPub hnp tr (pubOf X) pub]; exact ha)
  have eI : rowIn (chipT t) (segBase tr) (pubOf X) t r = rowIn (chipT t) tr pub t r := by
    unfold rowIn; rw [segBase_row hg]; exact rowIn_noPub hnp tr (pubOf X) pub t r
  have eO : rowOut (chipT t) (segBase tr) (pubOf X) t r = rowOut (chipT t) tr pub t r := by
    unfold rowOut; rw [segBase_row hg]; exact rowOut_noPub hnp tr (pubOf X) pub t r
  have eC : rowCons (chipT t) (segBase tr) (pubOf X) t r = rowCons (chipT t) tr pub t r := by
    unfold rowCons; rw [segBase_rowMsgs hg, rowMsgs_noPub hnp tr (pubOf X) pub t r]
  have eP : rowProd (chipT t) (segBase tr) (pubOf X) t r = rowProd (chipT t) tr pub t r := by
    unfold rowProd; rw [segBase_rowMsgs hg, rowMsgs_noPub hnp tr (pubOf X) pub t r]
  rwa [eI, eO, eC, eP] at h

#print axioms seg_base_rowfacts

/-! ## IF (26), CONV (28), UNREACH (29) rows of a segment trace

`if_rowfacts_m2`, `conv_rowfacts_m2`, `unreach_rowfacts_m2` (`Main/M2If.lean`, `Main/M2Rows.lean`)
use their `Holds (wasmBaseM2Air …)` only through the row constraints of their table, the FETCH and R16
lookups, and the occurrences of their own interactions.  Tables 26/28/29 of `wasmBaseSegAir` are the
same tables at the same indices, so the proofs below are those proofs, verbatim, over
`HoldsX (wasmBaseSegAir …)` with the segment lookups (`seg_fetchM2`, `seg_r16`, `seg_time_chk`). -/

theorem seg_t26 (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[26]'(by simp [seg_air_len]) = IfC.table := rfl
theorem seg_t28 (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[28]'(by simp [seg_air_len]) = Conv.table := rfl
theorem seg_t29 (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[29]'(by simp [seg_air_len]) = Unreach.table := rfl

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- FETCH lookup soundness with the M2 records. -/
theorem seg_fetchM2 (X : M2Ctx) (hcode : CodeOKM2 X tr) {o : Occ}
    (ho : o ∈ occs (wasmBaseSegAir nloc ngl) tr pub) (hb : o.1 = busFetch) (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ j, j < X.M.codeSize ∧ o.2.2.1 = codeRecM2 X j :=
  seg_fetch H X.toCtx hcode ho hb hs hc

/-- **Time check on the segment AIR.** -/
theorem seg_time_chk {ts tp hi : F}
    (h1 : (busR16, true, [ts - tp - ((1 : Nat) : F) - ((65536 : Nat) : F) * hi], 1) ∈
      occs (wasmBaseSegAir nloc ngl) tr pub)
    (h2 : (busR16, true, [((4 : Nat) : F) * hi], 1) ∈ occs (wasmBaseSegAir nloc ngl) tr pub) :
    ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((tp.toNat + 1 + n : Nat) : F) = ts := by
  obtain ⟨x, hx, hxl⟩ := seg_r16 H h1 rfl rfl rfl
  obtain ⟨y, hy, hyl⟩ := seg_r16 H h2 rfl rfl rfl
  simp only [List.cons.injEq, and_true] at hx hy
  refine ⟨x.toNat + 16384 * y.toNat, by omega, ?_⟩
  simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul, Fp.cast_toNat]
  rw [← hx, ← hy]
  have : ((65536 : Nat) : F) = ((16384 : Nat) : F) * ((4 : Nat) : F) := by
    rw [← Lean.Grind.Semiring.natCast_mul]
  rw [this]; grind

end

theorem seg_fetch_conv (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hcode : CodeOKM2 X tr)
    {pcN opN hN feeN : Nat} (hpcP : pcN < P) (hhP : hN < P) (hfP : feeN < P)
    (hop : isConvOp opN = true)
    (ho : (busFetch, true, [((pcN : Nat) : F), ((opN : Nat) : F), ((hN : Nat) : F), ((feeN : Nat) : F),
      ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F)], 1) ∈
        occs (wasmBaseSegAir nloc ngl) tr pub) :
    ∃ k pc fee, k < X.nf ∧ pc < (X.pfOf k).code.size ∧ X.offOf k + pc = pcN ∧
      (X.pfOf k).code[pc]? = some (.num opN) ∧ feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee ∧
      feeN = fee ∧ hN = (X.ckOf k).heights[pc]?.getD 0 ∧ fee ≤ X.maxFee := by
  have hP' := P_val
  obtain ⟨j, hj, hm⟩ := seg_fetchM2 H X hcode ho rfl rfl rfl
  simp only [codeRecM2] at hm
  obtain ⟨a, op, b, c, d, e, f, g, hsh⟩ := X.recShape hj
  have hopl := X.recOp_lt hj
  rw [hsh] at hm hopl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hopl
  obtain ⟨-, e1, -, -⟩ := cast8_inj hm
  have hconv := isConvOp_cases hop
  have hopEq : opN = op := natEq e1 (by omega) (by omega)
  subst hopEq
  have hop2 : isConvOp ((X.M.records[j]?.getD []).getD 1 0) = true := by rw [hsh]; exact hop
  obtain ⟨k, pc, fee, hk, hpc, hoff, hins, hfee, hrec⟩ := X.recG_conv hj hop2
  rw [hsh] at hrec hins
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hrec hins
  rw [hrec] at hm
  obtain ⟨e0, -, e2, e3⟩ := cast8_inj hm
  have hjl : j < 2 ^ 20 := Nat.lt_trans hj X.mf.total
  have hpcEq : pcN = j := natEq e0 hpcP (by omega)
  have hhb := (X.factsOf hk).hBound pc hpc
  have hfl := feeUnits_lt hfee
  refine ⟨k, pc, fee, hk, hpc, by omega, hins, hfee, natEq e3 hfP (by omega), natEq e2 hhP (by omega), ?_⟩
  have := X.recFee_le hj
  rw [hsh] at this
  simp only [List.cons.injEq] at hrec
  simp only [List.getD_cons_succ, List.getD_cons_zero] at this
  omega

/-- **The FETCH pin of an `unreachable` row.** -/
theorem seg_fetch_unreach (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hcode : CodeOKM2 X tr)
    {pcN hN feeN : Nat} (hpcP : pcN < P) (hhP : hN < P) (hfP : feeN < P)
    (ho : (busFetch, true, [((pcN : Nat) : F), ((opUnreach : Nat) : F), ((hN : Nat) : F), ((feeN : Nat) : F),
      ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F)], 1) ∈
        occs (wasmBaseSegAir nloc ngl) tr pub) :
    ∃ k pc fee, k < X.nf ∧ pc < (X.pfOf k).code.size ∧ X.offOf k + pc = pcN ∧
      (X.pfOf k).code[pc]? = some .unreachable ∧ feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee ∧
      feeN = fee ∧ hN = (X.ckOf k).heights[pc]?.getD 0 ∧ fee ≤ X.maxFee := by
  have hP' := P_val
  obtain ⟨j, hj, hm⟩ := seg_fetchM2 H X hcode ho rfl rfl rfl
  simp only [codeRecM2] at hm
  obtain ⟨a, op, b, c, d, e, f, g, hsh⟩ := X.recShape hj
  have hopl := X.recOp_lt hj
  rw [hsh] at hm hopl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hopl
  obtain ⟨-, e1, -, -⟩ := cast8_inj hm
  have hopEq : opUnreach = op := natEq e1 (by simp [opUnreach]; omega) (by omega)
  have hop2 : (X.M.records[j]?.getD []).getD 1 0 = opUnreach := by rw [hsh]; exact hopEq.symm
  obtain ⟨k, pc, fee, hk, hpc, hoff, hins, hfee, hrec⟩ := X.recG_unreach hj hop2
  rw [hsh] at hrec
  rw [hrec] at hm
  obtain ⟨e0, -, e2, e3⟩ := cast8_inj hm
  have hjl : j < 2 ^ 20 := Nat.lt_trans hj X.mf.total
  have hhb := (X.factsOf hk).hBound pc hpc
  have hfl := feeUnits_lt hfee
  refine ⟨k, pc, fee, hk, hpc, by have := natEq e0 hpcP (by omega); omega, hins, hfee,
    natEq e3 hfP (by omega), natEq e2 hhP (by omega), ?_⟩
  have := X.recFee_le hj
  rw [hsh] at this
  simp only [List.cons.injEq] at hrec
  simp only [List.getD_cons_succ, List.getD_cons_zero] at this
  omega


/-- **An active CONV row of a `HoldsX (wasmBaseSegAir …)` trace.**  Its FETCH answer pins a checked
function `k` and local pc whose instruction is the conversion `.num (convOpN tr r)`, with the row's
fee and height the pc's (all from `checkModuleM2`); its CH effect is `convVal` of the consumed value
(`conv_row_spec`, with the R16 bound of `2·rl` from the lookup); and the six non-spec `RowFacts2`
fields hold. -/
theorem conv_row_seg (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hcode : CodeOKM2 X tr)
    {r : Nat} (hr : r < tr.height 28) (hact : (Conv.act.eval (tr.row pub 28 r)).toNat = 1) :
    (∃ k pc fee, k < X.nf ∧ pc < (X.pfOf k).code.size ∧ X.offOf k + pc = cn tr 28 r cPc ∧
      (X.pfOf k).code[pc]? = some (.num (convOpN tr r)) ∧ isConvOp (convOpN tr r) = true ∧
      feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee ∧ fee ≤ X.maxFee ∧ cn tr 28 r cFee = fee ∧
      cn tr 28 r cH = (X.ckOf k).heights[pc]?.getD 0) ∧
    (∀ {i tp : Nat} {x : Val}, isNum x →
      decMsg [((0 : Nat) : F), (v Conv.kSb + v cH - 1).eval (tr.row pub 28 r),
        ((cn tr 28 r Conv.fWrap : Nat) : F), ((cn tr 28 r Conv.a : Nat) : F),
        ((cn tr 28 r (Conv.a + 1) : Nat) : F), ((cn tr 28 r (Conv.a + 2) : Nat) : F),
        ((cn tr 28 r (Conv.a + 3) : Nat) : F), ((cn tr 28 r Conv.ta : Nat) : F)] = enc 0 i x tp →
      rowCons Conv.table tr pub 28 r = [enc 0 i x tp] ∧
      rowProd Conv.table tr pub 28 r = [enc 0 i (convVal (convOpN tr r) x) (cn tr 28 r cTs)]) ∧
    (rowIn Conv.table tr pub 28 r).getD 3 0 = 0 ∧
    lvl (rowOut Conv.table tr pub 28 r) = lvl (rowIn Conv.table tr pub 28 r) + 1 ∧
    (∃ fee, fee ≤ X.maxFee ∧
      gasF (rowOut Conv.table tr pub 28 r) = gasF (rowIn Conv.table tr pub 28 r) + (fee : F)) ∧
    (∀ x ∈ rowCons Conv.table tr pub 28 r, ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧
      ((x.tp + 1 + n : Nat) : F) = lvl (rowIn Conv.table tr pub 28 r)) ∧
    (∀ x ∈ rowProd Conv.table tr pub 28 r, x.tp < P ∧
      ((x.tp : Nat) : F) = lvl (rowIn Conv.table tr pub 28 r)) ∧
    (rowProd Conv.table tr pub 28 r).Nodup := by
  have hP' := P_val
  have ht : 28 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hT := seg_t28 nloc ngl
  have hc := table_constr_eqX H ht Conv.table hT hr
  have hPr := rowNat_lt tr 28 r
  obtain ⟨hfl, -, -, -⟩ := conv_row_facts hc hact
  have hop : isConvOp (convOpN tr r) = true := by
    simp only [convOpN, isConvOp, Bool.or_eq_true, beq_iff_eq]
    rcases hfl with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> rw [a, b, c] <;> simp
  have hopP : convOpN tr r < P := by
    have := isConvOp_cases hop; omega
  -- interactions of the row, as occurrences
  have occ : ∀ i ∈ Conv.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 28 r)),
      (i.count.eval (tr.row pub 28 r)).toNat) ∈ occs (wasmBaseSegAir nloc ngl) tr pub := by
    intro i hi
    refine row_occ ht hr ?_
    rw [hT]; exact hi
  -- the FETCH pin
  have hfo := occ (fetch (v cPc) Conv.op (v cH) (v cFee) zeros4 Conv.act) (by simp [Conv.inters, stdState])
  have hopE : Conv.op.eval (tr.row pub 28 r) = ((convOpN tr r : Nat) : F) := by
    simp only [Conv.op, convOpN, Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', conv_col_eval,
      Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
  simp only [fetch, zeros4, List.cons_append, List.nil_append, List.map_cons, List.map_nil, hact, hopE,
    Expr.eval_ofNat', conv_col_eval] at hfo
  obtain ⟨k, pc, fee, hk, hpc, hoff, hins, hfee, hfeq, hheq, hfle⟩ :=
    seg_fetch_conv X H hcode (hPr _) (hPr _) (hPr _) hop hfo
  refine ⟨⟨k, pc, fee, hk, hpc, hoff, hins, hop, hfee, hfle, hfeq, hheq⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the CH effect
    intro i tp x hx hin
    refine conv_row_spec hc hact (fun h1 => ?_) hx hin
    have hro := occ (r16 (2 * v Conv.rl) (v Conv.fExtS)) (by simp [Conv.inters])
    simp only [r16, List.map_cons, List.map_nil, Expr.eval_mul', Expr.eval_ofNat', conv_col_eval] at hro
    have hcnt : (((cn tr 28 r Conv.fExtS : Nat) : F)).toNat = 1 := by
      rw [Fp.toNat_cast_of_lt (hPr _)]; exact h1
    rw [hcnt] at hro
    obtain ⟨y, hy, hyl⟩ := seg_r16 H hro rfl rfl rfl
    simp only [List.cons.injEq, and_true] at hy
    rw [← Lean.Grind.Semiring.natCast_mul] at hy
    rw [← hy, Fp.toNat_cast] at hyl
    exact hyl
  · rw [conv_rowIn]; rfl
  · rw [conv_rowIn, conv_rowOut]; simp only [lvl, List.getD_cons_succ, List.getD_cons_zero, one_cast]
  · refine ⟨fee, hfle, ?_⟩
    rw [conv_rowIn, conv_rowOut]
    simp only [gasF, List.getD_cons_succ, List.getD_cons_zero]
    rw [cell_cast tr 28 r 4]
    have : rowNat tr 28 r 4 = fee := hfeq
    rw [this]
  · -- consT from the time check
    intro x hx
    rw [conv_row_cons hact] at hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst hx
    have h1 := occ ((timeChk (v cTs) (v Conv.ta) (v Conv.ha) Conv.act)[0]'(by simp [timeChk]))
      (by simp [Conv.inters, timeChk])
    have h2 := occ ((timeChk (v cTs) (v Conv.ta) (v Conv.ha) Conv.act)[1]'(by simp [timeChk]))
      (by simp [Conv.inters, timeChk])
    simp only [timeChk, r16, B16, List.getElem_cons_zero, List.getElem_cons_succ, List.map_cons,
      List.map_nil, Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', conv_col_eval, hact] at h1 h2
    obtain ⟨n, hn, he⟩ := seg_time_chk H h1 h2
    refine ⟨n, hn, ?_⟩
    rw [conv_rowIn]
    simp only [decMsg, List.getD_cons_succ, List.getD_cons_zero, lvl]
    rw [Fp.toNat_cast_of_lt (hPr _)] at he ⊢
    rw [he, cell_cast tr 28 r 1]; rfl
  · intro x hx
    rw [conv_row_prod hact] at hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst hx
    simp only [decMsg, List.getD_cons_succ, List.getD_cons_zero]
    rw [Fp.toNat_cast_of_lt (hPr _), conv_rowIn]
    refine ⟨hPr _, ?_⟩
    simp only [lvl, List.getD_cons_succ, List.getD_cons_zero]
    rw [cell_cast tr 28 r 1]; rfl
  · rw [conv_row_prod hact]; simp


/-- **An active UNREACH row of a `HoldsX (wasmBaseSegAir …)` trace.**  Its FETCH answer pins a checked
function `k` and local pc whose instruction is `unreachable` (with the row's fee and height the pc's);
it consumes and produces nothing; its STATE output carries `halted = 2`; and the `RowFacts2` fields
`halt0`, `tsOut`, `gasOut` hold (`consT`, `prodT`, `prodNd` are trivial: no CH traffic). -/
theorem unreach_row_seg (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hcode : CodeOKM2 X tr)
    {r : Nat} (hr : r < tr.height 29) (hact : ((v Unreach.act).eval (tr.row pub 29 r)).toNat = 1) :
    (∃ k pc fee, k < X.nf ∧ pc < (X.pfOf k).code.size ∧ X.offOf k + pc = cn tr 29 r cPc ∧
      (X.pfOf k).code[pc]? = some .unreachable ∧
      feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee ∧ fee ≤ X.maxFee ∧ cn tr 29 r cFee = fee ∧
      cn tr 29 r cH = (X.ckOf k).heights[pc]?.getD 0) ∧
    rowCons Unreach.table tr pub 29 r = [] ∧ rowProd Unreach.table tr pub 29 r = [] ∧
    (rowOut Unreach.table tr pub 29 r).getD 3 0 = ((2 : Nat) : F) ∧
    (rowIn Unreach.table tr pub 29 r).getD 3 0 = 0 ∧
    lvl (rowOut Unreach.table tr pub 29 r) = lvl (rowIn Unreach.table tr pub 29 r) + 1 ∧
    (∃ fee, fee ≤ X.maxFee ∧
      gasF (rowOut Unreach.table tr pub 29 r) = gasF (rowIn Unreach.table tr pub 29 r) + (fee : F)) := by
  have ht : 29 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hT := seg_t29 nloc ngl
  have hPr := rowNat_lt tr 29 r
  have hfo := row_occ (pub := pub) ht hr
    (i := fetch (v cPc) (Expr.c opUnreach) (v cH) (v cFee) zeros4 (v Unreach.act))
    (by rw [hT]; simp [Unreach.table, Unreach.inters])
  have hact' : (((cn tr 29 r Unreach.act : Nat) : F)).toNat = 1 := by rw [← conv_col_eval]; exact hact
  simp only [fetch, zeros4, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    Expr.eval_ofNat', Expr.eval_c, conv_col_eval, hact'] at hfo
  obtain ⟨k, pc, fee, hk, hpc, hoff, hins, hfee, hfeq, hheq, hfle⟩ :=
    seg_fetch_unreach X H hcode (hPr _) (hPr _) (hPr _) hfo
  obtain ⟨hcons, hprod, hout⟩ := unreach_row hact
  refine ⟨⟨k, pc, fee, hk, hpc, hoff, hins, hfee, hfle, hfeq, hheq⟩, hcons, hprod, ?_, ?_, ?_, ?_⟩
  · rw [hout]; rfl
  · rw [unreach_rowIn]; rfl
  · rw [unreach_rowIn, hout]
    simp only [lvl, List.getD_cons_succ, List.getD_cons_zero, one_cast, cell_cast]; rfl
  · refine ⟨fee, hfle, ?_⟩
    rw [unreach_rowIn, hout]
    simp only [gasF, List.getD_cons_succ, List.getD_cons_zero, cell_cast]
    have e : cn tr 29 r cFee = fee := hfeq
    rw [e]; rfl


/-- **`RowFacts2` of an active CONV row** of a `HoldsX (wasmBaseSegAir …)` trace, for the M2
context. -/
theorem conv_rowfacts_seg (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hcode : CodeOKM2 X tr)
    {r : Nat} (hr : r < tr.height 28) (hact : (Conv.act.eval (tr.row pub 28 r)).toNat = 1) :
    RowFacts2 X.toCtx (rowIn Conv.table tr pub 28 r) (rowOut Conv.table tr pub 28 r)
      (rowCons Conv.table tr pub 28 r) (rowProd Conv.table tr pub 28 r) := by
  have hP' := P_val
  have hcP := rowNat_lt tr 28 r
  obtain ⟨⟨k0, pc0, fee, hk0, hpc0, hoff0, hins0, hop, hfee0, hfle, hfeq, hheq⟩, hspec, h0, hts, hgas, hct,
    hpt, hnd⟩ := conv_row_seg X H hcode hr hact
  refine ⟨?_, h0, hts, hgas, hct, hpt, hnd⟩
  intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
  rw [conv_rowIn] at hin
  obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
  have hpcl := R.pcLt
  have hoffb := X.toCtx.off_bound R.kLt
  have htot := X.toCtx.mf.total
  simp only [toCtx_offOf, toCtx_pfOf, toCtx_M] at hoffb hpcl
  have p0 : rowNat tr 28 r 0 = X.offOf E.k + pc := natEq (by rw [cell_cast] at i0; exact i0) (hcP _) (by
    simp only [toCtx_M] at htot; omega)
  have p1 : rowNat tr 28 r 1 = t := natEq (by rw [cell_cast] at i1; exact i1) (hcP _) (by omega)
  have psb : rowNat tr 28 r Conv.kSb = E.sb :=
    natEq (by rw [cell_cast] at i4; exact i4) (hcP _) (by have := R.sbLt; omega)
  have hsbR := R.sbLe
  obtain ⟨hk, hl⟩ := X.loc_unique hk0 hpc0 R.kLt hpcl (by rw [hoff0]; exact p0)
  subst k0
  subst pc0
  obtain ⟨ls0, hL0, hfl0⟩ := R.labels
  have hH := R.height
  simp only [toCtx_ckOf] at hL0 hH
  obtain ⟨h1, hnext, hL1, hH1⟩ := X.conv_succ R.kLt hins0 hop hL0 hH
  have p3 : rowNat tr 28 r cH = s.stack.size - E.sb := by
    show cn tr 28 r cH = _; rw [hheq, hH]; rfl
  have hHb := (X.factsOf R.kLt).hBound pc hpcl
  rw [hH] at hHb; simp only [Option.getD_some] at hHb
  have hszP : s.stack.size < P := by have := R.sbLt; omega
  -- the consumed message is the stack top
  have hcons := conv_row_cons (pub := pub) hact
  obtain ⟨mc, hmc_def⟩ : ∃ mc, mc = decMsg [((0 : Nat) : F), (v Conv.kSb + v cH - 1).eval (tr.row pub 28 r),
        ((cn tr 28 r Conv.fWrap : Nat) : F), ((cn tr 28 r Conv.a : Nat) : F),
        ((cn tr 28 r (Conv.a + 1) : Nat) : F), ((cn tr 28 r (Conv.a + 2) : Nat) : F),
        ((cn tr 28 r (Conv.a + 3) : Nat) : F), ((cn tr 28 r Conv.ta : Nat) : F)] := ⟨_, rfl⟩
  rw [← hmc_def] at hcons
  have hmc : live mc := hlive mc (by rw [hcons]; simp)
  have hsl : (v Conv.kSb + v cH - 1).eval (tr.row pub 28 r) =
      ((rowNat tr 28 r Conv.kSb : Nat) : F) + ((rowNat tr 28 r cH : Nat) : F) - ((1 : Nat) : F) := by
    simp only [v, Expr.eval_add', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', Trace.row, cell_cast]
  have ms : mc.space = 0 := by
    simp only [hmc_def, decMsg, List.getD_cons_zero]; rw [Fp.toNat_cast_of_lt (by omega)]
  have msl : mc.slot = s.stack.size - 1 := by
    simp only [hmc_def, decMsg, List.getD_cons_succ, List.getD_cons_zero]
    rw [hsl, slot_toNat psb p3 hsbR (by omega) hszP]
  obtain ⟨ea, -, -, vt⟩ := R.stack_dec hmc ms msl (by omega)
  have hnum := R.numS (s.stack.size - 1) (by omega)
  obtain ⟨-, hprod⟩ := hspec hnum (by rw [← hmc_def]; exact ea)
  have hins' : (X.toCtx.pfOf E.k).code[pc]? = some (.num (convOpN tr r)) := hins0
  have hfee' : feeUnits X.toCtx.cfg (X.toCtx.pfOf E.k).gas[pc]? = some fee := hfee0
  have hout : rowOut Conv.table tr pub 28 r =
      stMsg (X.toCtx.offOf E.k + (pc + 1)) (t + 1) (S + fee) 0 E.sb E.cid := by
    rw [conv_rowOut]
    rw [cell_cast] at i0 i1 i2 i4 i5
    rw [cell_cast tr 28 r 0, cell_cast tr 28 r 1, cell_cast tr 28 r 2, cell_cast tr 28 r 4,
      cell_cast tr 28 r Conv.kSb, cell_cast tr 28 r Conv.kCid, i0, i1, i2, i4, i5,
      show rowNat tr 28 r 4 = fee from hfeq]
    simp only [stMsg, Lean.Grind.Semiring.natCast_add, toCtx_offOf, one_cast, List.cons.injEq, and_true]
    grind
  refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfle, by omega, hout, fun hg => ⟨fun _ => ?_,
    fun h => absurd h (by decide), fun h => absurd h (by decide)⟩⟩
  obtain ⟨s', hst, hrel⟩ := step_conv X.toCtx R hins' hop hfee' hg hg64 (by omega) hnext
    ⟨ls0, hL1, hfl0⟩ hH1 mc (enc 0 (s.stack.size - 1) (convVal (convOpN tr r) mc.toVal) t) hmc
    ⟨ms, msl⟩ rfl
  refine ⟨s', hst, ?_⟩
  rw [vt] at hrel
  rw [hcons, hprod, show cn tr 28 r cTs = t from p1]
  exact hrel

/-- **`RowFacts2` of an active UNREACH row**: the spec step aborts (`halted = 2`). -/
theorem unreach_rowfacts_seg (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hcode : CodeOKM2 X tr)
    {r : Nat} (hr : r < tr.height 29) (hact : ((v Unreach.act).eval (tr.row pub 29 r)).toNat = 1) :
    RowFacts2 X.toCtx (rowIn Unreach.table tr pub 29 r) (rowOut Unreach.table tr pub 29 r)
      (rowCons Unreach.table tr pub 29 r) (rowProd Unreach.table tr pub 29 r) := by
  have hP' := P_val
  have hcP := rowNat_lt tr 29 r
  obtain ⟨⟨k0, pc0, fee, hk0, hpc0, hoff0, hins0, hfee0, hfle, hfeq, -⟩, hc, hp, hh2, h0, hts, hgas⟩ :=
    unreach_row_seg X H hcode hr hact
  refine ⟨?_, h0, hts, hgas, by rw [hc]; simp, by rw [hp]; simp, by rw [hp]; simp⟩
  intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
  rw [unreach_rowIn] at hin
  obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
  have hpcl := R.pcLt
  have hoffb := X.toCtx.off_bound R.kLt
  have htot := X.toCtx.mf.total
  simp only [toCtx_offOf, toCtx_pfOf, toCtx_M] at hoffb hpcl
  have p0 : rowNat tr 29 r 0 = X.offOf E.k + pc := natEq (by rw [cell_cast] at i0; exact i0) (hcP _) (by
    simp only [toCtx_M] at htot; omega)
  obtain ⟨hk, hl⟩ := X.loc_unique hk0 hpc0 R.kLt hpcl (by rw [hoff0]; exact p0)
  subst k0
  subst pc0
  have hins' : (X.toCtx.pfOf E.k).code[pc]? = some .unreachable := hins0
  have hfee' : feeUnits X.toCtx.cfg (X.toCtx.pfOf E.k).gas[pc]? = some fee := hfee0
  obtain ⟨-, -, hout0⟩ := unreach_row (pub := pub) (t := 29) (r := r) hact
  have hout : rowOut Unreach.table tr pub 29 r =
      stMsg (X.toCtx.offOf E.k + (pc + 1)) (t + 1) (S + fee) 2 E.sb E.cid := by
    rw [hout0]
    rw [cell_cast] at i0 i1 i2 i4 i5
    simp only [cn, cPc, cTs, cS, cFee] at hfeq ⊢
    rw [i0, i1, i2, i4, i5, hfeq]
    simp only [stMsg, Lean.Grind.Semiring.natCast_add, toCtx_offOf, one_cast, List.cons.injEq, and_true]
    grind
  refine ⟨E.k, pc + 1, fee, 2, E.sb, E.cid, hfle, by omega, hout, fun hg =>
    ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => ?_⟩⟩
  refine ⟨{ s with gas := { s.gas with g := s.gas.g - X.toCtx.R * fee } }, trapStr "Unreachable", ?_,
    R.step_gas hg rfl⟩
  rw [step_eq_exec X.toCtx R hins' hfee' hg hg64]
  simp [exec]


/-- **`RowFacts` of an active IF row** of a `HoldsX (wasmBaseSegAir …)` trace, for the M2 context. -/
theorem if_rowfacts_seg (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hcode : CodeOK X.toCtx tr)
    {r : Nat} (hr : r < tr.height 26) (hact : rowAct IfC.table tr pub 26 r) :
    RowFacts X.toCtx (rowIn IfC.table tr pub 26 r) (rowOut IfC.table tr pub 26 r)
      (rowCons IfC.table tr pub 26 r) (rowProd IfC.table tr pub 26 r) := by
  have hP' := P_val
  have hcP := rowNat_lt tr 26 r
  have ht : 26 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hT := seg_t26 nloc ngl
  have hcon : ∀ e ∈ IfC.constraints, e.eval (natRow (rowNat tr 26 r) (tr.row pub 26 r)) = 0 :=
    table_constr_eqX H ht IfC.table hT hr
  have hact' : (((rowNat tr 26 r IfC.fIf : Nat) : F)).toNat = 1 := by
    rw [Fp.toNat_cast_of_lt (hcP _)]; exact hact
  have occ : ∀ i ∈ IfC.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 26 r)),
      (i.count.eval (tr.row pub 26 r)).toNat) ∈ occs (wasmBaseSegAir nloc ngl) tr pub := by
    intro i hi
    refine row_occ ht hr ?_
    rw [hT]; exact hi
  -- the FETCH pin
  have hfo := occ (fetch (v cPc) (Expr.c IfC.opIf) (v cH) (v cFee) [v IfC.tgt, 0, 0, 0] IfC.act)
    (by simp [IfC.inters])
  simp only [fetch, List.cons_append, List.nil_append, List.map_cons, List.map_nil, IfC.act,
    Expr.eval_ofNat', Expr.eval_c, conv_col_eval, hact'] at hfo
  obtain ⟨j, hj, hm⟩ := seg_fetchM2 H X hcode hfo rfl rfl rfl
  simp only [codeRecM2] at hm
  obtain ⟨k, l, hk, hl, hoff, hrj⟩ := X.recG hj
  have hrec := X.rec_at hk hl
  have hsz : l < (X.ckOf k).records.size := by rw [(X.factsOf hk).records]; exact hl
  rw [Array.getElem?_eq_getElem hsz] at hrec
  have hopl := X.recOp_lt hj
  rw [hrj, Option.getD_some, Array.getElem?_eq_getElem hsz, Option.getD_some] at hm hopl
  obtain ⟨a, op, b, c, d, e5, f, g, hsh⟩ := recordAtM2_shape hrec
  rw [hsh] at hm hopl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hopl
  have hm2 := hm
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm2
  obtain ⟨-, e1, -, -, -, -, -, -⟩ := hm2
  have hopEq : op = IfC.opIf := (natEq e1 (by simp [IfC.opIf]; omega) (by omega)).symm
  obtain ⟨bt, e, el, fee, hins, hend, hels, hfee, hrr⟩ :=
    recordAtM2_if_op (hrec.trans (congrArg some hsh)) (by rw [hopEq]; rfl)
  rw [hrr] at hm
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm
  obtain ⟨m0, -, m3, m4, m6⟩ := hm
  have hjl : j < 2 ^ 20 := Nat.lt_trans hj X.mf.total
  have hhb := (X.factsOf hk).hBound l hl
  have hfl := feeUnits_lt hfee
  have hoffb := X.off_bound hk
  have htot : X.M.codeSize < 2 ^ 20 := X.mf.total
  have p0 : rowNat tr 26 r cPc = X.offOf k + l := natEq m0 (hcP _) (by omega)
  have p3 : rowNat tr 26 r cH = (X.ckOf k).heights[l]?.getD 0 := natEq m3 (hcP _) (by omega)
  have p4 : rowNat tr 26 r cFee = fee := natEq m4 (hcP _) (by omega)
  have helt : el + 1 < (X.pfOf k).code.size := by
    obtain ⟨ls, h, hls, hh⟩ := (X.factsOf hk).lh hl
    obtain ⟨lsT, hT', ftgt, lsF, hF, hs, -, -, -, h5, -, -⟩ := X.if_succ hk hins hls hh
    have := ifStepM2_spec hend hels hs
    rw [← this.2.2.2.1]; exact h5
  have p6 : rowNat tr 26 r IfC.tgt = el + 1 + X.offOf k := natEq m6 (hcP _) (by omega)
  have hfeeMax : fee ≤ X.toCtx.maxFee := by
    have := X.recFee_le hj
    rw [hrj, Option.getD_some, Array.getElem?_eq_getElem hsz, Option.getD_some, hsh, hrr] at this
    simpa using this
  -- the checker data
  have hd : IfRowData 26 X.toCtx tr r fee :=
    { k := k, pc := l, bt := bt, e := e, el := el, kLt := hk, pcLt := hl, gpc := p0.symm,
      ins := hins, endE := hend, elseE := hels, feeEq := hfee, tgt := p6, hEq := p3,
      hLt := by rw [p3]; exact hhb,
      succ := by
        intro ls h hls hh
        obtain ⟨lsT, hT', ftgt, lsF, hF, hs, h1, h2, h3, h4, h5, h6⟩ := X.if_succ hk hins hls hh
        obtain ⟨q1, q2, q3, q4, q5, q6⟩ := ifStepM2_spec hend hels hs
        subst q2 q3 q4 q5 q6
        exact ⟨h - 1, q1, rfl, h1, h2, h3, h4, h5, h6⟩ }
  -- the condition's producer time
  have hconsT : ∀ x ∈ rowCons IfC.table tr pub 26 r, ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧
      ((x.tp + 1 + n : Nat) : F) = lvl (rowIn IfC.table tr pub 26 r) := by
    intro x hx
    rw [if_rowCons hact] at hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst hx
    have h1 := occ ((timeChk (v cTs) (v IfC.tc) (v IfC.hc) IfC.act)[0]'(by simp [timeChk]))
      (by simp [IfC.inters, timeChk])
    have h2 := occ ((timeChk (v cTs) (v IfC.tc) (v IfC.hc) IfC.act)[1]'(by simp [timeChk]))
      (by simp [IfC.inters, timeChk])
    simp only [timeChk, r16, B16, IfC.act, List.getElem_cons_zero, List.getElem_cons_succ, List.map_cons,
      List.map_nil, Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', conv_col_eval, hact'] at h1 h2
    obtain ⟨n, hn, he⟩ := seg_time_chk H h1 h2
    refine ⟨n, hn, ?_⟩
    rw [if_rowIn]
    simp only [lvl, List.getD_cons_succ, List.getD_cons_zero]
    rw [Fp.toNat_cast_of_lt (hcP _)] at he
    rw [he, cell_cast tr 26 r 1]; rfl
  exact if_rowfacts hcon hact hfeeMax p4 hd hconsT


/-! ## Every instruction row of a segment trace -/

/-- **The per-row dispatch of `wasmBaseSegAir`** (the segment analogue of `m2_rowfacts`): every active
instruction row (tables 1–14, IF 26, CONV 28, UNREACH 29) of a `HoldsX (wasmBaseSegAir …)` trace has
`RowFacts2` for the M2 context.  Premises: the CODE/FUNC commitment bindings only. -/
theorem seg_rowfacts (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    {t r : Nat} (htI : IsInstrM2 t) (hr : r < tr.height t) (ha : rowAct (chipM2 t) tr pub t r) :
    RowFacts2 X.toCtx (rowIn (chipM2 t) tr pub t r) (rowOut (chipM2 t) tr pub t r)
      (rowCons (chipM2 t) tr pub t r) (rowProd (chipM2 t) tr pub t r) := by
  rcases htI with ⟨h1, h14⟩ | rfl | rfl | rfl
  · have hne : chipM2 t = chipT t := by
      simp only [chipM2]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [hne] at ha ⊢
    exact seg_base_rowfacts X.toCtx H hcode hfunc h1 h14 hr ha
  · exact (if_rowfacts_seg X H hcode hr ha).two
  · exact conv_rowfacts_seg X H hcode hr
      (by simpa [rowAct, chipM2, Conv.table, Conv.inters, stdState, stateIn] using ha)
  · exact unreach_rowfacts_seg X H hcode hr
      (by simpa [rowAct, chipM2, Unreach.table, Unreach.inters, stateIn] using ha)

#print axioms if_rowfacts_seg
#print axioms conv_rowfacts_seg
#print axioms unreach_rowfacts_seg
#print axioms seg_rowfacts

end WasmBase
