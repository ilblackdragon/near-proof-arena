import WasmBase.Main.MemInit
import WasmBase.StepMem
import WasmBase.Local.Mem
/-!
# Row lemmas: LOAD (table 11) and STORE (table 12)

One-hot op flags (`onehot_range`): an active row selects exactly one op `k0`; every flag sum
(`act`, `is64`, `sgn`, `cnt i`, `lastE i`) then evaluates to the op's parameter (`load_sumF`).
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

theorem mem_le_sum {x : Nat} : ∀ {l : List Nat}, x ∈ l → x ≤ l.sum := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a l ih =>
    intro h
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := ih h; simp; omega

theorem sum_le_len : ∀ (l : List Nat), (∀ x ∈ l, x ≤ 1) → l.sum ≤ l.length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih => intro h; simp only [List.sum_cons, List.length_cons]; have := h a List.mem_cons_self; have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)); omega

theorem filter_true_range (n : Nat) : (List.range n).filter (fun _ => true) = List.range n :=
  List.filter_eq_self.mpr (by simp)

theorem onehot_range (f : Nat → Nat) : ∀ n, (∀ k, k < n → f k ≤ 1) → ((List.range n).map f).sum ≤ 1 →
    (∀ k, k < n → f k = 0) ∨ ∃ k0, k0 < n ∧ ∀ k, k < n → f k = if k = k0 then 1 else 0 := by
  intro n
  induction n with
  | zero => intro _ _; left; intro k hk; omega
  | succ n ih =>
    intro hb hs
    rw [List.range_succ, List.map_append, List.sum_append] at hs
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hs
    have hfn := hb n (by omega)
    rcases ih (fun k hk => hb k (by omega)) (by omega) with h | ⟨k0, hk0, h⟩
    · rcases (show f n = 0 ∨ f n = 1 by omega) with h0 | h1
      · left; intro k hk
        rcases (show k < n ∨ k = n by omega) with hl | rfl
        · exact h k hl
        · exact h0
      · right; refine ⟨n, by omega, fun k hk => ?_⟩
        rcases (show k < n ∨ k = n by omega) with hl | rfl
        · rw [h k hl, if_neg (by omega)]
        · simp [h1]
    · have hsum : ((List.range n).map f).sum ≥ 1 := by
        have : f k0 ∈ (List.range n).map f := List.mem_map.mpr ⟨k0, List.mem_range.mpr hk0, rfl⟩
        have := mem_le_sum this
        rw [h k0 hk0, if_pos rfl] at this; exact this
      have h0 : f n = 0 := by omega
      right; refine ⟨k0, by omega, fun k hk => ?_⟩
      rcases (show k < n ∨ k = n by omega) with hl | rfl
      · exact h k hl
      · rw [h0, if_neg (by omega)]

/-- A fold of flag columns is the cast of their sum. -/
theorem fold_sum (c : Nat → Nat) (rw : Row) (fl : Nat → Nat) :
    ∀ (l : List Nat) (acc : Expr), (l.foldl (fun acc k => acc + v (fl k)) acc).eval (natRow c rw) =
      acc.eval (natRow c rw) + (((l.map fun k => c (fl k)).sum : Nat) : F) := by
  intro l
  induction l with
  | nil => intro acc; simp only [List.foldl_nil, List.map_nil, List.sum_nil]; grind
  | cons k l ih =>
    intro acc
    rw [List.foldl_cons, ih]
    simp only [Expr.eval_add', v, Expr.eval_col, natRow, List.map_cons, List.sum_cons,
      Lean.Grind.Semiring.natCast_add]
    grind

theorem sum_filter_le (f : Nat → Nat) (p : Nat → Bool) :
    ∀ l : List Nat, ((l.filter p).map f).sum ≤ (l.map f).sum := by
  intro l
  induction l with
  | nil => simp
  | cons k l ih => by_cases hp : p k <;> simp [List.filter_cons, hp] <;> omega

/-- The flags of a LOAD row: bits with sum ≤ 1 (the sum is `act`). -/
theorem load_total_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Load.table.constraints, e.eval (natRow (rowNat tr 11 r) (tr.row pub 11 r)) = 0) :
    (∀ k, k < 12 → rowNat tr 11 r (Load.fl k) ≤ 1) ∧
    ((List.range 12).map fun k => rowNat tr 11 r (Load.fl k)).sum ≤ 1 := by
  have hP' := P_val
  have hb : ∀ k, k < 12 → rowNat tr 11 r (Load.fl k) ≤ 1 := by
    intro k hk
    have := hcon (Chips.bool (v (Load.fl k))) (by
      simp only [Load.table, Load.constraints, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl ⟨k, hk, rfl⟩))
    simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow] at this
    have := bool_nat (rowNat_lt _ _ _ _) this; omega
  have hact := hcon (Chips.bool Load.act) (by simp [Load.table, Load.constraints])
  simp only [Chips.bool, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat'] at hact
  have ea : Load.act.eval (natRow (rowNat tr 11 r) (tr.row pub 11 r)) =
      ((((List.range 12).map fun k => rowNat tr 11 r (Load.fl k)).sum : Nat) : F) := by
    unfold Load.act Load.sumF
    rw [filter_true_range, fold_sum]; simp only [Expr.eval_ofNat']; grind
  rw [ea] at hact
  have hsl : ((List.range 12).map fun k => rowNat tr 11 r (Load.fl k)).sum ≤ 12 := by
    have h := sum_le_len ((List.range 12).map fun k => rowNat tr 11 r (Load.fl k)) (by
      intro x hx; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx; exact hb k (List.mem_range.mp hk))
    simpa using h
  have := bool_nat (by omega) hact
  exact ⟨hb, by omega⟩

theorem load_sumF_eval (tr : Trace) (pub : List F) (r : Nat) (p : Nat × Nat × Bool × Bool → Bool) :
    ((Load.sumF p).eval (tr.row pub 11 r)).toNat =
      ((((List.range 12).filter fun k => p (Load.ops.getD k default)).map fun k => rowNat tr 11 r (Load.fl k)).sum) % P := by
  rw [row_eq_natRow]
  unfold Load.sumF
  have e : ∀ n : Nat, ((0 : Nat) : F) + ((n : Nat) : F) = ((n : Nat) : F) := fun n => by grind
  rw [fold_sum, Expr.eval_ofNat', e, Fp.toNat_cast]

theorem load_count_mem (i : Inter) (hi : i ∈ Load.inters) :
    i.count = Load.act ∨ ∃ j, j < 8 ∧ i.count = Load.cnt j := by
  have := List.all_eq_true.mp
    (show Load.inters.all (fun i => decide (i.count = Load.act) ||
      (List.range 8).any (fun j => decide (i.count = Load.cnt j))) = true by decide) i hi
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range] at this
  exact this

theorem load_count_le_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Load.table.constraints, e.eval (natRow (rowNat tr 11 r) (tr.row pub 11 r)) = 0)
    (i : Inter) (hi : i ∈ Load.inters) :
    (i.count.eval (tr.row pub 11 r)).toNat ≤
      ((List.range 12).map fun k => rowNat tr 11 r (Load.fl k)).sum := by
  have hP' := P_val
  rcases load_count_mem i hi with h | ⟨j, _, h⟩ <;> rw [h]
  · unfold Load.act; rw [load_sumF_eval]; exact Nat.le_trans (Nat.mod_le _ _) (sum_filter_le _ _ _)
  · unfold Load.cnt; rw [load_sumF_eval]; exact Nat.le_trans (Nat.mod_le _ _) (sum_filter_le _ _ _)

theorem load_counts_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Load.table.constraints, e.eval (natRow (rowNat tr 11 r) (tr.row pub 11 r)) = 0) :
    ∀ i ∈ Load.inters, (i.count.eval (tr.row pub 11 r)).toNat ≤ 1 := fun i hi =>
  Nat.le_trans (load_count_le_of hcon i hi) (load_total_of hcon).2

theorem load_total {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 11) :
    (∀ k, k < 12 → rowNat tr 11 r (Load.fl k) ≤ 1) ∧
    ((List.range 12).map fun k => rowNat tr 11 r (Load.fl k)).sum ≤ 1 :=
  load_total_of (table_constr H (by simp [air_len]) hr)

theorem load_count_le {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 11) (i : Inter) (hi : i ∈ Load.inters) :
    (i.count.eval (tr.row pub 11 r)).toNat ≤
      ((List.range 12).map fun k => rowNat tr 11 r (Load.fl k)).sum :=
  load_count_le_of (table_constr H (by simp [air_len]) hr) i hi

theorem load_counts {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 11) :
    ∀ i ∈ Load.inters, (i.count.eval (tr.row pub 11 r)).toNat ≤ 1 :=
  load_counts_of (table_constr H (by simp [air_len]) hr)

theorem load_act_eval (tr : Trace) (pub : List F) (r : Nat) (hs : ((List.range 12).map fun k => rowNat tr 11 r (Load.fl k)).sum ≤ 1) :
    (Load.act.eval (tr.row pub 11 r)).toNat = ((List.range 12).map fun k => rowNat tr 11 r (Load.fl k)).sum := by
  unfold Load.act; rw [load_sumF_eval, filter_true_range, Nat.mod_eq_of_lt (by have := P_val; omega)]

theorem load_inactive {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 11)
    (hna : ¬ rowAct Load.table tr pub 11 r) :
    ∀ i ∈ Load.inters, (i.count.eval (tr.row pub 11 r)).toNat ≠ 1 := by
  obtain ⟨-, ht⟩ := load_total H hr
  have h0 : ((List.range 12).map fun k => rowNat tr 11 r (Load.fl k)).sum = 0 := by
    have : (Load.act.eval (tr.row pub 11 r)).toNat ≠ 1 := by
      simpa [rowAct, Load.table, Load.inters, stdState, stateIn] using hna
    rw [load_act_eval tr pub r ht] at this; omega
  intro i hi
  have := load_count_le H hr i hi
  omega

/-- Keeping the elements of `(range n).map f` whose count is `[i < w]`. -/
theorem filterMap_cnt (f : Nat → Inter) (rw : Row) (w : Nat)
    (hc : ∀ i, ((f i).count.eval rw).toNat = if i < w then 1 else 0) :
    ∀ n, ((List.range n).map f).filterMap (fun i => if (i.count.eval rw).toNat = 1 then
      some (i.msg.map (·.eval rw)) else none) = (List.range (min w n)).map (fun i => (f i).msg.map (·.eval rw)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.filterMap_append, ih]
    simp only [List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil, hc n]
    by_cases hn : n < w
    · rw [if_pos hn, if_pos rfl, show min w (n + 1) = min w n + 1 by omega, List.range_succ, List.map_append]
      rw [show min w n = n by omega]; rfl
    · rw [if_neg hn, if_neg (by decide), show min w (n + 1) = min w n by omega, List.append_nil]

theorem load_filterC :
    Load.table.inters.filter (fun i => i.bus = busStk ∧ i.send = false) =
      stkRecv (v Load.kSb + v cH - 1) 0 [v Load.a, v (Load.a + 1), 0, 0] (v Load.ta) Load.act ::
        (List.range 8).map (fun i => chRecv 3 (Load.eaE + Expr.c i) 0 [v (Load.b + i), 0, 0, 0] (v (Load.tb + i))
          (Load.cnt i)) := by decide

theorem load_filterP :
    Load.table.inters.filter (fun i => i.bus = busStk ∧ i.send = true) =
      (List.range 8).map (fun i => chSend 3 (Load.eaE + Expr.c i) 0 [v (Load.b + i), 0, 0, 0] (v cTs) (Load.cnt i)) ++
        [stkSend (v Load.kSb + v cH - 1) Load.is64 (limbsOf Load.r) (v cTs) Load.act] := by decide

theorem load_rowfacts {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hpub : PubOK X nloc ncode pub)
    {r : Nat} (hr : r < tr.height 11) (hact : rowAct Load.table tr pub 11 r) :
    RowFacts X (rowIn Load.table tr pub 11 r) (rowOut Load.table tr pub 11 r)
      (rowCons Load.table tr pub 11 r) (rowProd Load.table tr pub 11 r) := by
  have hP' := P_val
  have ht : 11 < (wasmBaseAir nloc ncode).tables.length := by simp [air_len]
  have hT : (wasmBaseAir nloc ncode).tables[11]'ht = Load.table := rfl
  have hcP : ∀ i, rowNat tr 11 r i < P := rowNat_lt tr 11 r
  have hcon : ∀ e ∈ Load.constraints, e.eval (natRow (rowNat tr 11 r) (tr.row pub 11 r)) = 0 :=
    table_constr H ht hr
  -- the selected op
  obtain ⟨hb, htot⟩ := load_total H hr
  have hsum1 : ((List.range 12).map fun k => rowNat tr 11 r (Load.fl k)).sum = 1 := by
    have : (Load.act.eval (tr.row pub 11 r)).toNat = 1 := by
      simpa [rowAct, Load.table, Load.inters, stdState, stateIn] using hact
    rwa [load_act_eval tr pub r htot] at this
  obtain ⟨k0, hk0, hone⟩ : ∃ k0, k0 < 12 ∧ ∀ k, k < 12 → rowNat tr 11 r (Load.fl k) = if k = k0 then 1 else 0 := by
    rcases onehot_range _ 12 hb (by omega) with h | h
    · exfalso
      have : ((List.range 12).map fun k => rowNat tr 11 r (Load.fl k)).sum = 0 := by
        have hz : ((List.range 12).map fun k => rowNat tr 11 r (Load.fl k)) = (List.range 12).map fun _ => 0 :=
          List.map_congr_left (fun k hk => h k (List.mem_range.mp hk))
        rw [hz]
        have z : ∀ l : List Nat, (l.map fun _ => 0).sum = 0 := by intro l; induction l <;> simp_all
        exact z _
      omega
    · exact h
  obtain ⟨o, ho⟩ : ∃ o, Load.ops.getD k0 default = o := ⟨_, rfl⟩
  have eF : ∀ p, (Load.sumF p).eval (tr.row pub 11 r) = ((if p o then 1 else 0 : Nat) : F) := fun p => by
    rw [row_eq_natRow, load_sumF _ _ k0 hk0 hone p, ho]
  have nF : ∀ p, ((Load.sumF p).eval (tr.row pub 11 r)).toNat = if p o then 1 else 0 := fun p => by
    rw [eF]; split <;> rfl
  have cA : (Load.act.eval (tr.row pub 11 r)).toNat = 1 := nF _
  have cC : ∀ i, ((Load.cnt i).eval (tr.row pub 11 r)).toNat = if i < o.2.1 then 1 else 0 := fun i => by
    unfold Load.cnt; rw [nF]; simp
  have hw : o.2.1 ≤ 8 ∧ 1 ≤ o.2.1 := by
    have : ∀ k, k < 12 → (Load.ops.getD k default).2.1 ≤ 8 ∧ 1 ≤ (Load.ops.getD k default).2.1 := by decide
    exact ho ▸ this k0 hk0
  have hocc : ∀ i ∈ Load.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 11 r)),
      (i.count.eval (tr.row pub 11 r)).toNat) ∈ occs (wasmBaseAir nloc ncode) tr pub := fun i hi =>
    row_occ ht hr (show i ∈ Load.table.inters from hi)
  -- `ea` (exact, < 2^28)
  have r16of := fun (e cnt : Expr) (hm : r16 e cnt ∈ Load.inters) (hc : (cnt.eval (tr.row pub 11 r)).toNat = 1) =>
    row_r16 L ht hr e cnt (by rw [hT]; exact hm) hc
  have bE0 := r16of (v Load.e) Load.act (by simp [Load.inters]) cA
  have bE1 := r16of (32 * v (Load.e + 1)) Load.act (by simp [Load.inters]) cA
  simp only [v, Expr.eval_mul', Expr.eval_col, Expr.eval_ofNat', Trace.row, Load.e, cell_cast,
    Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _), Nat.reduceAdd] at bE0 bE1
  let eaN := rowNat tr 11 r 23 + 2048 * (((32 : Nat) : F) * ((rowNat tr 11 r 24 : Nat) : F)).toNat
  have hEa : ∀ i, i < 8 → (Load.eaE.eval (tr.row pub 11 r) + ((i : Nat) : F)).toNat = eaN + i := by
    intro i hi
    have e : Load.eaE.eval (tr.row pub 11 r) = ((rowNat tr 11 r 23 : Nat) : F) + ((65536 : Nat) : F) *
        ((rowNat tr 11 r 24 : Nat) : F) := by
      simp only [Load.eaE, v, Expr.eval_add', Expr.eval_mul', Expr.eval_col, Expr.eval_ofNat', Trace.row, Load.e,
        cell_cast]
    have h1 := split27 e (by rw [Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)]; omega) bE1
    rw [Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)] at h1
    rw [← Fp.cast_toNat (Load.eaE.eval (tr.row pub 11 r)), h1, ← Lean.Grind.Semiring.natCast_add,
      Fp.toNat_cast_of_lt (by omega)]
  -- messages
  have hIn : rowIn Load.table tr pub 11 r =
      [((rowNat tr 11 r 0 : Nat) : F), ((rowNat tr 11 r 1 : Nat) : F), ((rowNat tr 11 r 2 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 11 r 56 : Nat) : F), ((rowNat tr 11 r 57 : Nat) : F)] := by
    simp only [rowIn, Load.table, Load.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero,
      List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row, Load.kSb, Load.kCid,
      cPc, cTs, cS]
  have hOut : rowOut Load.table tr pub 11 r =
      [((rowNat tr 11 r 0 : Nat) : F) + ((1 : Nat) : F), ((rowNat tr 11 r 1 : Nat) : F) + ((1 : Nat) : F),
        ((rowNat tr 11 r 2 : Nat) : F) + ((rowNat tr 11 r 4 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 11 r 56 : Nat) : F), ((rowNat tr 11 r 57 : Nat) : F)] := by
    simp only [rowOut, Load.table, Load.inters, stdState, stateOut, List.cons_append, List.getD_cons_succ,
      List.getD_cons_zero, List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_add', Expr.eval_ofNat',
      cell_cast, Trace.row, Load.kSb, Load.kCid, cPc, cTs, cS, cFee]
  let ma : Msg := ⟨0, (((rowNat tr 11 r 56 : Nat) : F) + ((rowNat tr 11 r 3 : Nat) : F) - ((1 : Nat) : F)).toNat, 0,
    rowNat tr 11 r 17, rowNat tr 11 r 18, 0, 0, rowNat tr 11 r 19⟩
  let mb : Nat → Nat → Msg := fun i tp => encB (eaN + i) (rowNat tr 11 r (26 + i)) tp
  have hCons : rowCons Load.table tr pub 11 r =
      ma :: (List.range o.2.1).map fun i => mb i (rowNat tr 11 r (34 + i)) := by
    rw [rowCons, rowMsgs_eq, load_filterC, List.filterMap_cons]
    simp only [stkRecv, chRecv, cA, ite_true]
    rw [filterMap_cnt _ _ o.2.1 (fun i => cC i) 8, show min o.2.1 8 = o.2.1 by omega]
    simp only [List.map_cons, List.map_map]
    congr 1
    · simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, v, Expr.eval_col, Expr.eval_add',
        Expr.eval_sub', Expr.eval_ofNat', Trace.row, Load.kSb, cH, Load.a, Load.ta, Nat.reduceAdd, cell_cast, decMsg,
        List.getD_cons_zero, List.getD_cons_succ, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _), ma]
      rfl
    · refine List.map_congr_left fun i hi => ?_
      have hi8 : i < 8 := by rw [List.mem_range] at hi; omega
      simp only [Function.comp, List.map_cons, List.map_nil, List.cons_append, List.nil_append, decMsg,
        List.getD_cons_zero, List.getD_cons_succ, Expr.eval_add', Expr.eval_c]
      rw [hEa i hi8]
      simp only [v, Expr.eval_col, Expr.eval_ofNat', Trace.row, cell_cast, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _),
        mb, encB, Load.b, Load.tb]
      rfl
  have hProd : rowProd Load.table tr pub 11 r =
      ((List.range o.2.1).map fun i => mb i (rowNat tr 11 r 1)) ++
        [⟨0, (((rowNat tr 11 r 56 : Nat) : F) + ((rowNat tr 11 r 3 : Nat) : F) - ((1 : Nat) : F)).toNat,
          if o.2.2.2 then 1 else 0, rowNat tr 11 r 52, rowNat tr 11 r 53, rowNat tr 11 r 54, rowNat tr 11 r 55,
          rowNat tr 11 r 1⟩] := by
    rw [rowProd, rowMsgs_eq, load_filterP, List.filterMap_append,
      filterMap_cnt _ _ o.2.1 (fun i => cC i) 8, show min o.2.1 8 = o.2.1 by omega]
    simp only [List.filterMap_cons, List.filterMap_nil, stkSend, chSend, cA, ite_true]
    rw [List.map_append, List.map_map]
    congr 1
    · refine List.map_congr_left fun i hi => ?_
      have hi8 : i < 8 := by rw [List.mem_range] at hi; omega
      simp only [Function.comp, List.map_cons, List.map_nil, List.cons_append, List.nil_append, decMsg,
        List.getD_cons_zero, List.getD_cons_succ, Expr.eval_add', Expr.eval_c]
      rw [hEa i hi8]
      simp only [v, Expr.eval_col, Expr.eval_ofNat', Trace.row, cell_cast, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _),
        mb, encB, Load.b, cTs]
      rfl
    · have ni : (Load.is64.eval (tr.row pub 11 r)).toNat = if o.2.2.2 then 1 else 0 := nF _
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, decMsg, List.getD_cons_zero,
        List.getD_cons_succ]
      rw [ni]
      simp only [v, Expr.eval_col, Expr.eval_add', Expr.eval_sub', Expr.eval_ofNat', Trace.row, Load.kSb, cH, cTs,
        limbsOf, List.range, List.range.loop, Load.r, Nat.reduceAdd, cell_cast, List.map_cons, List.map_nil,
        List.getD_cons_zero, List.getD_cons_succ, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)]
      rfl
  -- time checks
  have tchk : ∀ (cnt : Expr) (tpc hic : Nat), (cnt.eval (tr.row pub 11 r)).toNat = 1 →
      r16 (v cTs - v tpc - 1 - B16 * v hic) cnt ∈ Load.inters → r16 (4 * v hic) cnt ∈ Load.inters →
      ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((rowNat tr 11 r tpc + 1 + n : Nat) : F) = ((rowNat tr 11 r 1 : Nat) : F) := by
    intro cnt tpc hic hc m1 m2
    have h1 := hocc _ m1
    have h2 := hocc _ m2
    simp only [r16] at h1 h2
    rw [hc] at h1 h2
    simp only [List.map_cons, List.map_nil, Expr.eval_sub', Expr.eval_mul', v, Expr.eval_col, Expr.eval_ofNat',
      B16, cTs, Trace.row] at h1 h2
    obtain ⟨n, hn, e⟩ := time_chk L h1 h2
    exact ⟨n, hn, e.trans (cell_cast tr 11 r 1)⟩
  have tA := tchk Load.act Load.ta Load.ha cA (by simp [Load.inters, timeChk]) (by simp [Load.inters, timeChk])
  have tB : ∀ i, i < o.2.1 → ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧
      ((rowNat tr 11 r (34 + i) + 1 + n : Nat) : F) = ((rowNat tr 11 r 1 : Nat) : F) := by
    intro i hi
    have hi8 : i < 8 := by omega
    have hm : ∀ j ∈ timeChk (v cTs) (v (Load.tb + i)) (v (Load.hb + i)) (Load.cnt i), j ∈ Load.inters := by
      intro j hj
      simp only [Load.inters, List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inl (Or.inr ⟨i, hi8, Or.inl (Or.inr hj)⟩)
    have := tchk (Load.cnt i) (Load.tb + i) (Load.hb + i) (by rw [cC]; simp [hi])
      (hm _ (by simp [timeChk])) (hm _ (by simp [timeChk]))
    simpa [Load.tb] using this
  -- the FETCH query
  have hfetch := hocc (fetch (v cPc) Load.op (v cH) (v cFee) [v Load.off, v (Load.off + 1), 0, 0] Load.act)
    (by simp [Load.inters, stdState])
  simp only [fetch] at hfetch
  rw [cA] at hfetch
  obtain ⟨pc0, hpc0, hm0⟩ := fetch_pc hpub L hfetch
  obtain ⟨q, l, ins, fee, rec, hq, hl, hoff, hins, hfee, hfl, hrc, hm⟩ := fetch_rec hpub L hfetch hm0 hpc0
  have CF := X.factsOf hq
  obtain ⟨op, x0, x1, x2, x3, hre, hcase⟩ := recordOf_spec hrc
  have hoplt := recordOf_op_lt hrc
  rw [hre] at hm hoplt
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hoplt
  have eOp : Load.op.eval (tr.row pub 11 r) = ((o.1 : Nat) : F) := by
    rw [row_eq_natRow, load_op_eval _ _ k0 hk0 hone, ho]
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm
  rw [eOp] at hm
  simp only [v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row, cPc, cH, cFee, Load.off] at hm
  obtain ⟨e0, eop, eh, efee, ex0, ex1, -, -⟩ := hm
  have fee16 := feeUnits_lt hfee
  have efee' : rowNat tr 11 r 4 = fee := natEq efee (hcP _) (by omega)
  have hopr : 0x28 ≤ o.1 ∧ o.1 ≤ 0x35 ∧ isLoadOp o.1 = true := by
    have : ∀ k, k < 12 → 0x28 ≤ (Load.ops.getD k default).1 ∧ (Load.ops.getD k default).1 ≤ 0x35 ∧
        isLoadOp (Load.ops.getD k default).1 = true := by decide
    exact ho ▸ this k0 hk0
  have hop : op = o.1 := (natEq eop (by omega) (by omega)).symm
  -- RowFacts
  refine ⟨?_, by rw [hIn]; rfl, by rw [hIn, hOut]; rfl,
    ⟨fee, hfl, by rw [hIn, hOut]; simp only [gasF, List.getD_cons_succ, List.getD_cons_zero, efee']⟩, ?_, ?_, ?_⟩
  rotate_left
  · rw [hCons, hIn]
    intro x hx
    simp only [List.mem_cons, List.mem_map, List.mem_range] at hx
    simp only [lvl, List.getD_cons_succ, List.getD_cons_zero]
    rcases hx with rfl | ⟨i, hi, rfl⟩
    · exact tA
    · obtain ⟨n, hn, e⟩ := tB i hi; exact ⟨n, hn, e⟩
  · rw [hProd, hIn]
    intro x hx
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hx
    simp only [lvl, List.getD_cons_succ, List.getD_cons_zero]
    rcases hx with ⟨i, _, rfl⟩ | rfl
    · exact ⟨hcP _, rfl⟩
    · exact ⟨hcP _, rfl⟩
  · rw [hProd, List.nodup_append]
    refine ⟨?_, by simp, ?_⟩
    · exact List.pairwise_map.mpr ((List.pairwise_lt_range).imp fun h e => by
        have := congrArg Msg.slot e; simp only [mb, encB_slot] at this; omega)
    · intro x hx y hy hxy
      subst hxy
      simp only [List.mem_map, List.mem_range, List.mem_singleton] at hx hy
      obtain ⟨i, _, rfl⟩ := hx
      have := congrArg Msg.space hy; simp [mb, encB] at this
  -- the spec step
  intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
  rw [hIn] at hin
  obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
  have hpcl := R.pcLt
  have hoffb := X.off_bound R.kLt
  have htot := X.mf.total
  have p0 : rowNat tr 11 r 0 = X.offOf E.k + pc := natEq i0 (hcP _) (by omega)
  have p1 : rowNat tr 11 r 1 = t := natEq i1 (hcP _) (by omega)
  have p2 : rowNat tr 11 r 2 = S := natEq i2 (hcP _) (by omega)
  have psb : rowNat tr 11 r 56 = E.sb := natEq i4 (hcP _) (by have := R.sbLt; omega)
  have pcid : rowNat tr 11 r 57 = E.cid := natEq i5 (hcP _) (by have := R.cidLt; omega)
  have hsbR := R.sbLe
  have hpc : pc0 = X.offOf E.k + pc := natEq (e0.symm.trans i0) (by omega) (by omega)
  subst hpc
  obtain ⟨hqk, hlpc⟩ := X.loc_unique hq hl R.kLt hpcl hoff
  subst q
  subst l
  have hH := R.height
  have hHb := CF.hBound pc hpcl
  rw [hH] at eh hHb
  simp only [Option.getD_some] at eh hHb
  have p3 : rowNat tr 11 r 3 = s.stack.size - E.sb := natEq eh (hcP _) (by omega)
  have hszP : s.stack.size < P := by have := R.sbLt; omega
  have hout : rowOut Load.table tr pub 11 r = stMsg (X.offOf E.k + pc + 1) (t + 1) (S + fee) 0 E.sb E.cid := by
    rw [hOut, p0, p1, p2, efee', psb, pcid]
    simp only [stMsg, Lean.Grind.Semiring.natCast_add]
  rw [hCons] at hlive ⊢
  rw [hProd]
  refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfl, by omega, (by rw [hout, Nat.add_assoc]), fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
  -- the instruction is the load
  obtain ⟨al, off, hinsE, -, hisL, hoff, hxs⟩ : ∃ al off, ins = .load op al off ∧ (0x28 ≤ op ∧ op ≤ 0x35) ∧
      isLoadOp op = true ∧ off < 2 ^ 32 ∧ [x0, x1, x2, x3] = [off % 65536, off / 65536, 0, 0] := by
    rcases hcase with ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ |
      ⟨_, _, h, _⟩ | ⟨_, hf, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | hl | ⟨_, _, _, hmem, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, _, h, _⟩
    all_goals first
      | exact hl
      | (exfalso; omega)
      | (exfalso; simp only [isFamilyNum, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hf; omega)
      | (exfalso; simp only [Ctrl.opNext, Ctrl.opJump, Ctrl.opJif, Ctrl.opHalt, Ctrl.opHif] at h; omega)
      | (exfalso; simp only [opCall] at h; omega)
  subst hinsE
  simp only [List.cons.injEq, and_true] at hxs
  obtain ⟨hx0, hx1, -, -⟩ := hxs
  subst hx0 hx1
  have c21 : rowNat tr 11 r 21 = off % 65536 := natEq ex0 (hcP _) (by omega)
  have c22 : rowNat tr 11 r 22 = off / 65536 := natEq ex1 (hcP _) (by omega)
  obtain ⟨ls0, hL0, -⟩ := R.labels
  obtain ⟨h1, -⟩ := verify_straight X R.kLt hpcl hins hL0 R.height (pops := 1) (pushes := 1)
    (by simp [kindOf, hisL, hoff]) (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp)
    (by intro l; simp)
  have hslot : ma.slot = s.stack.size - 1 := slot_toNat psb p3 hsbR h1 hszP
  -- the constraints
  have hcy : rowNat tr 11 r 25 = 0 ∨ rowNat tr 11 r 25 = 1 := by
    have := hcon (Chips.bool (v Load.cyE)) (by simp [Load.constraints])
    simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow, Load.cyE] at this
    exact bool_nat (hcP _) this
  have hsb : rowNat tr 11 r 50 = 0 ∨ rowNat tr 11 r 50 = 1 := by
    have := hcon (Chips.bool (v Load.sbit)) (by simp [Load.constraints])
    simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow, Load.sbit] at this
    exact bool_nat (hcP _) this
  have hq0 := hcon (v Load.a + v Load.off - v Load.e - 65536 * v Load.cyE) (by simp [Load.constraints])
  have hq1 := hcon (v (Load.e + 1) - v (Load.a + 1) - v (Load.off + 1) - v Load.cyE) (by simp [Load.constraints])
  simp only [v, Expr.eval_sub', Expr.eval_add', Expr.eval_mul', Expr.eval_col, Expr.eval_ofNat', natRow, Load.a,
    Load.off, Load.e, Load.cyE, Nat.reduceAdd] at hq0 hq1
  have hea : ma.ok → ma.val + off = eaN := by
    intro ok
    obtain ⟨a0, a1, -, -, -⟩ := ok
    simp only [ma] at a0 a1
    have n0 : rowNat tr 11 r 17 + rowNat tr 11 r 21 = rowNat tr 11 r 23 + 65536 * rowNat tr 11 r 25 := by
      have : ((rowNat tr 11 r 17 + rowNat tr 11 r 21 : Nat) : F) =
          ((rowNat tr 11 r 23 + 65536 * rowNat tr 11 r 25 : Nat) : F) := by
        simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]; grind
      exact natEq this (by omega) (by omega)
    have n1 : rowNat tr 11 r 24 = rowNat tr 11 r 18 + rowNat tr 11 r 22 + rowNat tr 11 r 25 := by
      have : ((rowNat tr 11 r 24 : Nat) : F) = ((rowNat tr 11 r 18 + rowNat tr 11 r 22 + rowNat tr 11 r 25 : Nat) : F) := by
        simp only [Lean.Grind.Semiring.natCast_add]; grind
      exact natEq this (hcP _) (by omega)
    have ny : (((32 : Nat) : F) * ((rowNat tr 11 r 24 : Nat) : F)).toNat = 32 * rowNat tr 11 r 24 := by
      rw [← Lean.Grind.Semiring.natCast_mul, Fp.toNat_cast_of_lt (by omega)]
    simp only [eaN, ny, ma, Msg.val, val4]
    omega
  -- the flag sums on the natural row
  have eN : ∀ p, (Load.sumF p).eval (natRow (rowNat tr 11 r) (tr.row pub 11 r)) = ((if p o then 1 else 0 : Nat) : F) :=
    fun p => by rw [load_sumF _ _ k0 hk0 hone p, ho]
  have hwv : o.2.1 = 1 ∨ o.2.1 = 2 ∨ o.2.1 = 4 ∨ o.2.1 = 8 := by
    have : ∀ k, k < 12 → (Load.ops.getD k default).2.1 = 1 ∨ (Load.ops.getD k default).2.1 = 2 ∨
        (Load.ops.getD k default).2.1 = 4 ∨ (Load.ops.getD k default).2.1 = 8 := by decide
    exact ho ▸ this k0 hk0
  let b' : Nat → Nat := fun i => if i < o.2.1 then rowNat tr 11 r (26 + i) else 0
  -- the top byte
  have htopF : ((rowNat tr 11 r (26 + (o.2.1 - 1)) : Nat) : F) =
      ((128 : Nat) : F) * ((rowNat tr 11 r 50 : Nat) : F) + ((rowNat tr 11 r 51 : Nat) : F) := by
    have h := hcon (Load.topB - 128 * v Load.sbit - v Load.low7) (by simp [Load.constraints])
    simp only [Load.topB, Load.lastE, List.range, List.range.loop, List.foldl, Expr.eval_sub', Expr.eval_add',
      Expr.eval_mul', Expr.eval_ofNat', eN, v, Expr.eval_col, natRow_cur, Load.b, Load.sbit, Load.low7, Nat.reduceAdd] at h
    rcases hwv with hw1 | hw1 | hw1 | hw1 <;> simp only [hw1] at h ⊢ <;> simp at h ⊢ <;> grind
  have bLow := row_r16 L ht hr (512 * v Load.low7) Load.act (by rw [hT]; simp [Load.table, Load.inters]) cA
  simp only [v, Expr.eval_mul', Expr.eval_col, Expr.eval_ofNat', Trace.row, Load.low7, cell_cast] at bLow
  -- the result bytes
  have eB : ∀ i, i < 8 → (Load.B i).eval (natRow (rowNat tr 11 r) (tr.row pub 11 r)) =
      ((loadB k0 b' (rowNat tr 11 r 50) i : Nat) : F) := by
    intro i hi
    simp only [Load.B, Load.ext, Load.cnt, Load.sgn, Load.is64, Expr.eval_add', Expr.eval_mul', Expr.eval_sub',
      Expr.eval_ofNat', eN, v, Expr.eval_col, natRow_cur, Load.b, Load.sbit, loadB, b', ho]
    by_cases hiw : i < o.2.1
    · simp only [hiw, decide_true, ite_true]; grind
    · simp only [hiw, decide_false, ite_false, Bool.false_eq_true]
      by_cases h4 : i < 4 <;> simp only [h4, ite_true, ite_false, eN] <;>
        cases o.2.2.1 <;> cases o.2.2.2 <;> simp [Lean.Grind.Semiring.natCast_mul] <;> grind
  have hspec : loadSpec o.1 = (o.2.1, o.2.2.1, o.2.2.2) := by
    have : ∀ k, k < 12 → loadSpec (Load.ops.getD k default).1 = ((Load.ops.getD k default).2.1,
        (Load.ops.getD k default).2.2.1, (Load.ops.getD k default).2.2.2) := by decide
    exact ho ▸ this k0 hk0
  let mres : Msg := ⟨0, (((rowNat tr 11 r 56 : Nat) : F) + ((rowNat tr 11 r 3 : Nat) : F) - ((1 : Nat) : F)).toNat,
    if o.2.2.2 then 1 else 0, rowNat tr 11 r 52, rowNat tr 11 r 53, rowNat tr 11 r 54, rowNat tr 11 r 55,
    rowNat tr 11 r 1⟩
  have hmr : (∀ i, i < (loadSpec op).1 → rowNat tr 11 r (26 + i) < 256) →
      mres = enc 0 (s.stack.size - 1) (loadVal op (leVal (fun i => rowNat tr 11 r (26 + i)) 0 (loadSpec op).1)) t := by
    rw [hop, hspec]
    intro hbv
    have hb8 : ∀ i, i < 8 → b' i < 256 := fun i hi => by
      simp only [b']; split
      · exact hbv i ‹_›
      · omega
    have hs1 : rowNat tr 11 r 50 ≤ 1 := by omega
    have hl : ∀ i, i < 8 → loadB k0 b' (rowNat tr 11 r 50) i ≤ 255 := by
      intro i hi; simp only [loadB, ho]
      split
      · have := hb8 i hi; omega
      · cases o.2.2.1 <;> cases o.2.2.2 <;> by_cases h4 : i < 4 <;> simp [h4] <;> omega
    have hR : ∀ j, j < 4 → rowNat tr 11 r (52 + j) =
        loadB k0 b' (rowNat tr 11 r 50) (2 * j) + 256 * loadB k0 b' (rowNat tr 11 r 50) (2 * j + 1) := by
      intro j hj
      have h := hcon (v (Load.r + j) - (Load.B (2 * j) + 256 * Load.B (2 * j + 1))) (by
        simp only [Load.constraints, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inr ⟨j, hj, rfl⟩)
      simp only [Expr.eval_sub', Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', v, Expr.eval_col, natRow_cur, Load.r,
        eB (2 * j) (by omega), eB (2 * j + 1) (by omega)] at h
      have := hl (2 * j) (by omega); have := hl (2 * j + 1) (by omega)
      exact natEq (show ((rowNat tr 11 r (52 + j) : Nat) : F) = ((loadB k0 b' (rowNat tr 11 r 50) (2 * j) +
        256 * loadB k0 b' (rowNat tr 11 r 50) (2 * j + 1) : Nat) : F) by
          simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]; grind) (hcP _) (by omega)
    -- the sign bit and the low bits of the top byte
    have htb : rowNat tr 11 r (26 + (o.2.1 - 1)) < 256 := hbv _ (by omega)
    obtain ⟨low, hlow, hlt⟩ : ∃ low, rowNat tr 11 r (26 + (o.2.1 - 1)) = 128 * rowNat tr 11 r 50 + low ∧ low < 128 := by
      rcases hsb with h0 | h0 <;> rw [h0] at htopF ⊢
      · have e1 : ((rowNat tr 11 r 51 : Nat) : F) = ((rowNat tr 11 r (26 + (o.2.1 - 1)) : Nat) : F) := by
          rw [htopF]; grind
        have e2 := natEq e1 (hcP _) (hcP _)
        rw [e2, ← Lean.Grind.Semiring.natCast_mul, Fp.toNat_cast_of_lt (by omega)] at bLow
        exact ⟨rowNat tr 11 r (26 + (o.2.1 - 1)), by omega, by omega⟩
      · by_cases hge : 128 ≤ rowNat tr 11 r (26 + (o.2.1 - 1))
        · have e1 : ((rowNat tr 11 r 51 : Nat) : F) = ((rowNat tr 11 r (26 + (o.2.1 - 1)) - 128 : Nat) : F) := by
            have : ((rowNat tr 11 r (26 + (o.2.1 - 1)) : Nat) : F) =
                ((rowNat tr 11 r (26 + (o.2.1 - 1)) - 128 : Nat) : F) + ((128 : Nat) : F) := by
              rw [← Lean.Grind.Semiring.natCast_add, Nat.sub_add_cancel hge]
            rw [this] at htopF; grind
          have e2 := natEq e1 (hcP _) (by omega)
          rw [e2, ← Lean.Grind.Semiring.natCast_mul, Fp.toNat_cast_of_lt (by omega)] at bLow
          exact ⟨rowNat tr 11 r (26 + (o.2.1 - 1)) - 128, by omega, by omega⟩
        · exfalso
          have e1 : ((512 : Nat) : F) * ((rowNat tr 11 r 51 : Nat) : F) =
              ((P - 512 * (128 - rowNat tr 11 r (26 + (o.2.1 - 1))) : Nat) : F) := by
            have hP0 : ((P : Nat) : F) = ((0 : Nat) : F) := eq_of_toNat (by rw [Fp.toNat_cast, Nat.mod_self])
            have : ((P - 512 * (128 - rowNat tr 11 r (26 + (o.2.1 - 1))) : Nat) : F) +
                ((512 * (128 - rowNat tr 11 r (26 + (o.2.1 - 1))) : Nat) : F) = ((P : Nat) : F) := by
              rw [← Lean.Grind.Semiring.natCast_add, Nat.sub_add_cancel (by omega)]
            have h2 : ((512 * (128 - rowNat tr 11 r (26 + (o.2.1 - 1))) : Nat) : F) +
                ((512 * rowNat tr 11 r (26 + (o.2.1 - 1)) : Nat) : F) = ((65536 : Nat) : F) := by
              rw [← Lean.Grind.Semiring.natCast_add]; congr 1; omega
            rw [hP0] at this
            simp only [Lean.Grind.Semiring.natCast_mul] at h2 this ⊢
            grind
          rw [e1, Fp.toNat_cast_of_lt (by omega)] at bLow
          omega
    have LS := load_sem k0 hk0
    simp only [LoadSem, ho] at LS
    obtain ⟨hv, htag⟩ := LS b' hb8 (rowNat tr 11 r 50) low hs1 hlt (by
      simp only [b', show o.2.1 - 1 < o.2.1 by omega, ite_true]; exact hlow)
    have hle : leVal (fun i => rowNat tr 11 r (26 + i)) 0 o.2.1 = leVal b' 0 o.2.1 :=
      leVal_congr (fun i hi => by simp only [b', Nat.zero_add, hi, ite_true])
    rw [hle, enc_limbs (by have := hl 0 (by omega); have := hl 1 (by omega); omega)
      (by have := hl 2 (by omega); have := hl 3 (by omega); omega)
      (by have := hl 4 (by omega); have := hl 5 (by omega); omega)
      (by have := hl 6 (by omega); have := hl 7 (by omega); omega) hv, htag]
    have r0 := hR 0 (by omega); have r1 := hR 1 (by omega); have r2 := hR 2 (by omega); have r3 := hR 3 (by omega)
    simp only [Nat.reduceAdd, Nat.reduceMul] at r0 r1 r2 r3
    simp only [mres, r0, r1, r2, r3, p1]
    rw [show (((rowNat tr 11 r 56 : Nat) : F) + ((rowNat tr 11 r 3 : Nat) : F) - ((1 : Nat) : F)).toNat =
      s.stack.size - 1 from hslot]
  have hw' : (loadSpec op).1 = o.2.1 := by rw [hop, hspec]
  obtain ⟨s', hs', hrel⟩ := step_load X R hins hisL hoff hfee hg hg64 ma (hlive ma List.mem_cons_self)
    ⟨rfl, hslot⟩ eaN hea (fun i => rowNat tr 11 r (26 + i)) (fun i => rowNat tr 11 r (34 + i))
    (fun i hi => hlive _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩)))
    mres hmr
  rw [hw'] at hrel
  refine ⟨s', hs', ?_⟩
  subst p1
  rw [stepLive_congr (c2 := ma :: (List.range o.2.1).map fun i => encB (eaN + i) (rowNat tr 11 r (26 + i))
      (rowNat tr 11 r (34 + i)))
    (p2 := mres :: (List.range o.2.1).map fun i => encB (eaN + i) (rowNat tr 11 r (26 + i)) (rowNat tr 11 r 1)) (fun _ => Iff.rfl)
    (fun x => by
      simp only [List.mem_append, List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false, mb]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h)]
  exact hrel

/-- The flags of a STORE row: bits with sum ≤ 1 (the sum is `act`). -/
theorem store_total_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Store.table.constraints, e.eval (natRow (rowNat tr 12 r) (tr.row pub 12 r)) = 0) :
    (∀ k, k < 7 → rowNat tr 12 r (Store.fl k) ≤ 1) ∧
    ((List.range 7).map fun k => rowNat tr 12 r (Store.fl k)).sum ≤ 1 := by
  have hP' := P_val
  have hb : ∀ k, k < 7 → rowNat tr 12 r (Store.fl k) ≤ 1 := by
    intro k hk
    have := hcon (Chips.bool (v (Store.fl k))) (by
      simp only [Store.table, Store.constraints, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl ⟨k, hk, rfl⟩))
    simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow] at this
    have := bool_nat (rowNat_lt _ _ _ _) this; omega
  have hact := hcon (Chips.bool Store.act) (by simp [Store.table, Store.constraints])
  simp only [Chips.bool, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat'] at hact
  have ea : Store.act.eval (natRow (rowNat tr 12 r) (tr.row pub 12 r)) =
      ((((List.range 7).map fun k => rowNat tr 12 r (Store.fl k)).sum : Nat) : F) := by
    unfold Store.act Store.sumF
    rw [filter_true_range, fold_sum]; simp only [Expr.eval_ofNat']; grind
  rw [ea] at hact
  have hsl : ((List.range 7).map fun k => rowNat tr 12 r (Store.fl k)).sum ≤ 7 := by
    have h := sum_le_len ((List.range 7).map fun k => rowNat tr 12 r (Store.fl k)) (by
      intro x hx; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx; exact hb k (List.mem_range.mp hk))
    simpa using h
  have := bool_nat (by omega) hact
  exact ⟨hb, by omega⟩

theorem store_sumF_eval (tr : Trace) (pub : List F) (r : Nat) (p : Nat × Nat × Bool → Bool) :
    ((Store.sumF p).eval (tr.row pub 12 r)).toNat =
      ((((List.range 7).filter fun k => p (Store.ops.getD k default)).map fun k => rowNat tr 12 r (Store.fl k)).sum) % P := by
  rw [row_eq_natRow]
  unfold Store.sumF
  have e : ∀ n : Nat, ((0 : Nat) : F) + ((n : Nat) : F) = ((n : Nat) : F) := fun n => by grind
  rw [fold_sum, Expr.eval_ofNat', e, Fp.toNat_cast]

theorem store_count_mem (i : Inter) (hi : i ∈ Store.inters) :
    i.count = Store.act ∨ ∃ j, j < 8 ∧ i.count = Store.cnt j := by
  have := List.all_eq_true.mp
    (show Store.inters.all (fun i => decide (i.count = Store.act) ||
      (List.range 8).any (fun j => decide (i.count = Store.cnt j))) = true by decide) i hi
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range] at this
  exact this

theorem store_count_le_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Store.table.constraints, e.eval (natRow (rowNat tr 12 r) (tr.row pub 12 r)) = 0)
    (i : Inter) (hi : i ∈ Store.inters) :
    (i.count.eval (tr.row pub 12 r)).toNat ≤
      ((List.range 7).map fun k => rowNat tr 12 r (Store.fl k)).sum := by
  have hP' := P_val
  rcases store_count_mem i hi with h | ⟨j, _, h⟩ <;> rw [h]
  · unfold Store.act; rw [store_sumF_eval]; exact Nat.le_trans (Nat.mod_le _ _) (sum_filter_le _ _ _)
  · unfold Store.cnt; rw [store_sumF_eval]; exact Nat.le_trans (Nat.mod_le _ _) (sum_filter_le _ _ _)

theorem store_counts_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Store.table.constraints, e.eval (natRow (rowNat tr 12 r) (tr.row pub 12 r)) = 0) :
    ∀ i ∈ Store.inters, (i.count.eval (tr.row pub 12 r)).toNat ≤ 1 := fun i hi =>
  Nat.le_trans (store_count_le_of hcon i hi) (store_total_of hcon).2

theorem store_total {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 12) :
    (∀ k, k < 7 → rowNat tr 12 r (Store.fl k) ≤ 1) ∧
    ((List.range 7).map fun k => rowNat tr 12 r (Store.fl k)).sum ≤ 1 :=
  store_total_of (table_constr H (by simp [air_len]) hr)

theorem store_count_le {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 12) (i : Inter) (hi : i ∈ Store.inters) :
    (i.count.eval (tr.row pub 12 r)).toNat ≤
      ((List.range 7).map fun k => rowNat tr 12 r (Store.fl k)).sum :=
  store_count_le_of (table_constr H (by simp [air_len]) hr) i hi

theorem store_counts {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 12) :
    ∀ i ∈ Store.inters, (i.count.eval (tr.row pub 12 r)).toNat ≤ 1 :=
  store_counts_of (table_constr H (by simp [air_len]) hr)

theorem store_act_eval (tr : Trace) (pub : List F) (r : Nat) (hs : ((List.range 7).map fun k => rowNat tr 12 r (Store.fl k)).sum ≤ 1) :
    (Store.act.eval (tr.row pub 12 r)).toNat = ((List.range 7).map fun k => rowNat tr 12 r (Store.fl k)).sum := by
  unfold Store.act; rw [store_sumF_eval, filter_true_range, Nat.mod_eq_of_lt (by have := P_val; omega)]

theorem store_inactive {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 12)
    (hna : ¬ rowAct Store.table tr pub 12 r) :
    ∀ i ∈ Store.inters, (i.count.eval (tr.row pub 12 r)).toNat ≠ 1 := by
  obtain ⟨-, ht⟩ := store_total H hr
  have h0 : ((List.range 7).map fun k => rowNat tr 12 r (Store.fl k)).sum = 0 := by
    have : (Store.act.eval (tr.row pub 12 r)).toNat ≠ 1 := by
      simpa [rowAct, Store.table, Store.inters, stdState, stateIn] using hna
    rw [store_act_eval tr pub r ht] at this; omega
  intro i hi
  have := store_count_le H hr i hi
  omega


theorem store_filterC :
    Store.table.inters.filter (fun i => i.bus = busStk ∧ i.send = false) =
      stkRecv (v Store.kSb + v cH - 1) Store.is64 (limbsOf Store.vl) (v Store.tv) Store.act ::
      stkRecv (v Store.kSb + v cH - 2) 0 [v Store.a, v (Store.a + 1), 0, 0] (v Store.ta) Store.act ::
        (List.range 8).map (fun i => chRecv 3 (Store.eaE + Expr.c i) 0 [v (Store.ob + i), 0, 0, 0]
          (v (Store.tob + i)) (Store.cnt i)) := by decide

theorem store_filterP :
    Store.table.inters.filter (fun i => i.bus = busStk ∧ i.send = true) =
      (List.range 8).map (fun i => chSend 3 (Store.eaE + Expr.c i) 0 [v (Store.vb + i), 0, 0, 0] (v cTs)
        (Store.cnt i)) := by decide

theorem store_rowfacts {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hpub : PubOK X nloc ncode pub)
    {r : Nat} (hr : r < tr.height 12) (hact : rowAct Store.table tr pub 12 r) :
    RowFacts X (rowIn Store.table tr pub 12 r) (rowOut Store.table tr pub 12 r)
      (rowCons Store.table tr pub 12 r) (rowProd Store.table tr pub 12 r) := by
  have hP' := P_val
  have ht : 12 < (wasmBaseAir nloc ncode).tables.length := by simp [air_len]
  have hT : (wasmBaseAir nloc ncode).tables[12]'ht = Store.table := rfl
  have hcP : ∀ i, rowNat tr 12 r i < P := rowNat_lt tr 12 r
  have hcon : ∀ e ∈ Store.constraints, e.eval (natRow (rowNat tr 12 r) (tr.row pub 12 r)) = 0 :=
    table_constr H ht hr
  obtain ⟨hb, htot⟩ := store_total H hr
  have hsum1 : ((List.range 7).map fun k => rowNat tr 12 r (Store.fl k)).sum = 1 := by
    have : (Store.act.eval (tr.row pub 12 r)).toNat = 1 := by
      simpa [rowAct, Store.table, Store.inters, stdState, stateIn] using hact
    rwa [store_act_eval tr pub r htot] at this
  obtain ⟨k0, hk0, hone⟩ : ∃ k0, k0 < 7 ∧ ∀ k, k < 7 → rowNat tr 12 r (Store.fl k) = if k = k0 then 1 else 0 := by
    rcases onehot_range _ 7 hb (by omega) with h | h
    · exfalso
      have : ((List.range 7).map fun k => rowNat tr 12 r (Store.fl k)).sum = 0 := by
        have hz : ((List.range 7).map fun k => rowNat tr 12 r (Store.fl k)) = (List.range 7).map fun _ => 0 :=
          List.map_congr_left (fun k hk => h k (List.mem_range.mp hk))
        rw [hz]
        have z : ∀ l : List Nat, (l.map fun _ => 0).sum = 0 := by intro l; induction l <;> simp_all
        exact z _
      omega
    · exact h
  obtain ⟨o, ho⟩ : ∃ o, Store.ops.getD k0 default = o := ⟨_, rfl⟩
  have eF : ∀ p, (Store.sumF p).eval (tr.row pub 12 r) = ((if p o then 1 else 0 : Nat) : F) := fun p => by
    rw [row_eq_natRow, store_sumF _ _ k0 hk0 hone p, ho]
  have nF : ∀ p, ((Store.sumF p).eval (tr.row pub 12 r)).toNat = if p o then 1 else 0 := fun p => by
    rw [eF]; split <;> rfl
  have cA : (Store.act.eval (tr.row pub 12 r)).toNat = 1 := nF _
  have cC : ∀ i, ((Store.cnt i).eval (tr.row pub 12 r)).toNat = if i < o.2.1 then 1 else 0 := fun i => by
    unfold Store.cnt; rw [nF]; simp
  have hw : o.2.1 ≤ 8 ∧ 1 ≤ o.2.1 := by
    have : ∀ k, k < 7 → (Store.ops.getD k default).2.1 ≤ 8 ∧ 1 ≤ (Store.ops.getD k default).2.1 := by decide
    exact ho ▸ this k0 hk0
  have hocc : ∀ i ∈ Store.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 12 r)),
      (i.count.eval (tr.row pub 12 r)).toNat) ∈ occs (wasmBaseAir nloc ncode) tr pub := fun i hi =>
    row_occ ht hr (show i ∈ Store.table.inters from hi)
  have r16of := fun (e cnt : Expr) (hm : r16 e cnt ∈ Store.inters) (hc : (cnt.eval (tr.row pub 12 r)).toNat = 1) =>
    row_r16 L ht hr e cnt (by rw [hT]; exact hm) hc
  have bE0 := r16of (v Store.e) Store.act (by simp [Store.inters]) cA
  have bE1 := r16of (32 * v (Store.e + 1)) Store.act (by simp [Store.inters]) cA
  simp only [v, Expr.eval_mul', Expr.eval_col, Expr.eval_ofNat', Trace.row, Store.e, cell_cast,
    Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _), Nat.reduceAdd] at bE0 bE1
  let eaN := rowNat tr 12 r 32 + 2048 * (((32 : Nat) : F) * ((rowNat tr 12 r 33 : Nat) : F)).toNat
  have hEa : ∀ i, i < 8 → (Store.eaE.eval (tr.row pub 12 r) + ((i : Nat) : F)).toNat = eaN + i := by
    intro i hi
    have e : Store.eaE.eval (tr.row pub 12 r) = ((rowNat tr 12 r 32 : Nat) : F) + ((65536 : Nat) : F) *
        ((rowNat tr 12 r 33 : Nat) : F) := by
      simp only [Store.eaE, v, Expr.eval_add', Expr.eval_mul', Expr.eval_col, Expr.eval_ofNat', Trace.row, Store.e,
        cell_cast]
    have h1 := split27 e (by rw [Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)]; omega) bE1
    rw [Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)] at h1
    rw [← Fp.cast_toNat (Store.eaE.eval (tr.row pub 12 r)), h1, ← Lean.Grind.Semiring.natCast_add,
      Fp.toNat_cast_of_lt (by omega)]
  -- the value bytes are bytes
  have hvb : ∀ i, i < 8 → rowNat tr 12 r (18 + i) < 256 := by
    intro i hi
    have hjb : ∀ j, j < 4 → rowNat tr 12 r (18 + 2 * j) < 256 ∧ rowNat tr 12 r (18 + 2 * j + 1) < 256 := by
      intro j hj
      have h := hocc (byteQ 0 (v (Store.vb + 2 * j)) (v (Store.vb + 2 * j + 1)) 0 Store.act) (by
        simp only [Store.inters, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inr ⟨j, hj, rfl⟩))
      simp only [byteQ] at h
      rw [cA] at h
      obtain ⟨k, x, y, -, hx, hy, he⟩ := L.byte _ h rfl rfl rfl
      simp only [List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', Trace.row, Store.vb, cell_cast,
        List.cons.injEq, and_true] at he
      exact ⟨by rw [natEq he.2.1 (hcP _) (by omega)]; exact hx, by rw [natEq he.2.2.1 (hcP _) (by omega)]; exact hy⟩
    rcases (show ∃ j, j < 4 ∧ (i = 2 * j ∨ i = 2 * j + 1) from ⟨i / 2, by omega, by omega⟩) with ⟨j, hj, rfl | rfl⟩
    · exact (hjb j ‹_›).1
    · rw [← Nat.add_assoc]; exact (hjb j ‹_›).2
  -- messages
  have hIn : rowIn Store.table tr pub 12 r =
      [((rowNat tr 12 r 0 : Nat) : F), ((rowNat tr 12 r 1 : Nat) : F), ((rowNat tr 12 r 2 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 12 r 59 : Nat) : F), ((rowNat tr 12 r 60 : Nat) : F)] := by
    simp only [rowIn, Store.table, Store.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero,
      List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row, Store.kSb, Store.kCid,
      cPc, cTs, cS]
  have hOut : rowOut Store.table tr pub 12 r =
      [((rowNat tr 12 r 0 : Nat) : F) + ((1 : Nat) : F), ((rowNat tr 12 r 1 : Nat) : F) + ((1 : Nat) : F),
        ((rowNat tr 12 r 2 : Nat) : F) + ((rowNat tr 12 r 4 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 12 r 59 : Nat) : F), ((rowNat tr 12 r 60 : Nat) : F)] := by
    simp only [rowOut, Store.table, Store.inters, stdState, stateOut, List.cons_append, List.getD_cons_succ,
      List.getD_cons_zero, List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_add', Expr.eval_ofNat',
      cell_cast, Trace.row, Store.kSb, Store.kCid, cPc, cTs, cS, cFee]
  let mv : Msg := ⟨0, (((rowNat tr 12 r 59 : Nat) : F) + ((rowNat tr 12 r 3 : Nat) : F) - ((1 : Nat) : F)).toNat,
    if o.2.2 then 1 else 0, rowNat tr 12 r 12, rowNat tr 12 r 13, rowNat tr 12 r 14, rowNat tr 12 r 15, rowNat tr 12 r 16⟩
  let ma : Msg := ⟨0, (((rowNat tr 12 r 59 : Nat) : F) + ((rowNat tr 12 r 3 : Nat) : F) - ((2 : Nat) : F)).toNat, 0,
    rowNat tr 12 r 26, rowNat tr 12 r 27, 0, 0, rowNat tr 12 r 28⟩
  have hCons : rowCons Store.table tr pub 12 r =
      mv :: ma :: (List.range o.2.1).map fun i => encB (eaN + i) (rowNat tr 12 r (35 + i)) (rowNat tr 12 r (43 + i)) := by
    have ni : (Store.is64.eval (tr.row pub 12 r)).toNat = if o.2.2 then 1 else 0 := nF _
    rw [rowCons, rowMsgs_eq, store_filterC, List.filterMap_cons, List.filterMap_cons]
    simp only [stkRecv, chRecv, cA, ite_true]
    rw [filterMap_cnt _ _ o.2.1 (fun i => cC i) 8, show min o.2.1 8 = o.2.1 by omega]
    simp only [List.map_cons, List.map_map]
    congr 1
    · simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, decMsg, List.getD_cons_zero,
        List.getD_cons_succ]
      rw [ni]
      simp only [v, Expr.eval_col, Expr.eval_add', Expr.eval_sub', Expr.eval_ofNat', Trace.row, Store.kSb, cH,
        limbsOf, List.range, List.range.loop, Store.vl, Store.tv, Nat.reduceAdd, cell_cast, List.map_cons,
        List.map_nil, List.getD_cons_zero, List.getD_cons_succ, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _), mv]
      rfl
    congr 1
    · simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, v, Expr.eval_col, Expr.eval_add',
        Expr.eval_sub', Expr.eval_ofNat', Trace.row, Store.kSb, cH, Store.a, Store.ta, Nat.reduceAdd, cell_cast,
        decMsg, List.getD_cons_zero, List.getD_cons_succ, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _), ma]
      rfl
    · refine List.map_congr_left fun i hi => ?_
      have hi8 : i < 8 := by rw [List.mem_range] at hi; omega
      simp only [Function.comp, List.map_cons, List.map_nil, List.cons_append, List.nil_append, decMsg,
        List.getD_cons_zero, List.getD_cons_succ, Expr.eval_add', Expr.eval_c]
      rw [hEa i hi8]
      simp only [v, Expr.eval_col, Expr.eval_ofNat', Trace.row, cell_cast, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _),
        encB, Store.ob, Store.tob]
      rfl
  have hProd : rowProd Store.table tr pub 12 r =
      (List.range o.2.1).map fun i => encB (eaN + i) (rowNat tr 12 r (18 + i)) (rowNat tr 12 r 1) := by
    rw [rowProd, rowMsgs_eq, store_filterP, filterMap_cnt _ _ o.2.1 (fun i => cC i) 8,
      show min o.2.1 8 = o.2.1 by omega, List.map_map]
    refine List.map_congr_left fun i hi => ?_
    have hi8 : i < 8 := by rw [List.mem_range] at hi; omega
    simp only [Function.comp, chSend, List.map_cons, List.map_nil, List.cons_append, List.nil_append, decMsg,
      List.getD_cons_zero, List.getD_cons_succ, Expr.eval_add', Expr.eval_c]
    rw [hEa i hi8]
    simp only [v, Expr.eval_col, Expr.eval_ofNat', Trace.row, cell_cast, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _),
      encB, Store.vb, cTs]
    rfl
  -- time checks
  have tchk : ∀ (cnt : Expr) (tpc hic : Nat), (cnt.eval (tr.row pub 12 r)).toNat = 1 →
      r16 (v cTs - v tpc - 1 - B16 * v hic) cnt ∈ Store.inters → r16 (4 * v hic) cnt ∈ Store.inters →
      ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((rowNat tr 12 r tpc + 1 + n : Nat) : F) = ((rowNat tr 12 r 1 : Nat) : F) := by
    intro cnt tpc hic hc m1 m2
    have h1 := hocc _ m1
    have h2 := hocc _ m2
    simp only [r16] at h1 h2
    rw [hc] at h1 h2
    simp only [List.map_cons, List.map_nil, Expr.eval_sub', Expr.eval_mul', v, Expr.eval_col, Expr.eval_ofNat',
      B16, cTs, Trace.row] at h1 h2
    obtain ⟨n, hn, e⟩ := time_chk L h1 h2
    exact ⟨n, hn, e.trans (cell_cast tr 12 r 1)⟩
  have tV := tchk Store.act Store.tv Store.hv cA (by simp [Store.inters, timeChk]) (by simp [Store.inters, timeChk])
  have tA := tchk Store.act Store.ta Store.ha cA (by simp [Store.inters, timeChk]) (by simp [Store.inters, timeChk])
  have tB : ∀ i, i < o.2.1 → ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧
      ((rowNat tr 12 r (43 + i) + 1 + n : Nat) : F) = ((rowNat tr 12 r 1 : Nat) : F) := by
    intro i hi
    have hi8 : i < 8 := by omega
    have hm : ∀ j ∈ timeChk (v cTs) (v (Store.tob + i)) (v (Store.hob + i)) (Store.cnt i), j ∈ Store.inters := by
      intro j hj
      simp only [Store.inters, List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inr ⟨i, hi8, Or.inl (Or.inr hj)⟩
    have := tchk (Store.cnt i) (Store.tob + i) (Store.hob + i) (by rw [cC]; simp [hi])
      (hm _ (by simp [timeChk])) (hm _ (by simp [timeChk]))
    simpa [Store.tob] using this
  -- the FETCH query
  have hfetch := hocc (fetch (v cPc) Store.op (v cH) (v cFee) [v Store.off, v (Store.off + 1), 0, 0] Store.act)
    (by simp [Store.inters, stdState])
  simp only [fetch] at hfetch
  rw [cA] at hfetch
  obtain ⟨pc0, hpc0, hm0⟩ := fetch_pc hpub L hfetch
  obtain ⟨q, l, ins, fee, rec, hq, hl, hoff, hins, hfee, hfl, hrc, hm⟩ := fetch_rec hpub L hfetch hm0 hpc0
  have CF := X.factsOf hq
  obtain ⟨op, x0, x1, x2, x3, hre, hcase⟩ := recordOf_spec hrc
  have hoplt := recordOf_op_lt hrc
  rw [hre] at hm hoplt
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hoplt
  have eOp : Store.op.eval (tr.row pub 12 r) = ((o.1 : Nat) : F) := by
    rw [row_eq_natRow, store_op_eval _ _ k0 hk0 hone, ho]
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm
  rw [eOp] at hm
  simp only [v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row, cPc, cH, cFee, Store.off] at hm
  obtain ⟨e0, eop, eh, efee, ex0, ex1, -, -⟩ := hm
  have fee16 := feeUnits_lt hfee
  have efee' : rowNat tr 12 r 4 = fee := natEq efee (hcP _) (by omega)
  have hopr : 0x36 ≤ o.1 ∧ o.1 ≤ 0x3E ∧ isStoreOp o.1 = true ∧ storeWidth o.1 = o.2.1 := by
    have : ∀ k, k < 7 → 0x36 ≤ (Store.ops.getD k default).1 ∧ (Store.ops.getD k default).1 ≤ 0x3E ∧
        isStoreOp (Store.ops.getD k default).1 = true ∧
        storeWidth (Store.ops.getD k default).1 = (Store.ops.getD k default).2.1 := by decide
    exact ho ▸ this k0 hk0
  have hop : op = o.1 := (natEq eop (by omega) (by omega)).symm
  -- RowFacts
  refine ⟨?_, by rw [hIn]; rfl, by rw [hIn, hOut]; rfl,
    ⟨fee, hfl, by rw [hIn, hOut]; simp only [gasF, List.getD_cons_succ, List.getD_cons_zero, efee']⟩, ?_, ?_, ?_⟩
  rotate_left
  · rw [hCons, hIn]
    intro x hx
    simp only [List.mem_cons, List.mem_map, List.mem_range] at hx
    simp only [lvl, List.getD_cons_succ, List.getD_cons_zero]
    rcases hx with rfl | rfl | ⟨i, hi, rfl⟩
    · exact tV
    · exact tA
    · obtain ⟨n, hn, e⟩ := tB i hi; exact ⟨n, hn, e⟩
  · rw [hProd, hIn]
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    simp only [lvl, List.getD_cons_succ, List.getD_cons_zero]
    obtain ⟨i, _, rfl⟩ := hx
    exact ⟨hcP _, rfl⟩
  · rw [hProd]
    exact List.pairwise_map.mpr ((List.pairwise_lt_range).imp fun h e => by
      have := congrArg Msg.slot e; simp only [encB_slot] at this; omega)
  -- the spec step
  intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
  rw [hIn] at hin
  obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
  have hpcl := R.pcLt
  have hoffb := X.off_bound R.kLt
  have htot := X.mf.total
  have p0 : rowNat tr 12 r 0 = X.offOf E.k + pc := natEq i0 (hcP _) (by omega)
  have p1 : rowNat tr 12 r 1 = t := natEq i1 (hcP _) (by omega)
  have p2 : rowNat tr 12 r 2 = S := natEq i2 (hcP _) (by omega)
  have psb : rowNat tr 12 r 59 = E.sb := natEq i4 (hcP _) (by have := R.sbLt; omega)
  have pcid : rowNat tr 12 r 60 = E.cid := natEq i5 (hcP _) (by have := R.cidLt; omega)
  have hsbR := R.sbLe
  have hpc : pc0 = X.offOf E.k + pc := natEq (e0.symm.trans i0) (by omega) (by omega)
  subst hpc
  obtain ⟨hqk, hlpc⟩ := X.loc_unique hq hl R.kLt hpcl hoff
  subst q
  subst l
  have hH := R.height
  have hHb := CF.hBound pc hpcl
  rw [hH] at eh hHb
  simp only [Option.getD_some] at eh hHb
  have p3 : rowNat tr 12 r 3 = s.stack.size - E.sb := natEq eh (hcP _) (by omega)
  have hszP : s.stack.size < P := by have := R.sbLt; omega
  have hout : rowOut Store.table tr pub 12 r = stMsg (X.offOf E.k + pc + 1) (t + 1) (S + fee) 0 E.sb E.cid := by
    rw [hOut, p0, p1, p2, efee', psb, pcid]
    simp only [stMsg, Lean.Grind.Semiring.natCast_add]
  rw [hCons] at hlive ⊢
  rw [hProd]
  refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfl, by omega, (by rw [hout, Nat.add_assoc]), fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
  obtain ⟨al, off, hinsE, -, hisS, hoff, hxs⟩ : ∃ al off, ins = .store op al off ∧ (0x36 ≤ op ∧ op ≤ 0x3E) ∧
      isStoreOp op = true ∧ off < 2 ^ 32 ∧ [x0, x1, x2, x3] = [off % 65536, off / 65536, 0, 0] := by
    rcases hcase with ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ |
      ⟨_, _, h, _⟩ | ⟨_, hf, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, _, hmem, _⟩ | hl | ⟨_, _, hgl, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, _, h, _⟩
    all_goals first
      | exact hl
      | (exfalso; omega)
      | (exfalso; simp only [isFamilyNum, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hf; omega)
      | (exfalso; simp only [Ctrl.opNext, Ctrl.opJump, Ctrl.opJif, Ctrl.opHalt, Ctrl.opHif] at h; omega)
      | (exfalso; simp only [opCall] at h; omega)
  subst hinsE
  simp only [List.cons.injEq, and_true] at hxs
  obtain ⟨hx0, hx1, -, -⟩ := hxs
  subst hx0 hx1
  have c30 : rowNat tr 12 r 30 = off % 65536 := natEq ex0 (hcP _) (by omega)
  have c31 : rowNat tr 12 r 31 = off / 65536 := natEq ex1 (hcP _) (by omega)
  obtain ⟨ls0, hL0, -⟩ := R.labels
  obtain ⟨h2, -⟩ := verify_straight X R.kLt hpcl hins hL0 R.height (pops := 2) (pushes := 0)
    (by simp [kindOf, hisS, hoff]) (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp)
    (by intro l; simp)
  have hslotV : mv.slot = s.stack.size - 1 := slot_toNat psb p3 hsbR (by omega) hszP
  have hslotA : ma.slot = s.stack.size - 2 := slot_toNat psb p3 hsbR h2 hszP
  have hcy : rowNat tr 12 r 34 = 0 ∨ rowNat tr 12 r 34 = 1 := by
    have := hcon (Chips.bool (v Store.cyE)) (by simp [Store.constraints])
    simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow, Store.cyE] at this
    exact bool_nat (hcP _) this
  have hq0 := hcon (v Store.a + v Store.off - v Store.e - 65536 * v Store.cyE) (by simp [Store.constraints])
  have hq1 := hcon (v (Store.e + 1) - v (Store.a + 1) - v (Store.off + 1) - v Store.cyE) (by simp [Store.constraints])
  simp only [v, Expr.eval_sub', Expr.eval_add', Expr.eval_mul', Expr.eval_col, Expr.eval_ofNat', natRow, Store.a,
    Store.off, Store.e, Store.cyE, Nat.reduceAdd] at hq0 hq1
  have hea : ma.ok → ma.val + off = eaN := by
    intro ok
    obtain ⟨a0, a1, -, -, -⟩ := ok
    simp only [ma] at a0 a1
    have n0 : rowNat tr 12 r 26 + rowNat tr 12 r 30 = rowNat tr 12 r 32 + 65536 * rowNat tr 12 r 34 := by
      have : ((rowNat tr 12 r 26 + rowNat tr 12 r 30 : Nat) : F) =
          ((rowNat tr 12 r 32 + 65536 * rowNat tr 12 r 34 : Nat) : F) := by
        simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]; grind
      exact natEq this (by omega) (by omega)
    have n1 : rowNat tr 12 r 33 = rowNat tr 12 r 27 + rowNat tr 12 r 31 + rowNat tr 12 r 34 := by
      have : ((rowNat tr 12 r 33 : Nat) : F) = ((rowNat tr 12 r 27 + rowNat tr 12 r 31 + rowNat tr 12 r 34 : Nat) : F) := by
        simp only [Lean.Grind.Semiring.natCast_add]; grind
      exact natEq this (hcP _) (by omega)
    have ny : (((32 : Nat) : F) * ((rowNat tr 12 r 33 : Nat) : F)).toNat = 32 * rowNat tr 12 r 33 := by
      rw [← Lean.Grind.Semiring.natCast_mul, Fp.toNat_cast_of_lt (by omega)]
    simp only [eaN, ny, ma, Msg.val, val4]
    omega
  -- the value's bytes
  have hlimb : ∀ j, j < 4 → rowNat tr 12 r (12 + j) = rowNat tr 12 r (18 + 2 * j) + 256 * rowNat tr 12 r (18 + 2 * j + 1) := by
    intro j hj
    have h := hcon (v (Store.vl + j) - v (Store.vb + 2 * j) - 256 * v (Store.vb + 2 * j + 1)) (by
      simp only [Store.constraints, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨j, hj, rfl⟩)
    simp only [v, Expr.eval_sub', Expr.eval_mul', Expr.eval_col, Expr.eval_ofNat', natRow, Store.vl, Store.vb] at h
    have := hvb (2 * j) (by omega); have h' := hvb (2 * j + 1) (by omega)
    rw [← Nat.add_assoc] at h'
    exact natEq (show ((rowNat tr 12 r (12 + j) : Nat) : F) = ((rowNat tr 12 r (18 + 2 * j) +
      256 * rowNat tr 12 r (18 + 2 * j + 1) : Nat) : F) by
        simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]; grind) (hcP _) (by omega)
  have hnb : mv.ok → ∀ i, i < storeWidth op → rowNat tr 12 r (18 + i) = mv.val / 256 ^ i % 256 := by
    intro _ i hi
    have l0 := hlimb 0 (by omega); have l1 := hlimb 1 (by omega); have l2 := hlimb 2 (by omega)
    have l3 := hlimb 3 (by omega)
    simp only [Nat.reduceAdd, Nat.reduceMul] at l0 l1 l2 l3
    have hw' : storeWidth op = o.2.1 := by rw [hop]; exact hopr.2.2.2
    rw [store_bytes (fun i => rowNat tr 12 r (18 + i)) hvb i (by omega)]
    simp only [mv, Msg.val, l0, l1, l2, l3, Nat.reduceAdd]
  have hw' : storeWidth op = o.2.1 := by rw [hop]; exact hopr.2.2.2
  obtain ⟨s', hs', hrel⟩ := step_store X R hins hisS hoff hfee hg hg64 mv ma (hlive mv List.mem_cons_self)
    (hlive ma (List.mem_cons_of_mem _ List.mem_cons_self)) ⟨rfl, hslotV⟩ ⟨rfl, hslotA⟩ eaN hea
    (fun i => rowNat tr 12 r (35 + i)) (fun i => rowNat tr 12 r (43 + i)) (fun i => rowNat tr 12 r (18 + i))
    (fun i hi => hlive _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩)))) hnb
  rw [hw'] at hrel
  refine ⟨s', hs', ?_⟩
  subst p1
  exact hrel

end WasmBase
