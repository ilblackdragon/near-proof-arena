import WasmBase.Main.Rows
import WasmBase.StepOps2
import WasmBase.Local.Cmp
/-!
# Row lemma: CMP (`eqz`, `eq`, `ne`, `lt/gt/le/ge _s/_u`, i32 and i64)
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 8000000 in
/-- The constraint facts of a CMP row used outside `cmp_sound` (flags, the pinning of `ra`, `rb`). -/
theorem cmp_facts (c : Nat → Nat) (rw : Row) (hP : ∀ i, c i < P)
    (hc : ∀ e ∈ Cmp.constraints, e.eval (natRow c rw) = 0) :
    c 5 ≤ 1 ∧ c 6 ≤ 1 ∧ c 7 ≤ 1 ∧ c 8 ≤ 1 ∧ c 9 ≤ 1 ∧ c 10 ≤ 1 ∧ c 11 ≤ 1 ∧ c 12 ≤ 1 ∧ c 13 ≤ 1 ∧
    c 14 ≤ 1 ∧ c 15 ≤ 1 ∧
    c 5 + c 6 + c 7 + c 8 + c 9 + c 10 + c 11 + c 12 + c 13 + c 14 + c 15 ≤ 1 ∧ c 16 ≤ 1 ∧ c 29 ≤ 1 ∧
    c 31 ≤ 1 ∧ (c 5 = 1 → ∀ i, i < 4 → c (23 + i) = 0) ∧
    ((c 30 + 32768 * c 29 : Nat) : F) = ((if c 16 = 1 then c 20 else c 18 : Nat) : F) ∧
    ((c 32 + 32768 * c 31 : Nat) : F) = ((if c 16 = 1 then c 26 else c 24 : Nat) : F) := by
  simp only [Cmp.constraints, Cmp.flags, List.forall_mem_append, List.forall_mem_map, List.forall_mem_flatMap,
    List.mem_range, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, Chips.bool, v,
    Cmp.act, Cmp.limbEq, Cmp.X, Cmp.Y, Cmp.flipX, Cmp.flipY, Cmp.sX, Cmp.sY, Cmp.topInd, Cmp.brIn, Cmp.swap,
    Cmp.signed, Cmp.zsum, Cmp.eqf, Cmp.topA, Cmp.topB, B16, List.foldl, List.map_cons, List.map_nil,
    List.foldl_cons, List.foldl_nil,
    Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, natRow,
    Cmp.fEqz, Cmp.fEq, Cmp.fNe, Cmp.fLtS, Cmp.fLtU, Cmp.fGtS, Cmp.fGtU, Cmp.fLeS, Cmp.fLeU, Cmp.fGeS, Cmp.fGeU,
    Cmp.is64, Cmp.a, Cmp.b, Cmp.sa, Cmp.ra, Cmp.sb, Cmp.rb, Cmp.d, Cmp.br, Cmp.inv, Nat.reduceAdd,
    Nat.reduceSub, ↓reduceIte, Nat.reduceEqDiff, Expr.eval_c] at hc
  obtain ⟨⟨⟨⟨⟨⟨fb0, fb1, fb2, fb3, fb4, fb5, fb6, fb7, fb8, fb9, fb10⟩, bact, b64⟩, hbz⟩, -, -, -, -,
    bsa, bsb, tA, tB⟩, -⟩, -⟩ := hc
  have hP' := P_val
  have f0 := bool_nat (hP _) fb0; have f1 := bool_nat (hP _) fb1; have f2 := bool_nat (hP _) fb2
  have f3 := bool_nat (hP _) fb3; have f4 := bool_nat (hP _) fb4; have f5 := bool_nat (hP _) fb5
  have f6 := bool_nat (hP _) fb6; have f7 := bool_nat (hP _) fb7; have f8 := bool_nat (hP _) fb8
  have f9 := bool_nat (hP _) fb9; have f10 := bool_nat (hP _) fb10
  have w64 := bool_nat (hP _) b64
  have sa' := bool_nat (hP _) bsa
  have sb' := bool_nat (hP _) bsb
  have hs : c 5 + c 6 + c 7 + c 8 + c 9 + c 10 + c 11 + c 12 + c 13 + c 14 + c 15 < P := by omega
  have hact := bool_nat (n := 0 + c 5 + c 6 + c 7 + c 8 + c 9 + c 10 + c 11 + c 12 + c 13 + c 14 + c 15)
    (by omega) (by simpa only [Lean.Grind.Semiring.natCast_add] using bact)
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · intro h1 i hi
    have := hbz i hi
    simp only [h1] at this
    exact (zero_of_mul_nat (x := 1) (by decide) (hP _) this).resolve_left (by decide)
  · rcases w64 with g | g <;> simp only [g] at tA ⊢ <;> simp only [show ¬ (0 = 1) by decide, ite_true, ite_false] <;>
      fp_ring
  · rcases w64 with g | g <;> simp only [g] at tB ⊢ <;> simp only [show ¬ (0 = 1) by decide, ite_true, ite_false] <;>
      fp_ring

/-- `x + 2^15 s ≡ top` with `top < 2^16`, `s` a bit, and `2 x mod p < 2^16` pin `2 x < 2^16`. -/
theorem cmp_pin (x s top : Nat) (hx : x < P) (hs : s ≤ 1) (htop : top < 65536) (hr : (2 * x) % P < 65536)
    (h : ((x + 32768 * s : Nat) : F) = ((top : Nat) : F)) : 2 * x < 65536 := by
  have hP' := P_val
  have e := congrArg Fp.toNat h
  rw [Fp.toNat_cast, Fp.toNat_cast, Nat.mod_eq_of_lt (show top < P by omega)] at e
  rcases (show s = 0 ∨ s = 1 by omega) with g | g <;> subst g
  · rw [Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hx] at e
    subst e
    rw [Nat.mod_eq_of_lt (by omega)] at hr; exact hr
  · by_cases hw : x + 32768 * 1 < P
    · rw [Nat.mod_eq_of_lt hw] at e; rw [Nat.mod_eq_of_lt (by omega)] at hr; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at e
      exfalso
      by_cases ht : 32768 ≤ top
      · omega
      · rw [show 2 * x = (2 * top + P - 65536) + P by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)] at hr
        omega

theorem cmp_count_cases (i : Inter) (hi : i ∈ Cmp.inters) : i.count = Cmp.act ∨ i.count = Cmp.act - v Cmp.fEqz := by
  have := List.all_eq_true.mp
    (show Cmp.inters.all (fun i => decide (i.count = Cmp.act) || decide (i.count = Cmp.act - v Cmp.fEqz)) = true
      by decide) i hi
  simpa using this

theorem cmp_act_eval (pub : List F) (tr : Trace) (r : Nat) :
    (Cmp.act.eval (tr.row pub 5 r)) = ((rowNat tr 5 r 5 + rowNat tr 5 r 6 + rowNat tr 5 r 7 + rowNat tr 5 r 8 +
      rowNat tr 5 r 9 + rowNat tr 5 r 10 + rowNat tr 5 r 11 + rowNat tr 5 r 12 + rowNat tr 5 r 13 +
      rowNat tr 5 r 14 + rowNat tr 5 r 15 : Nat) : F) := by
  simp only [Cmp.act, Cmp.flags, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, v, Expr.eval_add',
    Expr.eval_col, Expr.eval_ofNat', Trace.row, cell_cast, Cmp.fEqz, Cmp.fEq, Cmp.fNe, Cmp.fLtS, Cmp.fLtU,
    Cmp.fGtS, Cmp.fGtU, Cmp.fLeS, Cmp.fLeU, Cmp.fGeS, Cmp.fGeU, Lean.Grind.Semiring.natCast_add]
  rw [show ((0 : Nat) : F) = 0 from rfl]; grind

theorem cmp_flags_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Cmp.table.constraints, e.eval (natRow (rowNat tr 5 r) (tr.row pub 5 r)) = 0) :
    rowNat tr 5 r 5 + rowNat tr 5 r 6 + rowNat tr 5 r 7 + rowNat tr 5 r 8 + rowNat tr 5 r 9 + rowNat tr 5 r 10 +
      rowNat tr 5 r 11 + rowNat tr 5 r 12 + rowNat tr 5 r 13 + rowNat tr 5 r 14 + rowNat tr 5 r 15 ≤ 1 ∧
    rowNat tr 5 r 5 ≤ 1 := by
  have := cmp_facts (rowNat tr 5 r) (tr.row pub 5 r) (rowNat_lt tr 5 r) hcon
  omega

theorem cmp_flags {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 5) :
    rowNat tr 5 r 5 + rowNat tr 5 r 6 + rowNat tr 5 r 7 + rowNat tr 5 r 8 + rowNat tr 5 r 9 + rowNat tr 5 r 10 +
      rowNat tr 5 r 11 + rowNat tr 5 r 12 + rowNat tr 5 r 13 + rowNat tr 5 r 14 + rowNat tr 5 r 15 ≤ 1 ∧
    rowNat tr 5 r 5 ≤ 1 :=
  cmp_flags_of (table_constr H (by simp [air_len]) hr)

theorem cmp_counts_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Cmp.table.constraints, e.eval (natRow (rowNat tr 5 r) (tr.row pub 5 r)) = 0) :
    ∀ i ∈ Cmp.inters, (i.count.eval (tr.row pub 5 r)).toNat ≤ 1 := by
  have hP' := P_val
  obtain ⟨hf, h5⟩ := cmp_flags_of hcon
  intro i hi
  rcases cmp_count_cases i hi with hc | hc <;> rw [hc]
  · rw [cmp_act_eval, Fp.toNat_cast_of_lt (by omega)]; exact hf
  · rw [Expr.eval_sub', cmp_act_eval]
    simp only [v, Expr.eval_col, Trace.row, cell_cast, Cmp.fEqz]
    rw [toNat_cast_sub (by omega) (by omega)]; omega

theorem cmp_counts {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 5) :
    ∀ i ∈ Cmp.inters, (i.count.eval (tr.row pub 5 r)).toNat ≤ 1 :=
  cmp_counts_of (table_constr H (by simp [air_len]) hr)

theorem cmp_inactive {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 5)
    (hna : ¬ rowAct Cmp.table tr pub 5 r) :
    ∀ i ∈ Cmp.inters, (i.count.eval (tr.row pub 5 r)).toNat ≠ 1 := by
  have hP' := P_val
  obtain ⟨hf, h5⟩ := cmp_flags H hr
  have ha : rowNat tr 5 r 5 + rowNat tr 5 r 6 + rowNat tr 5 r 7 + rowNat tr 5 r 8 + rowNat tr 5 r 9 +
      rowNat tr 5 r 10 + rowNat tr 5 r 11 + rowNat tr 5 r 12 + rowNat tr 5 r 13 + rowNat tr 5 r 14 +
      rowNat tr 5 r 15 ≠ 1 := by
    intro h; apply hna
    simp only [rowAct, Cmp.table, Cmp.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero]
    rw [cmp_act_eval, Fp.toNat_cast_of_lt (by omega)]; exact h
  intro i hi
  rcases cmp_count_cases i hi with hc | hc <;> rw [hc]
  · rw [cmp_act_eval, Fp.toNat_cast_of_lt (by omega)]; exact ha
  · rw [Expr.eval_sub', cmp_act_eval]
    simp only [v, Expr.eval_col, Trace.row, cell_cast, Cmp.fEqz]
    rw [toNat_cast_sub (by omega) (by omega)]; omega

theorem cmp_mem (i : Inter) (h : Cmp.inters.any (fun j => decide (j = i)) = true) : i ∈ Cmp.inters := by
  obtain ⟨j, hj, e⟩ := List.any_eq_true.mp h
  rw [← of_decide_eq_true e]; exact hj

theorem cmp_b2_le (b : Bool) : Num.b2 b ≤ 1 := by unfold Num.b2; split <;> omega

theorem cmp_enc_b2 (sl tp : Nat) (b : Bool) :
    enc 0 sl (.i32 (UInt32.ofNat (Num.b2 b))) tp = ⟨0, sl, 0, Num.b2 b, 0, 0, 0, tp⟩ := by
  have h := cmp_b2_le b
  simp only [enc, vTag, vNum, UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (show Num.b2 b < 2 ^ 32 by omega)]
  congr 1 <;> omega

set_option maxHeartbeats 4000000 in
theorem cmp_rowfacts {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hpub : PubOK X nloc ncode pub)
    {r : Nat} (hr : r < tr.height 5) (hact : rowAct Cmp.table tr pub 5 r) :
    RowFacts X (rowIn Cmp.table tr pub 5 r) (rowOut Cmp.table tr pub 5 r)
      (rowCons Cmp.table tr pub 5 r) (rowProd Cmp.table tr pub 5 r) := by
  have hP' := P_val
  have ht : 5 < (wasmBaseAir nloc ncode).tables.length := by simp [air_len]
  have hcP : ∀ i, rowNat tr 5 r i < P := rowNat_lt tr 5 r
  have hcon : ∀ e ∈ Cmp.table.constraints, e.eval (natRow (rowNat tr 5 r) (tr.row pub 5 r)) = 0 :=
    table_constr H ht hr
  obtain ⟨f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, fs, f16, f29, f31, hbz, pinA, pinB⟩ :=
    cmp_facts (rowNat tr 5 r) (tr.row pub 5 r) hcP hcon
  have a1 : rowNat tr 5 r 5 + rowNat tr 5 r 6 + rowNat tr 5 r 7 + rowNat tr 5 r 8 + rowNat tr 5 r 9 +
      rowNat tr 5 r 10 + rowNat tr 5 r 11 + rowNat tr 5 r 12 + rowNat tr 5 r 13 + rowNat tr 5 r 14 +
      rowNat tr 5 r 15 = 1 := by
    have h := hact
    simp only [rowAct, Cmp.table, Cmp.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero] at h
    rwa [cmp_act_eval, Fp.toNat_cast_of_lt (by omega)] at h
  have hocc : ∀ i ∈ Cmp.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 5 r)),
      (i.count.eval (tr.row pub 5 r)).toNat) ∈ occs (wasmBaseAir nloc ncode) tr pub := fun i hi =>
    row_occ ht hr (show i ∈ Cmp.table.inters from hi)
  have cntA : (Expr.eval (tr.row pub 5 r) Cmp.act).toNat = 1 := by
    rw [cmp_act_eval, Fp.toNat_cast_of_lt (by omega)]; exact a1
  have cntB : (Expr.eval (tr.row pub 5 r) (Cmp.act - v Cmp.fEqz)).toNat = 1 - rowNat tr 5 r 5 := by
    rw [Expr.eval_sub', cmp_act_eval]
    simp only [v, Expr.eval_col, Trace.row, cell_cast, Cmp.fEqz]
    rw [toNat_cast_sub (by omega) (by omega)]; omega
  have hIn : rowIn Cmp.table tr pub 5 r =
      [((rowNat tr 5 r 0 : Nat) : F), ((rowNat tr 5 r 1 : Nat) : F), ((rowNat tr 5 r 2 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 5 r 42 : Nat) : F), ((rowNat tr 5 r 43 : Nat) : F)] := by
    simp only [rowIn, Cmp.table, Cmp.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero,
      List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', cell_cast, Trace.row, Cmp.kSb, Cmp.kCid, cPc, cTs, cS]
  have hOut : rowOut Cmp.table tr pub 5 r =
      [((rowNat tr 5 r 0 : Nat) : F) + ((1 : Nat) : F), ((rowNat tr 5 r 1 : Nat) : F) + ((1 : Nat) : F),
        ((rowNat tr 5 r 2 : Nat) : F) + ((rowNat tr 5 r 4 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 5 r 42 : Nat) : F), ((rowNat tr 5 r 43 : Nat) : F)] := by
    simp only [rowOut, Cmp.table, Cmp.inters, stdState, stateOut, List.cons_append, List.getD_cons_succ,
      List.getD_cons_zero, List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_add', Expr.eval_ofNat',
      cell_cast, Trace.row, Cmp.kSb, Cmp.kCid, cPc, cTs, cS, cFee]
  -- the FETCH query
  have hfetch := hocc (fetch (v cPc) Cmp.op (v cH) (v cFee) zeros4 Cmp.act)
    (by simp [Cmp.inters, stdState])
  simp only [fetch, cntA] at hfetch
  obtain ⟨pc0, hpc0, hm0⟩ := fetch_pc hpub L hfetch
  obtain ⟨q, l, ins, fee, rec, hq, hl, hoff, hins, hfee, hfl, hrc, hm⟩ := fetch_rec hpub L hfetch hm0 hpc0
  have CF := X.factsOf hq
  obtain ⟨op, x0, x1, x2, x3, hre, hcase⟩ := recordOf_spec hrc
  have hlt := recordOf_op_lt hrc
  rw [hre] at hm hlt
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hlt
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, zeros4, List.cons.injEq,
    and_true] at hm
  obtain ⟨e0, eop, eh, efee, -, -, -, -⟩ := hm
  simp only [v, Expr.eval_col, Trace.row, cell_cast, cPc, cH, cFee] at e0 eh efee
  have fee16 := feeUnits_lt hfee
  have efee' : rowNat tr 5 r 4 = fee := natEq efee (hcP _) (by omega)
  have hop : op = 0x45 + 11 * rowNat tr 5 r 16 + (1 * rowNat tr 5 r 6 + 2 * rowNat tr 5 r 7 + 3 * rowNat tr 5 r 8 +
      4 * rowNat tr 5 r 9 + 5 * rowNat tr 5 r 10 + 6 * rowNat tr 5 r 11 + 7 * rowNat tr 5 r 12 +
      8 * rowNat tr 5 r 13 + 9 * rowNat tr 5 r 14 + 10 * rowNat tr 5 r 15) := by
    simp only [Cmp.op, Cmp.flags, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
      List.foldl_cons, List.foldl_nil, v, Expr.eval_add', Expr.eval_mul', Expr.eval_col, Expr.eval_c,
      Expr.eval_ofNat', Trace.row, cell_cast, Cmp.is64, Cmp.fEqz, Cmp.fEq, Cmp.fNe, Cmp.fLtS, Cmp.fLtU,
      Cmp.fGtS, Cmp.fGtU, Cmp.fLeS, Cmp.fLeU, Cmp.fGeS, Cmp.fGeU, Nat.reduceAdd] at eop
    simp only [← Lean.Grind.Semiring.natCast_mul, ← Lean.Grind.Semiring.natCast_add] at eop
    have := (natEq eop (by omega) (by omega)).symm
    omega
  -- the time checks
  have tchk : ∀ (tp hi : Nat) (cnt : Expr), (Expr.eval (tr.row pub 5 r) cnt).toNat = 1 →
      (timeChk (v cTs) (v tp) (v hi) cnt).all (fun i => Cmp.inters.any (fun j => decide (j = i))) = true →
      ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((rowNat tr 5 r tp + 1 + n : Nat) : F) = ((rowNat tr 5 r 1 : Nat) : F) := by
    intro tp hi cnt hc hsub'
    have hsub : ∀ i ∈ timeChk (v cTs) (v tp) (v hi) cnt, i ∈ Cmp.inters := fun i hi =>
      cmp_mem i (List.all_eq_true.mp hsub' i hi)
    have o1 := hocc _ (hsub (r16 (v cTs - v tp - 1 - B16 * v hi) cnt) (by simp [timeChk]))
    have o2 := hocc _ (hsub (r16 (4 * v hi) cnt) (by simp [timeChk]))
    simp only [r16] at o1 o2
    rw [hc] at o1 o2
    simp only [List.map_cons, List.map_nil, v, Expr.eval_sub', Expr.eval_mul', Expr.eval_col,
      Expr.eval_ofNat', B16, Trace.row, cTs] at o1 o2
    obtain ⟨n, hn, he⟩ := time_chk L o1 o2
    exact ⟨n, hn, by simp only [cell_cast, Fp.toNat_cast_of_lt (hcP _)] at he; exact he⟩
  have tA := tchk Cmp.ta Cmp.ha Cmp.act cntA (by decide)
  -- range facts from R16 lookups
  have r16c : ∀ e : Expr, r16 e Cmp.act ∈ Cmp.inters → (Expr.eval (tr.row pub 5 r) e).toNat < 65536 := by
    intro e he
    have o := hocc _ he
    simp only [r16, cntA, List.map_cons, List.map_nil] at o
    obtain ⟨x, hx, hxl⟩ := L.r16 _ o rfl rfl rfl
    simp only [List.cons.injEq, and_true] at hx
    rw [hx]; exact hxl
  have hd : ∀ i, i < 4 → rowNat tr 5 r (Cmp.d + i) < 65536 := by
    intro i hi
    have := r16c (v (Cmp.d + i)) (by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> exact cmp_mem _ (by decide))
    simp only [v, Expr.eval_col, Trace.row] at this
    exact this
  have hra : (2 * rowNat tr 5 r 30) % P < 65536 := by
    have := r16c (2 * v Cmp.ra) (cmp_mem _ (by decide))
    simp only [v, Expr.eval_mul', Expr.eval_col, Expr.eval_ofNat', Trace.row, cell_cast, Cmp.ra,
      ← Lean.Grind.Semiring.natCast_mul, Fp.toNat_cast] at this
    exact this
  have hrb : (2 * rowNat tr 5 r 32) % P < 65536 := by
    have := r16c (2 * v Cmp.rb) (cmp_mem _ (by decide))
    simp only [v, Expr.eval_mul', Expr.eval_col, Expr.eval_ofNat', Trace.row, cell_cast, Cmp.rb,
      ← Lean.Grind.Semiring.natCast_mul, Fp.toNat_cast] at this
    exact this
  have fC : (Cmp.table.inters.filter fun i => i.bus = busStk ∧ i.send = false) =
      [stkRecv Cmp.slotA (v Cmp.is64) (limbsOf Cmp.a) (v Cmp.ta) Cmp.act,
       stkRecv (v Cmp.kSb + v cH - 1) (v Cmp.is64) (limbsOf Cmp.b) (v Cmp.tb) (Cmp.act - v Cmp.fEqz)] := by decide
  have fP : (Cmp.table.inters.filter fun i => i.bus = busStk ∧ i.send = true) =
      [stkSend Cmp.slotA 0 [Cmp.res, 0, 0, 0] (v cTs) Cmp.act] := by decide
  have rawCons : rowMsgs Cmp.table tr pub 5 r busStk false =
      ([[((0 : Nat) : F), tr.cell 5 r 42 + tr.cell 5 r 3 - ((2 : Nat) : F) + tr.cell 5 r 5, tr.cell 5 r 16, tr.cell 5 r 17,
          tr.cell 5 r 18, tr.cell 5 r 19, tr.cell 5 r 20, tr.cell 5 r 21]] ++
       (if rowNat tr 5 r 5 = 0 then
        [[((0 : Nat) : F), tr.cell 5 r 42 + tr.cell 5 r 3 - ((1 : Nat) : F), tr.cell 5 r 16, tr.cell 5 r 23, tr.cell 5 r 24,
          tr.cell 5 r 25, tr.cell 5 r 26, tr.cell 5 r 27]] else [])) := by
    rw [rowMsgs_eq, fC]
    simp only [List.filterMap_cons, List.filterMap_nil, stkRecv, chRecv, cntA, cntB, ite_true]
    by_cases h5 : rowNat tr 5 r 5 = 0
    · simp only [h5, show 1 - 0 = 1 from rfl, ite_true, limbsOf, List.range, List.range.loop,
        List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil, v, Expr.eval_sub',
        Expr.eval_add', Expr.eval_col, Expr.eval_ofNat', Trace.row, cH, Cmp.kSb, Cmp.slotA, Cmp.fEqz, Cmp.is64, Cmp.a,
        Cmp.ta, Cmp.b, Cmp.tb, Nat.reduceAdd]
    · have h51 : rowNat tr 5 r 5 = 1 := by omega
      simp only [h51, show ¬ (1 - 1 = 1) by decide, show ¬ ((1 : Nat) = 0) by decide, ite_false, limbsOf,
        List.range, List.range.loop,
        List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil, v, Expr.eval_sub',
        Expr.eval_add', Expr.eval_col, Expr.eval_ofNat', Trace.row, cH, Cmp.kSb, Cmp.slotA, Cmp.fEqz, Cmp.is64, Cmp.a,
        Cmp.ta, Nat.reduceAdd]
  have rawProd : rowMsgs Cmp.table tr pub 5 r busStk true =
      [[((0 : Nat) : F), tr.cell 5 r 42 + tr.cell 5 r 3 - ((2 : Nat) : F) + tr.cell 5 r 5, ((0 : Nat) : F),
        Expr.eval (tr.row pub 5 r) Cmp.res, ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), tr.cell 5 r 1]] := by
    rw [rowMsgs_eq, fP]
    simp only [List.filterMap_cons, List.filterMap_nil, stkSend, chSend, cntA, ite_true]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, v, Expr.eval_sub',
      Expr.eval_add', Expr.eval_col, Expr.eval_ofNat', cH, Cmp.kSb, cTs, Cmp.slotA, Cmp.fEqz]
    rfl
  have z0 : (((0 : Nat) : F)).toNat = 0 := Fp.toNat_cast_of_lt (by omega)
  have hIn1 : lvl (rowIn Cmp.table tr pub 5 r) = ((rowNat tr 5 r 1 : Nat) : F) := by rw [hIn]; rfl
  have hgas : gasF (rowOut Cmp.table tr pub 5 r) = gasF (rowIn Cmp.table tr pub 5 r) + ((fee : Nat) : F) := by
    rw [hIn, hOut]; simp only [gasF, List.getD_cons_succ, List.getD_cons_zero, efee']
  have hts : lvl (rowOut Cmp.table tr pub 5 r) = lvl (rowIn Cmp.table tr pub 5 r) + 1 := by
    rw [hIn, hOut]; rfl
  have hProd : rowProd Cmp.table tr pub 5 r =
      [⟨0, (tr.cell 5 r 42 + tr.cell 5 r 3 - ((2 : Nat) : F) + tr.cell 5 r 5).toNat, 0,
        (Expr.eval (tr.row pub 5 r) Cmp.res).toNat, 0, 0, 0, rowNat tr 5 r 1⟩] := by
    rw [rowProd, rawProd]
    simp only [List.map_cons, List.map_nil, decMsg, List.getD_cons_zero, List.getD_cons_succ, z0]
    rfl
  have hprodT : ∀ x ∈ rowProd Cmp.table tr pub 5 r, x.tp < P ∧ ((x.tp : Nat) : F) = lvl (rowIn Cmp.table tr pub 5 r) := by
    intro x hx
    rw [hProd] at hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst hx
    exact ⟨hcP 1, by rw [hIn1]⟩
  have hprodNd : (rowProd Cmp.table tr pub 5 r).Nodup := by rw [hProd]; simp
  have spec_pre : ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop)
      (S_seg segb : Nat),
      RelW X E s f tps tpl t pc S live S_seg segb → rowIn Cmp.table tr pub 5 r = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
      t + 1 < P → S + X.maxFee < P → q = E.k ∧ l = pc ∧ pc0 = X.offOf E.k + pc ∧ rowNat tr 5 r 1 = t ∧
        (1 ≤ s.stack.size - E.sb → (tr.cell 5 r 42 + tr.cell 5 r 3 - ((1 : Nat) : F)).toNat = s.stack.size - 1) ∧
        (2 ≤ s.stack.size - E.sb + rowNat tr 5 r 5 →
          (tr.cell 5 r 42 + tr.cell 5 r 3 - ((2 : Nat) : F) + tr.cell 5 r 5).toNat = s.stack.size + rowNat tr 5 r 5 - 2) ∧
        rowOut Cmp.table tr pub 5 r = stMsg (X.offOf E.k + (pc + 1)) (t + 1) (S + fee) 0 E.sb E.cid := by
    intro E s f tps tpl t pc S live S_seg segb R hin ht1 hS
    rw [hIn] at hin
    obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
    have hpcl := R.pcLt
    have hoffb := X.off_bound R.kLt
    have htot := X.mf.total
    obtain ⟨ls0, hL0, hfl0⟩ := R.labels
    have p0 : rowNat tr 5 r 0 = X.offOf E.k + pc := natEq i0 (hcP _) (by omega)
    have p1 : rowNat tr 5 r 1 = t := natEq i1 (hcP _) (by omega)
    have p2 : rowNat tr 5 r 2 = S := natEq i2 (hcP _) (by omega)
    have psb : rowNat tr 5 r 42 = E.sb := natEq i4 (hcP _) (by have := R.sbLt; omega)
    have pcid : rowNat tr 5 r 43 = E.cid := natEq i5 (hcP _) (by have := R.cidLt; omega)
    have hsbR := R.sbLe
    have hpc : pc0 = X.offOf E.k + pc := natEq (e0.symm.trans i0) (by omega) (by omega)
    subst hpc
    obtain ⟨hqk, hlpc⟩ := X.loc_unique hq hl R.kLt hpcl hoff
    subst q
    subst l
    have hH := R.height
    have hHb := CF.hBound pc hpcl
    have eh' := eh
    rw [hH] at eh' hHb
    simp only [Option.getD_some] at eh' hHb
    have p3 : rowNat tr 5 r 3 = s.stack.size - E.sb := natEq eh' (hcP _) (by omega)
    have hszP : s.stack.size + 2 < P := by have := R.sbLt; omega
    refine ⟨rfl, rfl, rfl, p1, fun hk => by rw [cell_cast, cell_cast]; exact slot_toNat psb p3 hsbR hk (by omega), fun hk => ?_, ?_⟩
    · rw [cell_cast, cell_cast, cell_cast, psb, p3]
      have : ((E.sb : Nat) : F) + ((s.stack.size - E.sb : Nat) : F) - ((2 : Nat) : F) + ((rowNat tr 5 r 5 : Nat) : F) =
          ((s.stack.size + rowNat tr 5 r 5 - 2 : Nat) : F) := by
        have e2 : ((s.stack.size + rowNat tr 5 r 5 - 2 : Nat) : F) + ((2 : Nat) : F) =
            ((E.sb : Nat) : F) + ((s.stack.size - E.sb : Nat) : F) + ((rowNat tr 5 r 5 : Nat) : F) := by
          rw [← Lean.Grind.Semiring.natCast_add, ← Lean.Grind.Semiring.natCast_add, ← Lean.Grind.Semiring.natCast_add]
          congr 1; omega
        grind
      rw [this, Fp.toNat_cast_of_lt (by omega)]
    rw [hOut, p0, p1, p2, efee', psb, pcid, ← Nat.add_assoc]
    simp only [stMsg, Lean.Grind.Semiring.natCast_add]
  have hres : ∀ hA : (∀ i, i < 4 → rowNat tr 5 r (Cmp.a + i) < 65536),
      ∀ hB : (∀ i, i < 4 → rowNat tr 5 r (Cmp.b + i) < 65536),
      (Expr.eval (tr.row pub 5 r) Cmp.res).toNat =
        Num.b2 (cmpSpec (1 * rowNat tr 5 r 6 + 2 * rowNat tr 5 r 7 + 3 * rowNat tr 5 r 8 + 4 * rowNat tr 5 r 9 +
          5 * rowNat tr 5 r 10 + 6 * rowNat tr 5 r 11 + 7 * rowNat tr 5 r 12 + 8 * rowNat tr 5 r 13 +
          9 * rowNat tr 5 r 14 + 10 * rowNat tr 5 r 15) (32 + 32 * rowNat tr 5 r 16)
          (val4 (rowNat tr 5 r 17) (rowNat tr 5 r 18) (rowNat tr 5 r 19) (rowNat tr 5 r 20))
          (val4 (rowNat tr 5 r 23) (rowNat tr 5 r 24) (rowNat tr 5 r 25) (rowNat tr 5 r 26))) := by
    intro hA hB
    have pa : 2 * rowNat tr 5 r 30 < 65536 := by
      refine cmp_pin _ _ _ (hcP _) f29 ?_ hra pinA
      have := hA 1 (by decide); have := hA 3 (by decide)
      simp only [Cmp.a, Nat.reduceAdd] at *
      split <;> omega
    have pb : 2 * rowNat tr 5 r 32 < 65536 := by
      refine cmp_pin _ _ _ (hcP _) f31 ?_ hrb pinB
      have := hB 1 (by decide); have := hB 3 (by decide)
      simp only [Cmp.b, Nat.reduceAdd] at *
      split <;> omega
    obtain ⟨-, -, -, e⟩ := cmp_sound (rowNat tr 5 r) (tr.row pub 5 r) hcP hcon a1 hA hB hd pa pb
    simp only [Cmp.a, Cmp.b, Cmp.is64, Nat.reduceAdd] at e
    rw [row_eq_natRow, e, Fp.toNat_cast_of_lt (by have := cmp_b2_le (cmpSpec (1 * rowNat tr 5 r 6 + 2 * rowNat tr 5 r 7 + 3 * rowNat tr 5 r 8 + 4 * rowNat tr 5 r 9 +
          5 * rowNat tr 5 r 10 + 6 * rowNat tr 5 r 11 + 7 * rowNat tr 5 r 12 + 8 * rowNat tr 5 r 13 +
          9 * rowNat tr 5 r 14 + 10 * rowNat tr 5 r 15) (32 + 32 * rowNat tr 5 r 16)
          (val4 (rowNat tr 5 r 17) (rowNat tr 5 r 18) (rowNat tr 5 r 19) (rowNat tr 5 r 20))
          (val4 (rowNat tr 5 r 23) (rowNat tr 5 r 24) (rowNat tr 5 r 25) (rowNat tr 5 r 26))); omega)]
  have hnum : ins = .num op := by
    rcases hcase with ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ |
      ⟨_, _, h, _⟩ | ⟨h1, _, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, _, h, _⟩
    all_goals first
      | (exfalso; simp only [isBinop, binops, List.mem_cons, List.mem_nil_iff, or_false] at hop; omega)
      | (exfalso; omega)
      | exact h1
      | (exfalso; simp only [Ctrl.opNext, Ctrl.opJump, Ctrl.opJif, Ctrl.opHalt, Ctrl.opHif] at h; omega)
      | (exfalso; simp only [opCall] at h; omega)
  subst hnum
  have hidx : 1 * rowNat tr 5 r 6 + 2 * rowNat tr 5 r 7 + 3 * rowNat tr 5 r 8 + 4 * rowNat tr 5 r 9 +
      5 * rowNat tr 5 r 10 + 6 * rowNat tr 5 r 11 + 7 * rowNat tr 5 r 12 + 8 * rowNat tr 5 r 13 +
      9 * rowNat tr 5 r 14 + 10 * rowNat tr 5 r 15 ≤ 10 := by omega
  have hA_of : ∀ m : Msg, m.ok → m.l0 = rowNat tr 5 r 17 → m.l1 = rowNat tr 5 r 18 → m.l2 = rowNat tr 5 r 19 →
      m.l3 = rowNat tr 5 r 20 → ∀ i, i < 4 → rowNat tr 5 r (Cmp.a + i) < 65536 := by
    intro m ok h0 h1 h2 h3 i hi
    obtain ⟨l0, l1, l2, l3, -⟩ := ok
    simp only [Cmp.a]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> simp only [Nat.reduceAdd] <;>
      omega
  rcases (show rowNat tr 5 r 5 = 1 ∨ rowNat tr 5 r 5 = 0 by omega) with g5 | g5
  · -- eqz
    have hCons : rowCons Cmp.table tr pub 5 r =
        [⟨0, (tr.cell 5 r 42 + tr.cell 5 r 3 - ((2 : Nat) : F) + tr.cell 5 r 5).toNat, rowNat tr 5 r 16, rowNat tr 5 r 17,
          rowNat tr 5 r 18, rowNat tr 5 r 19, rowNat tr 5 r 20, rowNat tr 5 r 21⟩] := by
      rw [rowCons, rawCons, if_neg (by omega : ¬ rowNat tr 5 r 5 = 0)]
      simp only [List.append_nil, List.map_cons, List.map_nil, decMsg, List.getD_cons_zero, List.getD_cons_succ, z0]
      rfl
    refine ⟨?_, by rw [hIn]; rfl, hts, ⟨fee, hfl, hgas⟩, ?_, hprodT, hprodNd⟩
    rotate_left
    · rw [hCons, hIn1]
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact tA
    intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
    obtain ⟨hqk, hlpc, hpc, p1, slot1, slotA, hout⟩ := spec_pre E s f tps tpl t pc S live S_seg segb R hin ht1 hS
    subst q
    subst l
    obtain ⟨ls0, hL0, -⟩ := R.labels
    subst hpc
    have hidx0 : 1 * rowNat tr 5 r 6 + 2 * rowNat tr 5 r 7 + 3 * rowNat tr 5 r 8 + 4 * rowNat tr 5 r 9 +
      5 * rowNat tr 5 r 10 + 6 * rowNat tr 5 r 11 + 7 * rowNat tr 5 r 12 + 8 * rowNat tr 5 r 13 +
      9 * rowNat tr 5 r 14 + 10 * rowNat tr 5 r 15 = 0 := by omega
    rw [hidx0] at hop
    have hop' : op = 0x45 ∨ op = 0x50 := by omega
    have hfam : isFamilyNum op = true ∧ numPops op = 1 := by rcases hop' with rfl | rfl <;> decide
    obtain ⟨h1, -, -, -⟩ := verify_straight X R.kLt R.pcLt hins hL0 R.height (pops := 1) (pushes := 1)
      (by simp [kindOf, hfam.1, hfam.2]) (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp)
      (by intro l; simp)
    rw [hCons, hProd] at *
    have hma := hlive _ (List.mem_singleton_self _)
    have sl := slotA (by omega)
    rw [g5] at sl
    refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfl, by omega, hout, fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
    refine step_eqz X R hins hop' hfee hg hg64 _ _ hma ⟨rfl, by simp only [sl]; omega⟩ ?_
    intro r' hr'
    obtain ⟨-, oka, -, -⟩ := R.stack_dec hma (i := s.stack.size - 1) rfl (by simp only [sl]; omega) (by omega)
    have hB : ∀ i, i < 4 → rowNat tr 5 r (Cmp.b + i) < 65536 := fun i hi => by
      simp only [Cmp.b]; rw [hbz g5 i hi]; omega
    have hr := hres (hA_of _ oka rfl rfl rfl rfl) hB
    have e := hr' oka
    rw [hr, hidx0, e, cmp_enc_b2, sl, p1]
    simp only [cmpSpec, ite_true, Msg.val]
    rw [show s.stack.size + 1 - 2 = s.stack.size - 1 by omega]
    rfl
  · -- a relational operator
    have cB1 : (Expr.eval (tr.row pub 5 r) (Cmp.act - v Cmp.fEqz)).toNat = 1 := by rw [cntB, g5]
    have tB := tchk Cmp.tb Cmp.hb (Cmp.act - v Cmp.fEqz) cB1 (by decide)
    have hCons : rowCons Cmp.table tr pub 5 r =
        [⟨0, (tr.cell 5 r 42 + tr.cell 5 r 3 - ((2 : Nat) : F) + tr.cell 5 r 5).toNat, rowNat tr 5 r 16, rowNat tr 5 r 17,
          rowNat tr 5 r 18, rowNat tr 5 r 19, rowNat tr 5 r 20, rowNat tr 5 r 21⟩,
         ⟨0, (tr.cell 5 r 42 + tr.cell 5 r 3 - ((1 : Nat) : F)).toNat, rowNat tr 5 r 16, rowNat tr 5 r 23,
          rowNat tr 5 r 24, rowNat tr 5 r 25, rowNat tr 5 r 26, rowNat tr 5 r 27⟩] := by
      rw [rowCons, rawCons, if_pos g5]
      simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, decMsg, List.getD_cons_zero,
        List.getD_cons_succ, z0]
      rfl
    refine ⟨?_, by rw [hIn]; rfl, hts, ⟨fee, hfl, hgas⟩, ?_, hprodT, hprodNd⟩
    rotate_left
    · rw [hCons, hIn1]
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨tA, tB⟩
    intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
    obtain ⟨hqk, hlpc, hpc, p1, slot1, slotA, hout⟩ := spec_pre E s f tps tpl t pc S live S_seg segb R hin ht1 hS
    subst q
    subst l
    obtain ⟨ls0, hL0, -⟩ := R.labels
    subst hpc
    have hrel : op ∈ relops := by
      simp only [relops, List.mem_cons, List.mem_nil_iff, or_false]; omega
    have hfam : isFamilyNum op = true ∧ numPops op = 2 := by
      simp only [relops, List.mem_cons, List.mem_nil_iff, or_false] at hrel
      rcases hrel with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst h <;> decide
    obtain ⟨h2, -, -, -⟩ := verify_straight X R.kLt R.pcLt hins hL0 R.height (pops := 2) (pushes := 1)
      (by simp [kindOf, hfam.1, hfam.2]) (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp)
      (by intro l; simp)
    rw [hCons, hProd] at *
    have hma := hlive _ List.mem_cons_self
    have hmb := hlive _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have sl := slotA (by omega)
    rw [g5] at sl
    have sl1 := slot1 (by omega)
    refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfl, by omega, hout, fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
    refine step_relop X R hins hrel hfee hg hg64 _ _ _ hma hmb ⟨rfl, by simp only [sl]; omega⟩
      ⟨rfl, sl1⟩ ?_ trivial
    intro r' hr'
    obtain ⟨-, oka, -, -⟩ := R.stack_dec hma (i := s.stack.size - 2) rfl (by simp only [sl]; omega) (by omega)
    obtain ⟨-, okb, -, -⟩ := R.stack_dec hmb rfl sl1 (by omega)
    have hB : ∀ i, i < 4 → rowNat tr 5 r (Cmp.b + i) < 65536 := by
      obtain ⟨l0, l1, l2, l3, -⟩ := okb
      intro i hi
      simp only [Cmp.b]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> simp only [Nat.reduceAdd] <;>
        omega
    have hr := hres (hA_of _ oka rfl rfl rfl rfl) hB
    have e := hr' oka okb
    have hW : relW op = 32 + 32 * rowNat tr 5 r 16 := by
      unfold relW; split <;> omega
    have hK : relK op = (1 * rowNat tr 5 r 6 + 2 * rowNat tr 5 r 7 + 3 * rowNat tr 5 r 8 + 4 * rowNat tr 5 r 9 +
      5 * rowNat tr 5 r 10 + 6 * rowNat tr 5 r 11 + 7 * rowNat tr 5 r 12 + 8 * rowNat tr 5 r 13 +
      9 * rowNat tr 5 r 14 + 10 * rowNat tr 5 r 15) - 1 := by
      unfold relK; split <;> omega
    have hi1 : (1 * rowNat tr 5 r 6 + 2 * rowNat tr 5 r 7 + 3 * rowNat tr 5 r 8 + 4 * rowNat tr 5 r 9 +
      5 * rowNat tr 5 r 10 + 6 * rowNat tr 5 r 11 + 7 * rowNat tr 5 r 12 + 8 * rowNat tr 5 r 13 +
      9 * rowNat tr 5 r 14 + 10 * rowNat tr 5 r 15) ≠ 0 := by omega
    rw [hr, e, cmp_enc_b2, sl, p1, hW, hK]
    simp only [cmpSpec, hi1, ite_false, Msg.val]
    rw [show s.stack.size + 0 - 2 = s.stack.size - 2 by omega]

end WasmBase
