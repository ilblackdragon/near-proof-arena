import WasmBase.Main.Rows
import WasmBase.Main.RowMul
import WasmBase.StepOps
import WasmBase.Local.Shift
/-!
# Row lemma: SHIFT (`i32/i64.shl`, `shr_s`, `shr_u`, `rotl`, `rotr`)
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

theorem shift_rbyte_eval (c : Nat → Nat) (rw : Row) (h10 : c 10 ≤ 1) (j : Nat) :
    (Shift.rbyte j).eval (natRow c rw) = ((shiftR c j : Nat) : F) := by
  rcases (show c 10 = 0 ∨ c 10 = 1 by omega) with h | h <;>
  · unfold Shift.rbyte shiftR
    by_cases hj : j < 4
    · simp only [hj, ite_true, Shift.flo, Shift.fhi, v, Expr.eval_add', Expr.eval_mul', Expr.eval_sub',
        Expr.eval_col, Expr.eval_ofNat', natRow, Shift.is64, Shift.P, Shift.fShl, Shift.fShrS, Shift.fShrU,
        Shift.fRotl, Shift.fRotr, h]
      first | fp_ring | simp only [Lean.Grind.Semiring.natCast_mul, Lean.Grind.Semiring.natCast_add]
    · simp only [hj, ite_false, Shift.flo, Shift.fhi, v, Expr.eval_add', Expr.eval_mul', Expr.eval_sub',
        Expr.eval_col, Expr.eval_ofNat', natRow, Shift.is64, Shift.P, Shift.fShl, Shift.fShrS, Shift.fShrU,
        Shift.fRotl, Shift.fRotr, h]
      first | fp_ring | simp only [Lean.Grind.Semiring.natCast_mul, Lean.Grind.Semiring.natCast_add]


theorem shift_rowfacts {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hpub : PubOK X nloc ncode pub)
    {r : Nat} (hr : r < tr.height 4) (hact : rowAct Shift.table tr pub 4 r) :
    RowFacts X (rowIn Shift.table tr pub 4 r) (rowOut Shift.table tr pub 4 r)
      (rowCons Shift.table tr pub 4 r) (rowProd Shift.table tr pub 4 r) := by
  have hP' := P_val
  have ht : 4 < (wasmBaseAir nloc ncode).tables.length := by simp [air_len]
  have hcP : ∀ i, rowNat tr 4 r i < P := rowNat_lt tr 4 r
  have hcon : ∀ e ∈ Shift.table.constraints, e.eval (natRow (rowNat tr 4 r) (tr.row pub 4 r)) = 0 :=
    table_constr H ht hr
  have hev : ∀ i, Expr.eval (tr.row pub 4 r) (v i) = ((rowNat tr 4 r i : Nat) : F) := fun i => by
    simp only [v, Expr.eval_col, Trace.row, cell_cast]
  -- flags
  have bitOf : ∀ i, (Chips.bool (v i)) ∈ Shift.constraints → rowNat tr 4 r i ≤ 1 := by
    intro i hi
    have h := hcon _ hi
    simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow] at h
    rcases bool_nat (hcP i) h with h | h <;> omega
  have f0 := bitOf 5 (by simp [Shift.constraints, Shift.fShl])
  have f1 := bitOf 6 (by simp [Shift.constraints, Shift.fShrS])
  have f2 := bitOf 7 (by simp [Shift.constraints, Shift.fShrU])
  have f3 := bitOf 8 (by simp [Shift.constraints, Shift.fRotl])
  have f4 := bitOf 9 (by simp [Shift.constraints, Shift.fRotr])
  have w1 := bitOf 10 (by simp [Shift.constraints, Shift.is64])
  have cnt : (Expr.eval (tr.row pub 4 r) Shift.act).toNat = 1 := hact
  have a1 : rowNat tr 4 r 5 + rowNat tr 4 r 6 + rowNat tr 4 r 7 + rowNat tr 4 r 8 + rowNat tr 4 r 9 = 1 := by
    have e : Expr.eval (tr.row pub 4 r) Shift.act =
        ((rowNat tr 4 r 5 + rowNat tr 4 r 6 + rowNat tr 4 r 7 + rowNat tr 4 r 8 + rowNat tr 4 r 9 : Nat) : F) := by
      simp only [Shift.act, Shift.left, Shift.right, Expr.eval_add', hev, Shift.fShl, Shift.fShrS, Shift.fShrU,
        Shift.fRotl, Shift.fRotr]
      simp only [Lean.Grind.Semiring.natCast_add]; grind
    rw [e, Fp.toNat_cast_of_lt (by omega)] at cnt; exact cnt
  have hocc : ∀ i ∈ Shift.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 4 r)), 1) ∈
      occs (wasmBaseAir nloc ncode) tr pub := by
    intro i hi
    have hc : i.count = Shift.act :=
      of_decide_eq_true (List.all_eq_true.mp
        (show Shift.inters.all (fun i => decide (i.count = Shift.act)) = true by decide) i hi)
    have := row_occ (pub := pub) ht hr (show i ∈ Shift.table.inters from hi)
    rwa [hc, cnt] at this
  -- byte and range lookups
  have pairs : ∀ base n, (∀ i, i < n → byteQ 0 (v (base + 2 * i)) (v (base + 2 * i + 1)) 0 Shift.act ∈ Shift.inters) →
      ∀ k, k < 2 * n → rowNat tr 4 r (base + k) < 256 := by
    intro base n hm k hk
    have key : ∀ i, i < n → rowNat tr 4 r (base + 2 * i) < 256 ∧ rowNat tr 4 r (base + 2 * i + 1) < 256 := by
      intro i hi
      have := hocc _ (hm i hi)
      simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at this
      exact mul_pair L (hcP _) (hcP _) this
    rcases (show ∃ i, i < n ∧ (k = 2 * i ∨ k = 2 * i + 1) from ⟨k / 2, by omega, by omega⟩) with ⟨i, hi, rfl | rfl⟩
    · exact (key i hi).1
    · rw [← Nat.add_assoc]; exact (key i hi).2
  have hab := pairs Shift.ab 4 (fun i hi => by
    simp only [Shift.inters, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩)))
  have hPb := pairs Shift.P 8 (fun i hi => by
    simp only [Shift.inters, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inr ⟨i, hi, rfl⟩))
  have hcy := pairs Shift.cy 8 (fun i hi => by
    simp only [Shift.inters, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inr ⟨i, hi, rfl⟩)
  simp only [Shift.ab, Shift.P, Shift.cy, Nat.reduceMul] at hab hPb hcy
  have hq : rowNat tr 4 r 33 < 65536 := by
    have := hocc (r16 (v Shift.q) Shift.act) (by simp [Shift.inters])
    simp only [r16, List.map_cons, List.map_nil, hev, Shift.q] at this
    exact mul_r16 L (hcP _) this
  have hrest : (2 * rowNat tr 4 r 47) % P < 256 := by
    have := hocc (byteQ 0 (2 * v Shift.rest) 0 0 Shift.act) (by simp [Shift.inters])
    simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_mul', Expr.eval_ofNat', Shift.rest] at this
    obtain ⟨k, x, y, -, hx, -, hm⟩ := L.byte _ this rfl rfl rfl
    simp only [List.cons.injEq, and_true] at hm
    obtain ⟨-, e1, -, -⟩ := hm
    rw [← Lean.Grind.Semiring.natCast_mul] at e1
    have := congrArg Fp.toNat e1
    rw [Fp.toNat_cast, Fp.toNat_cast_of_lt (by omega)] at this
    omega
  -- the row's messages
  have hIn : rowIn Shift.table tr pub 4 r =
      [((rowNat tr 4 r 0 : Nat) : F), ((rowNat tr 4 r 1 : Nat) : F), ((rowNat tr 4 r 2 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 4 r 80 : Nat) : F), ((rowNat tr 4 r 81 : Nat) : F)] := by
    simp only [rowIn, Shift.table, Shift.inters, stdState, stateIn, List.cons_append, List.append_assoc,
      List.getD_cons_zero, List.map_cons, List.map_nil, hev, Expr.eval_ofNat', cPc, cTs, cS, Shift.kSb, Shift.kCid]
  have hOut : rowOut Shift.table tr pub 4 r =
      [((rowNat tr 4 r 0 : Nat) : F) + ((1 : Nat) : F), ((rowNat tr 4 r 1 : Nat) : F) + ((1 : Nat) : F),
        ((rowNat tr 4 r 2 : Nat) : F) + ((rowNat tr 4 r 4 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 4 r 80 : Nat) : F), ((rowNat tr 4 r 81 : Nat) : F)] := by
    simp only [rowOut, Shift.table, Shift.inters, stdState, stateOut, List.cons_append, List.append_assoc,
      List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil, hev, Expr.eval_add', Expr.eval_ofNat',
      cPc, cTs, cS, cFee, Shift.kSb, Shift.kCid]
  have tn : ∀ x : Nat, x < 65536 → (((x : Nat) : F)).toNat = x := fun x hx => Fp.toNat_cast_of_lt (by omega)
  have la : ∀ i, i < 4 → rowNat tr 4 r (11 + 2 * i) + 256 * rowNat tr 4 r (11 + 2 * i + 1) < 65536 := by
    intro i hi
    have := hab (2 * i) (by omega); have := hab (2 * i + 1) (by omega)
    rw [← Nat.add_assoc] at *; omega
  have filt : ∀ (b : Nat) (sd : Bool), rowMsgs Shift.table tr pub 4 r b sd =
      (Shift.inters.filter fun i => i.bus = b ∧ i.send = sd).map fun i => i.msg.map (·.eval (tr.row pub 4 r)) := by
    intro b sd
    rw [rowMsgs_eq]
    have : ∀ l : List Inter, (∀ i ∈ l, i.count = Shift.act) →
        l.filterMap (fun i => if (i.count.eval (tr.row pub 4 r)).toNat = 1 then some (i.msg.map (·.eval (tr.row pub 4 r))) else none) =
        l.map fun i => i.msg.map (·.eval (tr.row pub 4 r)) := by
      intro l hl
      induction l with
      | nil => rfl
      | cons i l ih =>
        rw [List.filterMap_cons, List.map_cons, hl i (by simp), cnt]
        simp only [ite_true]
        rw [ih (fun j hj => hl j (by simp [hj]))]
    apply this
    intro i hi
    exact of_decide_eq_true (List.all_eq_true.mp
      (show Shift.inters.all (fun i => decide (i.count = Shift.act)) = true by decide) i (List.mem_filter.mp hi).1)
  have hCons : rowCons Shift.table tr pub 4 r =
      [⟨0, (((rowNat tr 4 r 80 : Nat) : F) + ((rowNat tr 4 r 3 : Nat) : F) - ((2 : Nat) : F)).toNat, rowNat tr 4 r 10,
        rowNat tr 4 r (11 + 2 * 0) + 256 * rowNat tr 4 r (11 + 2 * 0 + 1),
        rowNat tr 4 r (11 + 2 * 1) + 256 * rowNat tr 4 r (11 + 2 * 1 + 1),
        rowNat tr 4 r (11 + 2 * 2) + 256 * rowNat tr 4 r (11 + 2 * 2 + 1),
        rowNat tr 4 r (11 + 2 * 3) + 256 * rowNat tr 4 r (11 + 2 * 3 + 1), rowNat tr 4 r 19⟩,
       ⟨0, (((rowNat tr 4 r 80 : Nat) : F) + ((rowNat tr 4 r 3 : Nat) : F) - ((1 : Nat) : F)).toNat, rowNat tr 4 r 10,
        rowNat tr 4 r 21, rowNat tr 4 r 22, rowNat tr 4 r 23, rowNat tr 4 r 24, rowNat tr 4 r 25⟩] := by
    rw [rowCons, filt]
    have a0 := la 0 (by decide); have a1' := la 1 (by decide); have a2 := la 2 (by decide); have a3 := la 3 (by decide)
    simp only [Nat.reduceAdd, Nat.reduceMul] at a0 a1' a2 a3
    simp [Shift.table, Shift.inters, stdState, stateIn, stateOut, fetch, stkSend, stkRecv, chSend, chRecv, timeChk,
      r16, byteQ, busState, busFetch, busStk, busR16, busByte, List.range, List.range.loop, limbsB, limbB, limbsOf,
      hev, cH, Shift.kSb, Shift.is64, Shift.ab, Shift.b, Shift.ta, Shift.tb, mul_limb_cast, decMsg, tn _ a0, tn _ a1',
      tn _ a2, tn _ a3, Fp.toNat_cast_of_lt (hcP _)]
    rfl
  have hrb : ∀ j, (Shift.rbyte j).eval (tr.row pub 4 r) = ((shiftR (rowNat tr 4 r) j : Nat) : F) := by
    intro j; rw [row_eq_natRow]; exact shift_rbyte_eval _ _ w1 j
  let Rr : Nat → Nat := fun i =>
    (((shiftR (rowNat tr 4 r) (2 * i) + 256 * shiftR (rowNat tr 4 r) (2 * i + 1) : Nat) : F)).toNat
  have hProd : rowProd Shift.table tr pub 4 r =
      [⟨0, (((rowNat tr 4 r 80 : Nat) : F) + ((rowNat tr 4 r 3 : Nat) : F) - ((2 : Nat) : F)).toNat, rowNat tr 4 r 10, Rr 0, Rr 1, Rr 2, Rr 3,
        rowNat tr 4 r 1⟩] := by
    rw [rowProd, filt]
    simp [Shift.table, Shift.inters, stdState, stateIn, stateOut, fetch, stkSend, stkRecv, chSend, chRecv, timeChk,
      r16, byteQ, busState, busFetch, busStk, busR16, busByte, List.range, List.range.loop, Shift.rlimb, hrb,
      hev, cH, Shift.kSb, cTs, Shift.is64, mul_limb_cast, decMsg, Fp.toNat_cast_of_lt (hcP _), Rr]
    rfl
  have hfo := hocc (fetch (v cPc) Shift.op (v cH) (v cFee) zeros4 Shift.act) (by simp [Shift.inters, stdState])
  simp only [fetch, zeros4, Shift.op, List.cons_append, List.nil_append, List.map_cons, List.map_nil, hev,
    Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', cPc, cH, cFee, Shift.is64, Shift.fShrS, Shift.fShrU,
    Shift.fRotl, Shift.fRotr] at hfo
  rw [show ((0x74 : Nat) : F) + ((18 : Nat) : F) * ((rowNat tr 4 r 10 : Nat) : F) + ((rowNat tr 4 r 6 : Nat) : F) +
      ((2 : Nat) : F) * ((rowNat tr 4 r 7 : Nat) : F) + ((3 : Nat) : F) * ((rowNat tr 4 r 8 : Nat) : F) +
      ((4 : Nat) : F) * ((rowNat tr 4 r 9 : Nat) : F) =
      ((0x74 + 18 * rowNat tr 4 r 10 + rowNat tr 4 r 6 + 2 * rowNat tr 4 r 7 + 3 * rowNat tr 4 r 8 +
        4 * rowNat tr 4 r 9 : Nat) : F) by
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]] at hfo
  have hta1 := hocc (r16 (v cTs - v Shift.ta - 1 - B16 * v Shift.ha) Shift.act) (by simp [Shift.inters, timeChk])
  have hta2 := hocc (r16 (4 * v Shift.ha) Shift.act) (by simp [Shift.inters, timeChk])
  have htb1 := hocc (r16 (v cTs - v Shift.tb - 1 - B16 * v Shift.hb) Shift.act) (by simp [Shift.inters, timeChk])
  have htb2 := hocc (r16 (4 * v Shift.hb) Shift.act) (by simp [Shift.inters, timeChk])
  simp only [r16, B16, List.map_cons, List.map_nil, hev, Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', cTs,
    Shift.ta, Shift.ha, Shift.tb, Shift.hb] at hta1 hta2 htb1 htb2
  have vA := val4_bytes (fun k => rowNat tr 4 r (11 + k))
  simp only [Nat.reduceAdd] at vA
  have hflags : (rowNat tr 4 r 5 = 1 ∧ rowNat tr 4 r 6 = 0 ∧ rowNat tr 4 r 7 = 0 ∧ rowNat tr 4 r 8 = 0 ∧ rowNat tr 4 r 9 = 0) ∨
      (rowNat tr 4 r 5 = 0 ∧ rowNat tr 4 r 6 = 1 ∧ rowNat tr 4 r 7 = 0 ∧ rowNat tr 4 r 8 = 0 ∧ rowNat tr 4 r 9 = 0) ∨
      (rowNat tr 4 r 5 = 0 ∧ rowNat tr 4 r 6 = 0 ∧ rowNat tr 4 r 7 = 1 ∧ rowNat tr 4 r 8 = 0 ∧ rowNat tr 4 r 9 = 0) ∨
      (rowNat tr 4 r 5 = 0 ∧ rowNat tr 4 r 6 = 0 ∧ rowNat tr 4 r 7 = 0 ∧ rowNat tr 4 r 8 = 1 ∧ rowNat tr 4 r 9 = 0) ∨
      (rowNat tr 4 r 5 = 0 ∧ rowNat tr 4 r 6 = 0 ∧ rowNat tr 4 r 7 = 0 ∧ rowNat tr 4 r 8 = 0 ∧ rowNat tr 4 r 9 = 1) := by
    omega
  have w64 : rowNat tr 4 r 10 = 0 ∨ rowNat tr 4 r 10 = 1 := by omega
  refine mul_binop_rowfacts L hpub (rowNat tr 4 r) hcP
    (0x74 + 18 * rowNat tr 4 r 10 + rowNat tr 4 r 6 + 2 * rowNat tr 4 r 7 + 3 * rowNat tr 4 r 8 + 4 * rowNat tr 4 r 9)
    (rowNat tr 4 r 10)
    (fun i => rowNat tr 4 r (11 + 2 * i) + 256 * rowNat tr 4 r (11 + 2 * i + 1))
    (fun i => rowNat tr 4 r (21 + i)) Rr 19 20 25 26 80 81
    hIn hOut hCons hProd hfo hta1 hta2 htb1 htb2 ?_ ?_ ?_
  · rcases w64 with g | g <;>
    rcases hflags with ⟨g5, g6, g7, g8, g9⟩ | ⟨g5, g6, g7, g8, g9⟩ | ⟨g5, g6, g7, g8, g9⟩ | ⟨g5, g6, g7, g8, g9⟩ |
      ⟨g5, g6, g7, g8, g9⟩ <;> rw [g, g6, g7, g8, g9] <;> simp [isBinop, binops]
  · rcases w64 with g | g <;>
    rcases hflags with ⟨g5, g6, g7, g8, g9⟩ | ⟨g5, g6, g7, g8, g9⟩ | ⟨g5, g6, g7, g8, g9⟩ | ⟨g5, g6, g7, g8, g9⟩ |
      ⟨g5, g6, g7, g8, g9⟩ <;> rw [g, g6, g7, g8, g9] <;> simp [opW]
  · intro oka okb
    simp only [Msg.ok, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero] at oka okb ⊢
    obtain ⟨w', hup, hbyt, hz, hbin⟩ := shift_sound (rowNat tr 4 r) (tr.row pub 4 r) hcP hcon a1
      (fun k hk => hab k hk) okb.1 hq hrest (fun j hj => hPb j hj) (fun j hj => hcy j hj)
    have rl : ∀ i, i < 4 → Rr i = shiftR (rowNat tr 4 r) (2 * i) + 256 * shiftR (rowNat tr 4 r) (2 * i + 1) := by
      intro i hi
      have := hbyt (2 * i) (by omega); have := hbyt (2 * i + 1) (by omega)
      exact tn _ (by omega)
    have r0 := rl 0 (by decide); have r1 := rl 1 (by decide); have r2 := rl 2 (by decide); have r3 := rl 3 (by decide)
    simp only [Nat.reduceMul, Nat.reduceAdd] at r0 r1 r2 r3
    have b0 := hbyt 0 (by decide); have b1 := hbyt 1 (by decide); have b2 := hbyt 2 (by decide)
    have b3 := hbyt 3 (by decide); have b4 := hbyt 4 (by decide); have b5 := hbyt 5 (by decide)
    have b6 := hbyt 6 (by decide); have b7 := hbyt 7 (by decide)
    rw [r0, r1, r2, r3]
    refine ⟨⟨by omega, by omega, by omega, by omega, ?_⟩, ?_⟩
    · rcases w64 with g | g
      · left
        have z4 := hz g 4 (by omega) (by omega); have z5 := hz g 5 (by omega) (by omega)
        have z6 := hz g 6 (by omega) (by omega); have z7 := hz g 7 (by omega) (by omega)
        rw [z4, z5, z6, z7]; exact ⟨g, rfl, rfl⟩
      · right; exact g
    · have vR := val4_bytes (shiftR (rowNat tr 4 r))
      rw [vA, vR]
      rcases w64 with g | g <;>
      rcases hflags with ⟨g5, g6, g7, g8, g9⟩ | ⟨g5, g6, g7, g8, g9⟩ | ⟨g5, g6, g7, g8, g9⟩ | ⟨g5, g6, g7, g8, g9⟩ |
        ⟨g5, g6, g7, g8, g9⟩ <;> rw [g, g6, g7, g8, g9] at hbin ⊢ <;> simpa [opW, opK] using hbin


theorem shift_counts_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Shift.table.constraints, e.eval (natRow (rowNat tr 4 r) (tr.row pub 4 r)) = 0) :
    ∀ i ∈ Shift.inters, (i.count.eval (tr.row pub 4 r)).toNat ≤ 1 := by
  have bAct := hcon (Chips.bool Shift.act) (by simp [Shift.table, Shift.constraints])
  rw [← row_eq_natRow] at bAct
  simp only [Chips.bool, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat'] at bAct
  intro i hi
  have hc : i.count = Shift.act :=
    of_decide_eq_true (List.all_eq_true.mp
      (show Shift.inters.all (fun i => decide (i.count = Shift.act)) = true by decide) i hi)
  rw [hc]
  rcases bool_cases bAct with h | h <;> rw [h]
  · exact Nat.zero_le _
  · exact Nat.le_of_eq (toNat_of_eq_one rfl)

theorem shift_counts {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 4) :
    ∀ i ∈ Shift.inters, (i.count.eval (tr.row pub 4 r)).toNat ≤ 1 :=
  shift_counts_of (table_constr H (by simp [air_len]) hr)

/-- (No `H`/`hr` needed: every SHIFT count is the activity expression itself.) -/
theorem shift_inactive {pub : List F} {tr : Trace} {r : Nat}
    (hna : ¬ rowAct Shift.table tr pub 4 r) :
    ∀ i ∈ Shift.inters, (i.count.eval (tr.row pub 4 r)).toNat ≠ 1 := by
  intro i hi
  have hc : i.count = Shift.act :=
    of_decide_eq_true (List.all_eq_true.mp
      (show Shift.inters.all (fun i => decide (i.count = Shift.act)) = true by decide) i hi)
  rw [hc]
  exact hna

end WasmBase
