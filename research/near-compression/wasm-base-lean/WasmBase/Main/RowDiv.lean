import WasmBase.Main.Rows
import WasmBase.StepOps
import WasmBase.Main.RowMul
import WasmBase.Local.Div
/-!
# Row lemma: DIV (`i32/i64.div_s/div_u/rem_s/rem_u`, with traps), and a generic trapping
binary-operation row lemma
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-- Generic row facts for a trapping binary-operation chip: like `mul_binop_rowfacts`, but the
output state carries `halted = 2 · trp` and the result is produced only when `trp = 0`; when
`trp = 1` the chip's guarantee is that the spec binop returns `none` (the step traps). -/
theorem div_binop_rowfacts {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (L : Looks X nloc ncode pub tr) (hpub : PubOK X nloc ncode pub)
    (c : Nat → Nat) (hcP : ∀ i, c i < P) (op tag : Nat) (A B Rr : Nat → Nat) (ta ha tb hb ksb kcid : Nat)
    {inS outS : List F} {cons prod : List Msg} (trp : Nat) (htrp : trp ≤ 1)
    (hIn : inS = [((c 0 : Nat) : F), ((c 1 : Nat) : F), ((c 2 : Nat) : F), ((0 : Nat) : F),
      ((c ksb : Nat) : F), ((c kcid : Nat) : F)])
    (hOut : outS = [((c 0 : Nat) : F) + ((1 : Nat) : F), ((c 1 : Nat) : F) + ((1 : Nat) : F),
      ((c 2 : Nat) : F) + ((c 4 : Nat) : F), ((2 * trp : Nat) : F), ((c ksb : Nat) : F), ((c kcid : Nat) : F)])
    (hcons : cons = [⟨0, (((c ksb : Nat) : F) + ((c 3 : Nat) : F) - ((2 : Nat) : F)).toNat, tag, A 0, A 1, A 2, A 3, c ta⟩,
      ⟨0, (((c ksb : Nat) : F) + ((c 3 : Nat) : F) - ((1 : Nat) : F)).toNat, tag, B 0, B 1, B 2, B 3, c tb⟩])
    (hprod : prod = if trp = 0 then [⟨0, (((c ksb : Nat) : F) + ((c 3 : Nat) : F) - ((2 : Nat) : F)).toNat, tag, Rr 0, Rr 1, Rr 2, Rr 3, c 1⟩]
      else [])
    (hfo : (busFetch, true, [((c 0 : Nat) : F), ((op : Nat) : F), ((c 3 : Nat) : F), ((c 4 : Nat) : F),
      ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F)], 1) ∈ occs (wasmBaseAir nloc ncode) tr pub)
    (hta1 : (busR16, true, [((c 1 : Nat) : F) - ((c ta : Nat) : F) - ((1 : Nat) : F) - ((65536 : Nat) : F) * ((c ha : Nat) : F)], 1) ∈
      occs (wasmBaseAir nloc ncode) tr pub)
    (hta2 : (busR16, true, [((4 : Nat) : F) * ((c ha : Nat) : F)], 1) ∈ occs (wasmBaseAir nloc ncode) tr pub)
    (htb1 : (busR16, true, [((c 1 : Nat) : F) - ((c tb : Nat) : F) - ((1 : Nat) : F) - ((65536 : Nat) : F) * ((c hb : Nat) : F)], 1) ∈
      occs (wasmBaseAir nloc ncode) tr pub)
    (htb2 : (busR16, true, [((4 : Nat) : F) * ((c hb : Nat) : F)], 1) ∈ occs (wasmBaseAir nloc ncode) tr pub)
    (hop : isBinop op) (htag : tag = if opW op = 64 then 1 else 0)
    (sem : (⟨0, 0, tag, A 0, A 1, A 2, A 3, 0⟩ : Msg).ok → (⟨0, 0, tag, B 0, B 1, B 2, B 3, 0⟩ : Msg).ok →
      (trp = 1 → Num.binop (opW op) (opK op) (val4 (A 0) (A 1) (A 2) (A 3)) (val4 (B 0) (B 1) (B 2) (B 3)) = none) ∧
      (trp = 0 → (⟨0, 0, tag, Rr 0, Rr 1, Rr 2, Rr 3, 0⟩ : Msg).ok ∧
        Num.binop (opW op) (opK op) (val4 (A 0) (A 1) (A 2) (A 3)) (val4 (B 0) (B 1) (B 2) (B 3)) =
          some (val4 (Rr 0) (Rr 1) (Rr 2) (Rr 3)))) :
    RowFacts2 X inS outS cons prod := by
  have hP' := P_val
  have hopl : op ≤ 0x8A := by
    simp only [isBinop, binops, List.mem_cons, List.mem_nil_iff, or_false] at hop; omega
  -- the fee bound, independent of the spec state
  obtain ⟨pc0, hpc0, hm0⟩ := fetch_pc hpub L hfo
  obtain ⟨q, l, ins, fee, rec, hq, hl, hoff, hins, hfee, hfl, hrc, hm⟩ := fetch_rec hpub L hfo hm0 hpc0
  have CF := X.factsOf hq
  obtain ⟨op', x0, x1, x2, x3, hre, hcase⟩ := recordOf_spec hrc
  rw [hre] at hm
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm
  obtain ⟨e0, eop, eh, efee, -, -, -, -⟩ := hm
  have fee16 := feeUnits_lt hfee
  have efee' : c 4 = fee := natEq efee (hcP _) (by omega)
  have hoplt := recordOf_op_lt hrc
  rw [hre] at hoplt; simp only [List.getD_cons_succ, List.getD_cons_zero] at hoplt
  have hopq : op = op' := natEq eop (by omega) (by omega)
  subst hopq
  -- time checks
  obtain ⟨na, hna, ena⟩ := time_chk L hta1 hta2
  obtain ⟨nb, hnb, enb⟩ := time_chk L htb1 htb2
  rw [Fp.toNat_cast_of_lt (hcP _)] at ena enb
  refine ⟨?_, by rw [hIn]; rfl, by rw [hIn, hOut]; rfl, ⟨fee, hfl, ?_⟩, ?_, ?_, by rw [hprod]; split <;> simp⟩
  rotate_left
  · rw [hIn, hOut]; simp only [gasF, List.getD_cons_succ, List.getD_cons_zero, efee']
  · rw [hcons]; intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨na, hna, by rw [hIn]; exact ena⟩
    · exact ⟨nb, hnb, by rw [hIn]; exact enb⟩
  · rw [hprod, hIn]
    split
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, lvl,
        List.getD_cons_succ, List.getD_cons_zero]; exact ⟨hcP _, trivial⟩
    · simp
  -- the spec step
  intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
  rw [hIn] at hin
  obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
  have hpcl := R.pcLt
  have hoffb := X.off_bound R.kLt
  have htot := X.mf.total
  have p0 : c 0 = X.offOf E.k + pc := natEq i0 (hcP _) (by omega)
  have p1 : c 1 = t := natEq i1 (hcP _) (by omega)
  have p2 : c 2 = S := natEq i2 (hcP _) (by omega)
  have psb : c ksb = E.sb := natEq i4 (hcP _) (by have := R.sbLt; omega)
  have pcid : c kcid = E.cid := natEq i5 (hcP _) (by have := R.cidLt; omega)
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
  have p3 : c 3 = s.stack.size - E.sb := natEq eh (hcP _) (by omega)
  have hszP : s.stack.size < P := by have := R.sbLt; omega
  -- the instruction is `.num op`
  have hinsn : ins = .num op := by
    rcases hcase with ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ |
      ⟨_, _, h, _⟩ | ⟨h, _, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, _, hmem, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, hgl, _⟩ | ⟨_, _, _, h, _⟩
    all_goals first
      | (exfalso; simp only [isBinop, binops, List.mem_cons, List.mem_nil_iff, or_false] at hop; omega)
      | (exfalso; omega)
      | exact h
      | (exfalso; subst h; simp [isBinop, binops, Ctrl.opNext, Ctrl.opJump, Ctrl.opJif, Ctrl.opHalt, Ctrl.opHif, opCall] at hop; done)
      | (exfalso; simp only [Ctrl.opNext, Ctrl.opJump, Ctrl.opJif, Ctrl.opHalt, Ctrl.opHif] at h; omega)
      | (exfalso; simp only [opCall] at h; omega)
  subst hinsn
  -- two operands on the stack
  obtain ⟨hfam, hpops⟩ := isFamilyNum_of_binop hop
  have hv := CF.verify pc hpcl
  obtain ⟨ls0, hL, -⟩ := R.labels
  simp only [verifyAt, hins, hL, hH, kindOf, hfam, ite_true, hpops, Bool.and_eq_true,
    decide_eq_true_eq] at hv
  have h2 := hv.1
  have s2 : (((c ksb : Nat) : F) + ((c 3 : Nat) : F) - ((2 : Nat) : F)).toNat = s.stack.size - 2 := by
    exact slot_toNat psb p3 hsbR h2 hszP
  have s1 : (((c ksb : Nat) : F) + ((c 3 : Nat) : F) - ((1 : Nat) : F)).toNat = s.stack.size - 1 := by
    exact slot_toNat psb p3 hsbR (by omega) hszP
  have hout : outS = stMsg (X.offOf E.k + pc + 1) (t + 1) (S + fee) (2 * trp) E.sb E.cid := by
    rw [hOut, p0, p1, p2, efee', psb, pcid]
    simp only [stMsg, Lean.Grind.Semiring.natCast_add]
  rw [hcons] at hlive ⊢
  rw [hprod]
  rw [s2, s1] at hlive
  rcases (show trp = 0 ∨ trp = 1 by omega) with rfl | rfl
  · refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfl, by omega, (by rw [hout, Nat.add_assoc]), fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide),
      fun h => absurd h (by decide)⟩⟩
    simp only [ite_true]
    rw [s2, s1, p1]
    exact step_binop X R hins hop hfee hg hg64 _ _ _
      (hlive _ (by simp)) (hlive _ (by simp)) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl, htag⟩
      (fun oka okb => by
        have := (sem (by simpa [Msg.ok] using oka) (by simpa [Msg.ok] using okb)).2 rfl
        exact ⟨by simpa [Msg.ok] using this.1, by simpa [Msg.val] using this.2⟩)
  · refine ⟨E.k, pc + 1, fee, 2, E.sb, E.cid, hfl, by omega, (by rw [hout, Nat.add_assoc]), fun hg => ⟨fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun _ => ?_⟩⟩
    exact step_binop_trap X R hins hop hfee hg hg64
      ⟨0, s.stack.size - 2, tag, A 0, A 1, A 2, A 3, c ta⟩ ⟨0, s.stack.size - 1, tag, B 0, B 1, B 2, B 3, c tb⟩
      (hlive _ (by simp)) (hlive _ (by simp)) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
      (fun oka okb => by
        have := (sem (by simpa [Msg.ok] using oka) (by simpa [Msg.ok] using okb)).1 rfl
        simpa [Msg.val] using this)

/-- `tz` is a bit on an active DIV row (no range facts needed: `tz = 1 − bsum·inv`, `bsum·tz = 0`). -/
theorem tz_facts' {c : Nat → Nat} {rw : Row} (hP : ∀ i, c i < P) (hact : c 5 + c 6 + c 7 + c 8 = 1)
    (t1 : Expr.eval (natRow c rw) (v Div.tz - Div.act * (1 - Div.bsum * v Div.invB)) = 0)
    (t2 : Expr.eval (natRow c rw) (Div.bsum * v Div.tz) = 0) : c 82 = 0 ∨ c 82 = 1 := by
  simp only [v, Div.tz, Div.invB, Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, natRow_cur,
    act_eval hact] at t1 t2
  generalize Div.bsum.eval (natRow c rw) = bs at t1 t2
  exact bool_nat (hP 82) (by grind)

theorem div_rnToNat (tr : Trace) (t r i : Nat) : (((rowNat tr t r i : Nat) : F)).toNat = rowNat tr t r i :=
  Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)

theorem div_zeroToNat : (((0 : Nat) : F)).toNat = 0 := Fp.toNat_cast_of_lt (by rw [P_val]; omega)

/-! ## The DIV row (table 10) -/

theorem div_table {nloc ncode : Nat} (ht : 10 < (wasmBaseAir nloc ncode).tables.length) :
    (wasmBaseAir nloc ncode).tables[10]'ht = Div.table := rfl

theorem div_cons {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 10) :
    ∀ e ∈ Div.constraints, e.eval (natRow (rowNat tr 10 r) (tr.row pub 10 r)) = 0 := by
  have ht : 10 < (wasmBaseAir nloc ncode).tables.length := by simp [air_len]
  exact table_constr H ht hr

/-- Flags and trap columns of a DIV row. -/
theorem div_flags_of {pub : List F} {tr : Trace} {r : Nat}
    (hc : ∀ e ∈ Div.constraints, e.eval (natRow (rowNat tr 10 r) (tr.row pub 10 r)) = 0) :
    rowNat tr 10 r 5 ≤ 1 ∧ rowNat tr 10 r 6 ≤ 1 ∧ rowNat tr 10 r 7 ≤ 1 ∧ rowNat tr 10 r 8 ≤ 1 ∧
    rowNat tr 10 r 5 + rowNat tr 10 r 6 + rowNat tr 10 r 7 + rowNat tr 10 r 8 ≤ 1 ∧
    (rowNat tr 10 r 5 + rowNat tr 10 r 6 + rowNat tr 10 r 7 + rowNat tr 10 r 8 = 0 →
      rowNat tr 10 r 82 = 0 ∧ rowNat tr 10 r 86 = 0) ∧
    (rowNat tr 10 r 5 + rowNat tr 10 r 6 + rowNat tr 10 r 7 + rowNat tr 10 r 8 = 1 →
      rowNat tr 10 r 82 + rowNat tr 10 r 86 ≤ 1) := by
  have hP' := P_val
  have hcP : ∀ i, rowNat tr 10 r i < P := rowNat_lt tr 10 r
  simp only [Div.constraints, List.forall_mem_append, List.forall_mem_flatMap, List.forall_mem_map,
    List.mem_range, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, List.forall_mem_cons,
    List.forall_mem_nil, and_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, h10⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  obtain ⟨g2, g3, g4, g5, -, g7, g8, -, -, -, -, -, -, -, -, g16, -⟩ := h2
  obtain ⟨t1, t2, t3⟩ := h10
  have b5 : rowNat tr 10 r 5 ≤ 1 := bit_of hcP h1
  have b6 : rowNat tr 10 r 6 ≤ 1 := bit_of hcP g2
  have b7 : rowNat tr 10 r 7 ≤ 1 := bit_of hcP g3
  have b8 : rowNat tr 10 r 8 ≤ 1 := bit_of hcP g4
  have bA : rowNat tr 10 r 22 ≤ 1 := bit_of hcP g7
  have bB : rowNat tr 10 r 24 ≤ 1 := bit_of hcP g8
  have bQ : rowNat tr 10 r 84 ≤ 1 := bit_of hcP g16
  simp only [Chips.bool, Div.act, v, Div.fDivS, Div.fDivU, Div.fRemS, Div.fRemU, Expr.eval_mul', Expr.eval_sub',
    Expr.eval_add', Expr.eval_ofNat', Expr.eval_col, natRow_cur] at g5
  have hsum := bool_nat (n := rowNat tr 10 r 5 + rowNat tr 10 r 6 + rowNat tr 10 r 7 + rowNat tr 10 r 8)
    (by omega) (by simp only [Lean.Grind.Semiring.natCast_add]; exact g5)
  refine ⟨b5, b6, b7, b8, by omega, fun h0 => ?_, fun h1 => ?_⟩
  · have ha : Div.act.eval (natRow (rowNat tr 10 r) (tr.row pub 10 r)) = ((0 : Nat) : F) := by
      simp only [Div.act, v, Div.fDivS, Div.fDivU, Div.fRemS, Div.fRemU, Expr.eval_add', Expr.eval_col, natRow_cur]
      rw [← h0]; simp only [Lean.Grind.Semiring.natCast_add]
    simp only [v, Div.tz, Div.invB, Div.nt, Div.tov, Div.fDivS, Div.hbA, Div.hbB, Div.hbQ, Expr.eval_sub',
      Expr.eval_mul', Expr.eval_ofNat', Expr.eval_col, natRow_cur, ha] at t1 t3
    have z82 : rowNat tr 10 r 82 = 0 := natEq (by grind) (hcP _) (by omega)
    rw [z82] at t3
    exact ⟨z82, natEq (by grind) (hcP _) (by omega)⟩
  · have tz := tz_facts' hcP h1 t1 t2
    have := tov_fact hcP h1 (by omega) b5 bA bB bQ t3
    have hle : rowNat tr 10 r 5 * rowNat tr 10 r 22 * rowNat tr 10 r 24 * rowNat tr 10 r 84 ≤ 1 * 1 * 1 * 1 :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul b5 bA) bB) bQ
    rcases tz with g | g <;> rw [g] at this ⊢ <;> simp only [Nat.sub_zero, Nat.sub_self, Nat.one_mul,
      Nat.zero_mul] at this <;> omega

theorem div_count_eq {i : Inter} (hi : i ∈ Div.inters) : i.count = Div.act ∨ i.count = Div.act * (1 - Div.trap) := by
  have := List.all_eq_true.mp
    (show Div.inters.all (fun i => decide (i.count = Div.act ∨ i.count = Div.act * (1 - Div.trap))) = true by decide) i hi
  simpa using this

theorem div_act_eval (tr : Trace) (pub : List F) (r : Nat) :
    Div.act.eval (tr.row pub 10 r) =
      ((rowNat tr 10 r 5 + rowNat tr 10 r 6 + rowNat tr 10 r 7 + rowNat tr 10 r 8 : Nat) : F) := by
  simp only [Div.act, v, Expr.eval_add', Expr.eval_col, Trace.row, Div.fDivS, Div.fDivU, Div.fRemS, Div.fRemU,
    cell_cast, Lean.Grind.Semiring.natCast_add]

theorem div_trap_eval (tr : Trace) (pub : List F) (r : Nat) :
    Div.trap.eval (tr.row pub 10 r) = ((rowNat tr 10 r 82 + rowNat tr 10 r 86 : Nat) : F) := by
  simp only [Div.trap, v, Expr.eval_add', Expr.eval_col, Trace.row, Div.tz, Div.tov, cell_cast,
    Lean.Grind.Semiring.natCast_add]

/-- The count `act · (1 − trap)` as a natural number. -/
theorem div_cnt2 {tr : Trace} {pub : List F} {r : Nat} {a t : Nat} (ha : a ≤ 1) (ht : a = 1 → t ≤ 1)
    (h0 : a = 0 → t = 0)
    (hae : Div.act.eval (tr.row pub 10 r) = ((a : Nat) : F)) (hte : Div.trap.eval (tr.row pub 10 r) = ((t : Nat) : F)) :
    ((Div.act * (1 - Div.trap)).eval (tr.row pub 10 r)).toNat = a * (1 - t) := by
  have hP' := P_val
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', hae, hte]
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl
  · rw [h0 rfl]; rfl
  · rcases (show t = 0 ∨ t = 1 by have := ht rfl; omega) with rfl | rfl
    · rw [show ((1 : Nat) : F) * (((1 : Nat) : F) - ((0 : Nat) : F)) = ((1 : Nat) : F) by grind]; rfl
    · rw [show ((1 : Nat) : F) * (((1 : Nat) : F) - ((1 : Nat) : F)) = ((0 : Nat) : F) by grind]; rfl

theorem div_counts_of {pub : List F} {tr : Trace} {r : Nat}
    (hc : ∀ e ∈ Div.constraints, e.eval (natRow (rowNat tr 10 r) (tr.row pub 10 r)) = 0) :
    ∀ i ∈ Div.inters, (i.count.eval (tr.row pub 10 r)).toNat ≤ 1 := by
  have hP' := P_val
  obtain ⟨-, -, -, -, hs, h0, h1⟩ := div_flags_of hc
  intro i hi
  rcases div_count_eq hi with hc | hc <;> rw [hc]
  · rw [div_act_eval, Fp.toNat_cast_of_lt (by omega)]; exact hs
  · rw [div_cnt2 hs h1 (fun h => (h0 h).1 ▸ (h0 h).2 ▸ rfl) (div_act_eval tr pub r) (div_trap_eval tr pub r)]
    have : rowNat tr 10 r 5 + rowNat tr 10 r 6 + rowNat tr 10 r 7 + rowNat tr 10 r 8 = 0 ∨
      rowNat tr 10 r 5 + rowNat tr 10 r 6 + rowNat tr 10 r 7 + rowNat tr 10 r 8 = 1 := by omega
    rcases this with h | h <;> rw [h] <;> omega

theorem div_counts {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 10) :
    ∀ i ∈ Div.inters, (i.count.eval (tr.row pub 10 r)).toNat ≤ 1 :=
  div_counts_of (div_cons (pub := pub) H hr)

theorem div_flags {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 10) :
    rowNat tr 10 r 5 ≤ 1 ∧ rowNat tr 10 r 6 ≤ 1 ∧ rowNat tr 10 r 7 ≤ 1 ∧ rowNat tr 10 r 8 ≤ 1 ∧
    rowNat tr 10 r 5 + rowNat tr 10 r 6 + rowNat tr 10 r 7 + rowNat tr 10 r 8 ≤ 1 ∧
    (rowNat tr 10 r 5 + rowNat tr 10 r 6 + rowNat tr 10 r 7 + rowNat tr 10 r 8 = 0 →
      rowNat tr 10 r 82 = 0 ∧ rowNat tr 10 r 86 = 0) ∧
    (rowNat tr 10 r 5 + rowNat tr 10 r 6 + rowNat tr 10 r 7 + rowNat tr 10 r 8 = 1 →
      rowNat tr 10 r 82 + rowNat tr 10 r 86 ≤ 1) :=
  div_flags_of (div_cons (pub := pub) H hr)

theorem div_inactive {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 10)
    (hna : ¬ rowAct Div.table tr pub 10 r) : ∀ i ∈ Div.inters, (i.count.eval (tr.row pub 10 r)).toNat ≠ 1 := by
  have hP' := P_val
  obtain ⟨-, -, -, -, hs, h0, h1⟩ := div_flags H hr
  have hna' : rowNat tr 10 r 5 + rowNat tr 10 r 6 + rowNat tr 10 r 7 + rowNat tr 10 r 8 ≠ 1 := by
    intro h; apply hna
    simp only [rowAct, Div.table, Div.inters, stateIn, List.cons_append, List.getD_cons_zero, div_act_eval]
    rw [Fp.toNat_cast_of_lt (by omega)]; exact h
  have hz : rowNat tr 10 r 5 + rowNat tr 10 r 6 + rowNat tr 10 r 7 + rowNat tr 10 r 8 = 0 := by omega
  intro i hi
  rcases div_count_eq hi with hc | hc <;> rw [hc]
  · rw [div_act_eval, hz]; decide
  · rw [div_cnt2 hs h1 (fun h => (h0 h).1 ▸ (h0 h).2 ▸ rfl) (div_act_eval tr pub r) (div_trap_eval tr pub r), hz]
    simp

theorem div_rowfacts {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hpub : PubOK X nloc ncode pub)
    {r : Nat} (hr : r < tr.height 10) (hact : rowAct Div.table tr pub 10 r) :
    RowFacts2 X (rowIn Div.table tr pub 10 r) (rowOut Div.table tr pub 10 r)
      (rowCons Div.table tr pub 10 r) (rowProd Div.table tr pub 10 r) := by
  have hP' := P_val
  have ht : 10 < (wasmBaseAir nloc ncode).tables.length := by simp [air_len]
  have hcP : ∀ i, rowNat tr 10 r i < P := rowNat_lt tr 10 r
  have hcon := div_cons (pub := pub) H hr
  obtain ⟨b5, b6, b7, b8, hs, -, h1⟩ := div_flags H hr
  have b9 : rowNat tr 10 r Div.is64 ≤ 1 := bit_of hcP (hcon (Chips.bool (v Div.is64)) (by simp [Div.constraints]))
  simp only [Div.is64] at b9
  have a1 : rowNat tr 10 r 5 + rowNat tr 10 r 6 + rowNat tr 10 r 7 + rowNat tr 10 r 8 = 1 := by
    have := hact
    simp only [rowAct, Div.table, Div.inters, stateIn, List.cons_append, List.getD_cons_zero, div_act_eval] at this
    rwa [Fp.toNat_cast_of_lt (by omega)] at this
  have cnt : (Div.act.eval (tr.row pub 10 r)).toNat = 1 := by
    rw [div_act_eval, a1]; rfl
  have htrp := h1 a1
  have hocc : ∀ i ∈ Div.inters, i.count = Div.act →
      (i.bus, i.send, i.msg.map (·.eval (tr.row pub 10 r)), 1) ∈ occs (wasmBaseAir nloc ncode) tr pub := by
    intro i hi hc
    have := row_occ (pub := pub) ht hr (show i ∈ Div.table.inters from hi)
    rwa [hc, cnt] at this
  have hev : ∀ i, Expr.eval (tr.row pub 10 r) (v i) = ((rowNat tr 10 r i : Nat) : F) := fun i => by
    simp only [v, Expr.eval_col, Trace.row, cell_cast]
  -- byte lookups
  have q26 := hocc (byteQ 0 (v 26) (v 27) 0 Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at q26
  obtain ⟨y26, y27⟩ := mul_pair L (hcP _) (hcP _) q26
  have q28 := hocc (byteQ 0 (v 28) (v 29) 0 Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at q28
  obtain ⟨y28, y29⟩ := mul_pair L (hcP _) (hcP _) q28
  have q30 := hocc (byteQ 0 (v 30) (v 31) 0 Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at q30
  obtain ⟨y30, y31⟩ := mul_pair L (hcP _) (hcP _) q30
  have q32 := hocc (byteQ 0 (v 32) (v 33) 0 Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at q32
  obtain ⟨y32, y33⟩ := mul_pair L (hcP _) (hcP _) q32
  have q34 := hocc (byteQ 0 (v 34) (v 35) 0 Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at q34
  obtain ⟨y34, y35⟩ := mul_pair L (hcP _) (hcP _) q34
  have q36 := hocc (byteQ 0 (v 36) (v 37) 0 Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at q36
  obtain ⟨y36, y37⟩ := mul_pair L (hcP _) (hcP _) q36
  have q38 := hocc (byteQ 0 (v 38) (v 39) 0 Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at q38
  obtain ⟨y38, y39⟩ := mul_pair L (hcP _) (hcP _) q38
  have q40 := hocc (byteQ 0 (v 40) (v 41) 0 Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at q40
  obtain ⟨y40, y41⟩ := mul_pair L (hcP _) (hcP _) q40
  have q42 := hocc (byteQ 0 (v 42) (v 43) 0 Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at q42
  obtain ⟨y42, y43⟩ := mul_pair L (hcP _) (hcP _) q42
  have q44 := hocc (byteQ 0 (v 44) (v 45) 0 Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at q44
  obtain ⟨y44, y45⟩ := mul_pair L (hcP _) (hcP _) q44
  have q46 := hocc (byteQ 0 (v 46) (v 47) 0 Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at q46
  obtain ⟨y46, y47⟩ := mul_pair L (hcP _) (hcP _) q46
  have q48 := hocc (byteQ 0 (v 48) (v 49) 0 Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at q48
  obtain ⟨y48, y49⟩ := mul_pair L (hcP _) (hcP _) q48
  have q50 := hocc (byteQ 0 (v 50) (v 51) 0 Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at q50
  obtain ⟨y50, y51⟩ := mul_pair L (hcP _) (hcP _) q50
  have q52 := hocc (byteQ 0 (v 52) (v 53) 0 Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at q52
  obtain ⟨y52, y53⟩ := mul_pair L (hcP _) (hcP _) q52
  have q54 := hocc (byteQ 0 (v 54) (v 55) 0 Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at q54
  obtain ⟨y54, y55⟩ := mul_pair L (hcP _) (hcP _) q54
  have q56 := hocc (byteQ 0 (v 56) (v 57) 0 Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at q56
  obtain ⟨y56, y57⟩ := mul_pair L (hcP _) (hcP _) q56
  -- RANGE16 lookups
  have o74 := hocc (r16 (v 74) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev] at o74
  have d74 := mul_r16 L (hcP _) o74
  have o75 := hocc (r16 (v 75) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev] at o75
  have d75 := mul_r16 L (hcP _) o75
  have o76 := hocc (r16 (v 76) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev] at o76
  have d76 := mul_r16 L (hcP _) o76
  have o77 := hocc (r16 (v 77) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev] at o77
  have d77 := mul_r16 L (hcP _) o77
  have o87 := hocc (r16 (v 87) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev] at o87
  have rs87 := mul_r16 L (hcP _) o87
  have o88 := hocc (r16 (v 88) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev] at o88
  have rs88 := mul_r16 L (hcP _) o88
  have o89 := hocc (r16 (v 89) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev] at o89
  have rs89 := mul_r16 L (hcP _) o89
  have o90 := hocc (r16 (v 90) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev] at o90
  have rs90 := mul_r16 L (hcP _) o90
  have o66 := hocc (r16 (v 66) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev] at o66
  have k66 := mul_r16 L (hcP _) o66
  have o67 := hocc (r16 (v 67) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev] at o67
  have k67 := mul_r16 L (hcP _) o67
  have o68 := hocc (r16 (v 68) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev] at o68
  have k68 := mul_r16 L (hcP _) o68
  have o69 := hocc (r16 (v 69) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev] at o69
  have k69 := mul_r16 L (hcP _) o69
  have o70 := hocc (r16 (v 70) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev] at o70
  have k70 := mul_r16 L (hcP _) o70
  have o71 := hocc (r16 (v 71) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev] at o71
  have k71 := mul_r16 L (hcP _) o71
  have o72 := hocc (r16 (v 72) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev] at o72
  have k72 := mul_r16 L (hcP _) o72
  have o73 := hocc (r16 (v 73) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev] at o73
  have k73 := mul_r16 L (hcP _) o73
  have o23 := hocc (r16 (2 * v 23) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev, Expr.eval_mul', Expr.eval_ofNat'] at o23
  have hra : (2 * rowNat tr 10 r 23) % P < 65536 := by
    obtain ⟨x, hx, hl⟩ := L.r16 _ o23 rfl rfl rfl
    simp only [List.cons.injEq, and_true] at hx
    rw [← hx, ← Lean.Grind.Semiring.natCast_mul, Fp.toNat_cast] at hl; exact hl
  have o25 := hocc (r16 (2 * v 25) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev, Expr.eval_mul', Expr.eval_ofNat'] at o25
  have hrb : (2 * rowNat tr 10 r 25) % P < 65536 := by
    obtain ⟨x, hx, hl⟩ := L.r16 _ o25 rfl rfl rfl
    simp only [List.cons.injEq, and_true] at hx
    rw [← hx, ← Lean.Grind.Semiring.natCast_mul, Fp.toNat_cast] at hl; exact hl
  have o85 := hocc (r16 (2 * v 85) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, List.map_cons, List.map_nil, hev, Expr.eval_mul', Expr.eval_ofNat'] at o85
  have hrq : (2 * rowNat tr 10 r 85) % P < 65536 := by
    obtain ⟨x, hx, hl⟩ := L.r16 _ o85 rfl rfl rfl
    simp only [List.cons.injEq, and_true] at hx
    rw [← hx, ← Lean.Grind.Semiring.natCast_mul, Fp.toNat_cast] at hl; exact hl
  have hbytes : ∀ i, i < 32 → rowNat tr 10 r (26 + i) < 256 := by
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
      i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨
      i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hcy : ∀ k, k < 8 → rowNat tr 10 r (66 + k) < 65536 := by
    intro k hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hd : ∀ i, i < 4 → rowNat tr 10 r (74 + i) < 65536 := by
    intro i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> assumption
  have hres : ∀ i, i < 4 → rowNat tr 10 r (87 + i) < 65536 := by
    intro i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> assumption
  -- the row's messages
  have hIn : rowIn Div.table tr pub 10 r =
      [((rowNat tr 10 r 0 : Nat) : F), ((rowNat tr 10 r 1 : Nat) : F), ((rowNat tr 10 r 2 : Nat) : F),
        ((0 : Nat) : F), ((rowNat tr 10 r 95 : Nat) : F), ((rowNat tr 10 r 96 : Nat) : F)] := by
    simp only [rowIn, Div.table, Div.inters, stateIn, List.cons_append, List.getD_cons_zero, List.map_cons,
      List.map_nil, hev, Expr.eval_ofNat', cPc, cTs, cS, Div.kSb, Div.kCid]
  have hOut : rowOut Div.table tr pub 10 r =
      [((rowNat tr 10 r 0 : Nat) : F) + ((1 : Nat) : F), ((rowNat tr 10 r 1 : Nat) : F) + ((1 : Nat) : F),
        ((rowNat tr 10 r 2 : Nat) : F) + ((rowNat tr 10 r 4 : Nat) : F),
        ((2 * (rowNat tr 10 r 82 + rowNat tr 10 r 86) : Nat) : F), ((rowNat tr 10 r 95 : Nat) : F),
        ((rowNat tr 10 r 96 : Nat) : F)] := by
    simp only [rowOut, Div.table, Div.inters, stateOut, List.cons_append, List.getD_cons_succ, List.getD_cons_zero,
      List.map_cons, List.map_nil, hev, Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', div_trap_eval, cPc, cTs,
      cS, cFee, Div.kSb, Div.kCid, Lean.Grind.Semiring.natCast_mul]
  have hCons : rowCons Div.table tr pub 10 r =
      [⟨0, (((rowNat tr 10 r 95 : Nat) : F) + ((rowNat tr 10 r 3 : Nat) : F) - ((2 : Nat) : F)).toNat, rowNat tr 10 r 9, rowNat tr 10 r 10,
          rowNat tr 10 r 11, rowNat tr 10 r 12, rowNat tr 10 r 13, rowNat tr 10 r 14⟩,
        ⟨0, (((rowNat tr 10 r 95 : Nat) : F) + ((rowNat tr 10 r 3 : Nat) : F) - ((1 : Nat) : F)).toNat, rowNat tr 10 r 9, rowNat tr 10 r 16,
          rowNat tr 10 r 17, rowNat tr 10 r 18, rowNat tr 10 r 19, rowNat tr 10 r 20⟩] := by
    rw [rowCons, rowMsgs_eq, show Div.table.inters.filter (fun i => i.bus = busStk ∧ i.send = false) =
      [stkRecv (v Div.kSb + v cH - 2) (v Div.is64) (limbsOf Div.a) (v Div.ta) Div.act,
       stkRecv (v Div.kSb + v cH - 1) (v Div.is64) (limbsOf Div.b) (v Div.tb) Div.act] by decide]
    simp only [List.filterMap_cons, List.filterMap_nil, stkRecv, chRecv, cnt, ite_true]
    simp only [List.map_cons, List.map_nil, limbsOf, List.range, List.range.loop, List.cons_append,
      List.nil_append, hev, Expr.eval_add', Expr.eval_sub', Expr.eval_ofNat', cH, Div.kSb, Div.is64, Div.a, Div.ta, Div.b, Div.tb,
      Nat.reduceAdd, decMsg, List.getD_cons_zero, List.getD_cons_succ, div_rnToNat, div_zeroToNat]
  have hProd : rowProd Div.table tr pub 10 r =
      if rowNat tr 10 r 82 + rowNat tr 10 r 86 = 0 then
        [⟨0, (((rowNat tr 10 r 95 : Nat) : F) + ((rowNat tr 10 r 3 : Nat) : F) - ((2 : Nat) : F)).toNat, rowNat tr 10 r 9, rowNat tr 10 r 87,
          rowNat tr 10 r 88, rowNat tr 10 r 89, rowNat tr 10 r 90, rowNat tr 10 r 1⟩] else [] := by
    rw [rowProd, rowMsgs_eq, show Div.table.inters.filter (fun i => i.bus = busStk ∧ i.send = true) =
      [stkSend (v Div.kSb + v cH - 2) (v Div.is64) (limbsOf Div.res) (v cTs) (Div.act * (1 - Div.trap))] by decide]
    simp only [List.filterMap_cons, List.filterMap_nil, stkSend, chSend]
    rw [div_cnt2 (by omega) (fun _ => htrp) (by omega) (div_act_eval tr pub r) (div_trap_eval tr pub r), a1]
    rcases (show rowNat tr 10 r 82 + rowNat tr 10 r 86 = 0 ∨ rowNat tr 10 r 82 + rowNat tr 10 r 86 = 1 by omega)
      with g | g <;> rw [g]
    · simp only [ite_true, List.map_cons, List.map_nil, limbsOf, List.range, List.range.loop, List.cons_append,
        List.nil_append, hev, Expr.eval_add', Expr.eval_sub', Expr.eval_ofNat', cH, Div.kSb, cTs, Div.is64, Div.res, Nat.reduceAdd, decMsg,
        List.getD_cons_zero, List.getD_cons_succ, div_rnToNat, div_zeroToNat, Nat.sub_zero, Nat.mul_one]
    · simp
  have hfo := hocc (fetch (v cPc) Div.op (v cH) (v cFee) zeros4 Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [fetch, zeros4, Div.op, List.cons_append, List.nil_append, List.map_cons, List.map_nil, hev,
    Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', cPc, cH, cFee, Div.is64, Div.fDivU, Div.fRemS,
    Div.fRemU] at hfo
  rw [show ((0x6D : Nat) : F) + ((18 : Nat) : F) * ((rowNat tr 10 r 9 : Nat) : F) + ((rowNat tr 10 r 6 : Nat) : F) +
      ((2 : Nat) : F) * ((rowNat tr 10 r 7 : Nat) : F) + ((3 : Nat) : F) * ((rowNat tr 10 r 8 : Nat) : F) =
      ((0x6D + 18 * rowNat tr 10 r 9 + rowNat tr 10 r 6 + 2 * rowNat tr 10 r 7 + 3 * rowNat tr 10 r 8 : Nat) : F) by
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]] at hfo
  have hta1 := hocc (r16 (v cTs - v Div.ta - 1 - B16 * v Div.ha) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  have hta2 := hocc (r16 (4 * v Div.ha) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  have htb1 := hocc (r16 (v cTs - v Div.tb - 1 - B16 * v Div.hb) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  have htb2 := hocc (r16 (4 * v Div.hb) Div.act) (by letI : BEq Inter := instBEqOfDecidableEq; decide) rfl
  simp only [r16, B16, List.map_cons, List.map_nil, hev, Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', cTs,
    Div.ta, Div.ha, Div.tb, Div.hb] at hta1 hta2 htb1 htb2
  -- opcode facts
  have h1hot : (rowNat tr 10 r 6 = 0 ∧ rowNat tr 10 r 7 = 0 ∧ rowNat tr 10 r 8 = 0) ∨
      (rowNat tr 10 r 6 = 1 ∧ rowNat tr 10 r 7 = 0 ∧ rowNat tr 10 r 8 = 0) ∨
      (rowNat tr 10 r 6 = 0 ∧ rowNat tr 10 r 7 = 1 ∧ rowNat tr 10 r 8 = 0) ∨
      (rowNat tr 10 r 6 = 0 ∧ rowNat tr 10 r 7 = 0 ∧ rowNat tr 10 r 8 = 1) := by omega
  have hwk : opW (0x6D + 18 * rowNat tr 10 r 9 + rowNat tr 10 r 6 + 2 * rowNat tr 10 r 7 + 3 * rowNat tr 10 r 8) =
        32 + 32 * rowNat tr 10 r 9 ∧
      opK (0x6D + 18 * rowNat tr 10 r 9 + rowNat tr 10 r 6 + 2 * rowNat tr 10 r 7 + 3 * rowNat tr 10 r 8) =
        3 + rowNat tr 10 r 6 + 2 * rowNat tr 10 r 7 + 3 * rowNat tr 10 r 8 := by
    rcases (show rowNat tr 10 r 9 = 0 ∨ rowNat tr 10 r 9 = 1 by omega) with g | g <;>
      simp only [opW, opK, g] <;> constructor <;> split <;> omega
  refine div_binop_rowfacts L hpub (rowNat tr 10 r) hcP
    (0x6D + 18 * rowNat tr 10 r 9 + rowNat tr 10 r 6 + 2 * rowNat tr 10 r 7 + 3 * rowNat tr 10 r 8)
    (rowNat tr 10 r 9) (fun i => rowNat tr 10 r (10 + i)) (fun i => rowNat tr 10 r (16 + i))
    (fun i => rowNat tr 10 r (87 + i)) 14 15 20 21 95 96 (rowNat tr 10 r 82 + rowNat tr 10 r 86) htrp
    hIn hOut hCons hProd hfo hta1 hta2 htb1 htb2 ?_ ?_ ?_
  · rcases (show rowNat tr 10 r 9 = 0 ∨ rowNat tr 10 r 9 = 1 by omega) with g | g <;>
      rcases h1hot with ⟨e6, e7, e8⟩ | ⟨e6, e7, e8⟩ | ⟨e6, e7, e8⟩ | ⟨e6, e7, e8⟩ <;>
      simp only [g, e6, e7, e8] <;> simp [isBinop, binops]
  · rw [hwk.1]; rcases (show rowNat tr 10 r 9 = 0 ∨ rowNat tr 10 r 9 = 1 by omega) with g | g <;> simp [g]
  · intro oka okb
    simp only [Msg.ok, Nat.reduceAdd] at oka okb
    have ha : ∀ i, i < 4 → rowNat tr 10 r (10 + i) < 65536 := by
      intro i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp only [Nat.reduceAdd, Nat.add_zero] <;> omega
    have hb : ∀ i, i < 4 → rowNat tr 10 r (16 + i) < 65536 := by
      intro i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp only [Nat.reduceAdd, Nat.add_zero] <;> omega
    obtain ⟨-, hz, -, hnone, hsome⟩ := div_sound (rowNat tr 10 r) (tr.row pub 10 r) hcP hcon a1 ha hb hra hrb hrq
      hbytes hcy hd hres
    simp only [Nat.reduceAdd, hwk.1, hwk.2]
    refine ⟨hnone, fun h0 => ⟨⟨rs87, rs88, rs89, rs90, ?_⟩, hsome h0⟩⟩
    rcases (show rowNat tr 10 r 9 = 0 ∨ rowNat tr 10 r 9 = 1 by omega) with g | g
    · obtain ⟨-, -, -, -, z89, z90⟩ := hz g; exact Or.inl ⟨g, z89, z90⟩
    · exact Or.inr g

end WasmBase
