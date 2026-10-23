import WasmBase.Main.Rows
import WasmBase.StepOps
import WasmBase.Local.Mul
/-!
# Row lemma: MUL (`i32.mul`, `i64.mul`), and a generic binary-operation row lemma
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-- Generic row facts for a binary-operation chip: input / output state, two consumed stack
messages (slots `h-2`, `h-1`, same tag), one produced message (slot `h-2`), a FETCH of a binary
opcode, two channel time checks, and the chip's local semantic guarantee `sem`. -/
theorem mul_binop_rowfacts {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (L : Looks X nloc ncode pub tr) (hpub : PubOK X nloc ncode pub)
    (c : Nat → Nat) (hcP : ∀ i, c i < P) (op tag : Nat) (A B Rr : Nat → Nat) (ta ha tb hb ksb kcid : Nat)
    {inS outS : List F} {cons prod : List Msg}
    (hIn : inS = [((c 0 : Nat) : F), ((c 1 : Nat) : F), ((c 2 : Nat) : F), ((0 : Nat) : F),
      ((c ksb : Nat) : F), ((c kcid : Nat) : F)])
    (hOut : outS = [((c 0 : Nat) : F) + ((1 : Nat) : F), ((c 1 : Nat) : F) + ((1 : Nat) : F),
      ((c 2 : Nat) : F) + ((c 4 : Nat) : F), ((0 : Nat) : F), ((c ksb : Nat) : F), ((c kcid : Nat) : F)])
    (hcons : cons = [⟨0, (((c ksb : Nat) : F) + ((c 3 : Nat) : F) - ((2 : Nat) : F)).toNat, tag, A 0, A 1, A 2, A 3, c ta⟩,
      ⟨0, (((c ksb : Nat) : F) + ((c 3 : Nat) : F) - ((1 : Nat) : F)).toNat, tag, B 0, B 1, B 2, B 3, c tb⟩])
    (hprod : prod = [⟨0, (((c ksb : Nat) : F) + ((c 3 : Nat) : F) - ((2 : Nat) : F)).toNat, tag, Rr 0, Rr 1, Rr 2, Rr 3, c 1⟩])
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
      (⟨0, 0, tag, Rr 0, Rr 1, Rr 2, Rr 3, 0⟩ : Msg).ok ∧
        Num.binop (opW op) (opK op) (val4 (A 0) (A 1) (A 2) (A 3)) (val4 (B 0) (B 1) (B 2) (B 3)) =
          some (val4 (Rr 0) (Rr 1) (Rr 2) (Rr 3))) :
    RowFacts X inS outS cons prod := by
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
  refine ⟨?_, by rw [hIn]; rfl, by rw [hIn, hOut]; rfl, ⟨fee, hfl, ?_⟩, ?_, ?_, by rw [hprod]; simp⟩
  rotate_left
  · rw [hIn, hOut]; simp only [gasF, List.getD_cons_succ, List.getD_cons_zero, efee']
  · rw [hcons]; intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨na, hna, by rw [hIn]; exact ena⟩
    · exact ⟨nb, hnb, by rw [hIn]; exact enb⟩
  · rw [hprod, hIn]; simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, lvl,
      List.getD_cons_succ, List.getD_cons_zero]; exact ⟨hcP _, trivial⟩
  -- the spec step
  intro E s f tps tpl t pc S live S_seg segb R hin hlive ht1 hS hg64
  rw [hIn] at hin
  obtain ⟨i0, i1, i2, -, i4, i5⟩ := stMsg_cons hin
  have hpcl := R.pcLt
  have hoffb := X.off_bound R.kLt
  have htot := X.mf.total
  obtain ⟨ls0, hL0, hfl0⟩ := R.labels
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
  have hout : outS = stMsg (X.offOf E.k + pc + 1) (t + 1) (S + fee) 0 E.sb E.cid := by
    rw [hOut, p0, p1, p2, efee', psb, pcid]
    simp only [stMsg, Lean.Grind.Semiring.natCast_add]
  rw [hcons] at hlive ⊢
  rw [hprod]
  refine ⟨E.k, pc + 1, fee, 0, E.sb, E.cid, hfl, by omega, (by rw [hout, Nat.add_assoc]), fun hg => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
  rw [s2, s1, p1]
  rw [s2, s1] at hlive
  exact step_binop X R hins hop hfee hg hg64 _ _ _
    (hlive _ (by simp)) (hlive _ (by simp)) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl, htag⟩
    (fun oka okb => by
      have := sem (by simpa [Msg.ok] using oka) (by simpa [Msg.ok] using okb)
      exact ⟨by simpa [Msg.ok] using this.1, by simpa [Msg.val] using this.2⟩)

theorem mul_pair {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace} (L : Looks X nloc ncode pub tr) {a b : Nat}
    (ha : a < P) (hb : b < P)
    (ho : (busByte, true, [((0 : Nat) : F), ((a : Nat) : F), ((b : Nat) : F), ((0 : Nat) : F)], 1) ∈
      occs (wasmBaseAir nloc ncode) tr pub) : a < 256 ∧ b < 256 := by
  have hP' := P_val
  obtain ⟨k, x, y, -, hx, hy, hm⟩ := L.byte _ ho rfl rfl rfl
  simp only [List.cons.injEq, and_true] at hm
  obtain ⟨-, e1, e2, -⟩ := hm
  exact ⟨by rw [natEq e1 ha (by omega)]; exact hx, by rw [natEq e2 hb (by omega)]; exact hy⟩

theorem mul_r16 {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace} (L : Looks X nloc ncode pub tr) {a : Nat}
    (ha : a < P) (ho : (busR16, true, [((a : Nat) : F)], 1) ∈ occs (wasmBaseAir nloc ncode) tr pub) :
    a < 65536 := by
  obtain ⟨x, hx, hl⟩ := L.r16 _ ho rfl rfl rfl
  simp only [List.cons.injEq, and_true] at hx
  rw [← hx, Fp.toNat_cast_of_lt ha] at hl; exact hl

theorem mul_limb_cast (a b : Nat) :
    ((a : Nat) : F) + ((256 : Nat) : F) * ((b : Nat) : F) = ((a + 256 * b : Nat) : F) := by
  simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]

theorem mul_rowfacts {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) (L : Looks X nloc ncode pub tr) (hpub : PubOK X nloc ncode pub)
    {r : Nat} (hr : r < tr.height 3) (hact : rowAct Mul.table tr pub 3 r) :
    RowFacts X (rowIn Mul.table tr pub 3 r) (rowOut Mul.table tr pub 3 r)
      (rowCons Mul.table tr pub 3 r) (rowProd Mul.table tr pub 3 r) := by
  have hP' := P_val
  have ht : 3 < (wasmBaseAir nloc ncode).tables.length := by simp [air_len]
  have hcP : ∀ i, rowNat tr 3 r i < P := rowNat_lt tr 3 r
  have hcon : ∀ e ∈ Mul.table.constraints, e.eval (natRow (rowNat tr 3 r) (tr.row pub 3 r)) = 0 :=
    table_constr H ht hr
  have a1 : rowNat tr 3 r 5 = 1 := by
    simpa only [rowAct, Mul.table, Mul.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero,
      v, Expr.eval_col, Trace.row, Mul.act, rowNat] using hact
  have cnt : (Expr.eval (tr.row pub 3 r) (v Mul.act)).toNat = 1 := by
    simp only [v, Expr.eval_col, Trace.row, Mul.act]; exact a1
  have hocc : ∀ i ∈ Mul.inters, i.count = v Mul.act →
      (i.bus, i.send, i.msg.map (·.eval (tr.row pub 3 r)), 1) ∈ occs (wasmBaseAir nloc ncode) tr pub := by
    intro i hi hc
    have := row_occ (pub := pub) ht hr (show i ∈ Mul.table.inters from hi)
    rwa [hc, cnt] at this
  have hev : ∀ i, Expr.eval (tr.row pub 3 r) (v i) = ((rowNat tr 3 r i : Nat) : F) := fun i => by
    simp only [v, Expr.eval_col, Trace.row, cell_cast]
  -- byte and range lookups
  have hbyte : ∀ base, base = Mul.ab ∨ base = Mul.bb ∨ base = Mul.rb → ∀ k, k < 8 → rowNat tr 3 r (base + k) < 256 := by
    intro base hbase k hk
    have key : ∀ i, i < 4 → rowNat tr 3 r (base + 2 * i) < 256 ∧ rowNat tr 3 r (base + 2 * i + 1) < 256 := by
      intro i hi
      have hm : byteQ 0 (v (base + 2 * i)) (v (base + 2 * i + 1)) 0 (v Mul.act) ∈ Mul.inters := by
        simp only [Mul.inters, List.mem_append, List.mem_map, List.mem_range]
        rcases hbase with rfl | rfl | rfl
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩)))
        · exact Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩))
        · exact Or.inl (Or.inr ⟨i, hi, rfl⟩)
      have := hocc _ hm rfl
      simp only [byteQ, List.map_cons, List.map_nil, hev, Expr.eval_ofNat'] at this
      exact mul_pair L (hcP _) (hcP _) this
    rcases (show ∃ i, i < 4 ∧ (k = 2 * i ∨ k = 2 * i + 1) from ⟨k / 2, by omega, by omega⟩) with ⟨i, hi, rfl | rfl⟩
    · exact (key i hi).1
    · rw [← Nat.add_assoc]; exact (key i hi).2
  have hcy : ∀ k, k < 8 → rowNat tr 3 r (Mul.cy + k) < 65536 := by
    intro k hk
    have hm : r16 (v (Mul.cy + k)) (v Mul.act) ∈ Mul.inters := by
      simp only [Mul.inters, List.mem_append, List.mem_map, List.mem_range]; exact Or.inr ⟨k, hk, rfl⟩
    have := hocc _ hm rfl
    simp only [r16, List.map_cons, List.map_nil, hev] at this
    exact mul_r16 L (hcP _) this
  -- the row's messages
  have hIn : rowIn Mul.table tr pub 3 r =
      [((rowNat tr 3 r 0 : Nat) : F), ((rowNat tr 3 r 1 : Nat) : F), ((rowNat tr 3 r 2 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 3 r 43 : Nat) : F), ((rowNat tr 3 r 44 : Nat) : F)] := by
    simp only [rowIn, Mul.table, Mul.inters, stdState, stateIn, List.cons_append, List.append_assoc, List.getD_cons_zero,
      List.map_cons, List.map_nil, hev, Expr.eval_ofNat', cPc, cTs, cS, Mul.kSb, Mul.kCid]
  have hOut : rowOut Mul.table tr pub 3 r =
      [((rowNat tr 3 r 0 : Nat) : F) + ((1 : Nat) : F), ((rowNat tr 3 r 1 : Nat) : F) + ((1 : Nat) : F),
        ((rowNat tr 3 r 2 : Nat) : F) + ((rowNat tr 3 r 4 : Nat) : F), ((0 : Nat) : F),
        ((rowNat tr 3 r 43 : Nat) : F), ((rowNat tr 3 r 44 : Nat) : F)] := by
    simp only [rowOut, Mul.table, Mul.inters, stdState, stateOut, List.cons_append, List.append_assoc,
      List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil, hev, Expr.eval_add', Expr.eval_ofNat',
      cPc, cTs, cS, cFee, Mul.kSb, Mul.kCid]
  have hab := hbyte Mul.ab (Or.inl rfl)
  have hbb := hbyte Mul.bb (Or.inr (Or.inl rfl))
  have hrb := hbyte Mul.rb (Or.inr (Or.inr rfl))
  simp only [Mul.ab, Mul.bb, Mul.rb] at hab hbb hrb
  have lim : ∀ base, (∀ k, k < 8 → rowNat tr 3 r (base + k) < 256) → ∀ i, i < 4 →
      rowNat tr 3 r (base + 2 * i) + 256 * rowNat tr 3 r (base + 2 * i + 1) < 65536 := by
    intro base hb i hi
    have := hb (2 * i) (by omega); have := hb (2 * i + 1) (by omega)
    rw [← Nat.add_assoc] at *; omega
  have tn : ∀ x : Nat, x < 65536 → (((x : Nat) : F)).toNat = x := fun x hx => Fp.toNat_cast_of_lt (by omega)
  have hCons : rowCons Mul.table tr pub 3 r =
      [⟨0, (((rowNat tr 3 r 43 : Nat) : F) + ((rowNat tr 3 r 3 : Nat) : F) - ((2 : Nat) : F)).toNat, rowNat tr 3 r 6,
        rowNat tr 3 r (7 + 2 * 0) + 256 * rowNat tr 3 r (7 + 2 * 0 + 1),
        rowNat tr 3 r (7 + 2 * 1) + 256 * rowNat tr 3 r (7 + 2 * 1 + 1),
        rowNat tr 3 r (7 + 2 * 2) + 256 * rowNat tr 3 r (7 + 2 * 2 + 1),
        rowNat tr 3 r (7 + 2 * 3) + 256 * rowNat tr 3 r (7 + 2 * 3 + 1), rowNat tr 3 r 15⟩,
       ⟨0, (((rowNat tr 3 r 43 : Nat) : F) + ((rowNat tr 3 r 3 : Nat) : F) - ((1 : Nat) : F)).toNat, rowNat tr 3 r 6,
        rowNat tr 3 r (17 + 2 * 0) + 256 * rowNat tr 3 r (17 + 2 * 0 + 1),
        rowNat tr 3 r (17 + 2 * 1) + 256 * rowNat tr 3 r (17 + 2 * 1 + 1),
        rowNat tr 3 r (17 + 2 * 2) + 256 * rowNat tr 3 r (17 + 2 * 2 + 1),
        rowNat tr 3 r (17 + 2 * 3) + 256 * rowNat tr 3 r (17 + 2 * 3 + 1), rowNat tr 3 r 25⟩] := by
    rw [rowCons, rowMsgs_eq]
    simp only [Mul.table, Mul.inters, stdState, stateIn, stateOut, fetch, stkSend, stkRecv, chSend, chRecv, timeChk,
      r16, byteQ, List.cons_append, List.nil_append, List.append_assoc, List.map_append, List.filter_append,
      List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, busState, busFetch, busStk, busR16, busByte,
      List.range, List.range.loop]
    simp only [show (0 : Nat) = 2 ↔ False by decide, show (1 : Nat) = 2 ↔ False by decide,
      show (3 : Nat) = 2 ↔ False by decide, show (4 : Nat) = 2 ↔ False by decide, false_and,
      decide_false, Bool.false_eq_true, ite_false, true_and, and_true, decide_true, ite_true, List.filterMap_cons,
      List.filterMap_nil, cnt, List.nil_append, List.append_nil, List.cons_append]
    simp only [limbsB, limbB, List.range, List.range.loop, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, hev, Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', cH, Mul.kSb, Mul.is64, Mul.ab,
      Mul.bb, Mul.ta, Mul.tb, mul_limb_cast, decMsg, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd,
      Nat.reduceMul]
    have la := fun i hi => lim 7 hab i hi
    have lb := fun i hi => lim 17 hbb i hi
    have a0 := la 0 (by decide); have a1 := la 1 (by decide); have a2 := la 2 (by decide); have a3 := la 3 (by decide)
    have b0 := lb 0 (by decide); have b1 := lb 1 (by decide); have b2 := lb 2 (by decide); have b3 := lb 3 (by decide)
    simp only [Nat.reduceAdd, Nat.reduceMul] at a0 a1 a2 a3 b0 b1 b2 b3
    simp only [Bool.true_eq_false, decide_false, Bool.false_eq_true, ite_false, List.filterMap_nil, List.map_nil,
      tn _ a0, tn _ a1, tn _ a2, tn _ a3, tn _ b0, tn _ b1, tn _ b2, tn _ b3, Fp.toNat_cast_of_lt (hcP _),
      show (((0 : Nat) : F)).toNat = 0 from rfl]
  have hProd : rowProd Mul.table tr pub 3 r =
      [⟨0, (((rowNat tr 3 r 43 : Nat) : F) + ((rowNat tr 3 r 3 : Nat) : F) - ((2 : Nat) : F)).toNat, rowNat tr 3 r 6,
        rowNat tr 3 r (27 + 2 * 0) + 256 * rowNat tr 3 r (27 + 2 * 0 + 1),
        rowNat tr 3 r (27 + 2 * 1) + 256 * rowNat tr 3 r (27 + 2 * 1 + 1),
        rowNat tr 3 r (27 + 2 * 2) + 256 * rowNat tr 3 r (27 + 2 * 2 + 1),
        rowNat tr 3 r (27 + 2 * 3) + 256 * rowNat tr 3 r (27 + 2 * 3 + 1), rowNat tr 3 r 1⟩] := by
    rw [rowProd, rowMsgs_eq]
    simp only [Mul.table, Mul.inters, stdState, stateIn, stateOut, fetch, stkSend, stkRecv, chSend, chRecv, timeChk,
      r16, byteQ, List.cons_append, List.nil_append, List.append_assoc, List.map_append, List.filter_append,
      List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, busState, busFetch, busStk, busR16, busByte,
      List.range, List.range.loop]
    simp only [show (0 : Nat) = 2 ↔ False by decide, show (1 : Nat) = 2 ↔ False by decide,
      show (3 : Nat) = 2 ↔ False by decide, show (4 : Nat) = 2 ↔ False by decide, false_and,
      decide_false, Bool.false_eq_true, ite_false, true_and, and_true, decide_true, ite_true, List.filterMap_cons,
      List.filterMap_nil, cnt, List.nil_append, List.append_nil, List.cons_append, Bool.true_eq_false]
    simp only [limbsB, limbB, List.range, List.range.loop, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, hev, Expr.eval_add', Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', cH, Mul.kSb, cTs, Mul.is64,
      Mul.rb, mul_limb_cast, decMsg, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd, Nat.reduceMul]
    have lr := fun i hi => lim 27 hrb i hi
    have r0 := lr 0 (by decide); have r1 := lr 1 (by decide); have r2 := lr 2 (by decide); have r3 := lr 3 (by decide)
    simp only [Nat.reduceAdd, Nat.reduceMul] at r0 r1 r2 r3
    simp only [tn _ r0, tn _ r1, tn _ r2, tn _ r3, Fp.toNat_cast_of_lt (hcP _),
      show (((0 : Nat) : F)).toNat = 0 from rfl, List.map_cons, List.map_nil]
  have hfo := hocc (fetch (v cPc) Mul.op (v cH) (v cFee) zeros4 (v Mul.act)) (by simp [Mul.inters, stdState]) rfl
  simp only [fetch, zeros4, Mul.op, List.cons_append, List.nil_append, List.map_cons, List.map_nil, hev,
    Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', cPc, cH, cFee, Mul.is64] at hfo
  rw [show ((0x6C : Nat) : F) + ((18 : Nat) : F) * ((rowNat tr 3 r 6 : Nat) : F) = ((0x6C + 18 * rowNat tr 3 r 6 : Nat) : F) by
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]] at hfo
  have hta1 := hocc (r16 (v cTs - v Mul.ta - 1 - B16 * v Mul.ha) (v Mul.act)) (by simp [Mul.inters, timeChk]) rfl
  have hta2 := hocc (r16 (4 * v Mul.ha) (v Mul.act)) (by simp [Mul.inters, timeChk]) rfl
  have htb1 := hocc (r16 (v cTs - v Mul.tb - 1 - B16 * v Mul.hb) (v Mul.act)) (by simp [Mul.inters, timeChk]) rfl
  have htb2 := hocc (r16 (4 * v Mul.hb) (v Mul.act)) (by simp [Mul.inters, timeChk]) rfl
  simp only [r16, B16, List.map_cons, List.map_nil, hev, Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', cTs,
    Mul.ta, Mul.ha, Mul.tb, Mul.hb] at hta1 hta2 htb1 htb2
  -- the local semantics
  obtain ⟨w64, hup, hmul⟩ := mul_sound (rowNat tr 3 r) (tr.row pub 3 r) hcP hcon a1
    (fun k hk => hab k hk) (fun k hk => hbb k hk) (fun k hk => hrb k hk) hcy
  simp only [Mul.is64, Mul.ab, Mul.bb, Mul.rb] at w64 hup hmul
  have lr := fun i hi => lim 27 hrb i hi
  have la := fun i hi => lim 7 hab i hi
  have lb := fun i hi => lim 17 hbb i hi
  have vA := val4_bytes (fun k => rowNat tr 3 r (7 + k))
  have vB := val4_bytes (fun k => rowNat tr 3 r (17 + k))
  have vR := val4_bytes (fun k => rowNat tr 3 r (27 + k))
  simp only [Nat.reduceAdd] at vA vB vR
  refine mul_binop_rowfacts L hpub (rowNat tr 3 r) hcP (0x6C + 18 * rowNat tr 3 r 6) (rowNat tr 3 r 6)
    (fun i => rowNat tr 3 r (7 + 2 * i) + 256 * rowNat tr 3 r (7 + 2 * i + 1))
    (fun i => rowNat tr 3 r (17 + 2 * i) + 256 * rowNat tr 3 r (17 + 2 * i + 1))
    (fun i => rowNat tr 3 r (27 + 2 * i) + 256 * rowNat tr 3 r (27 + 2 * i + 1)) 15 16 25 26 43 44
    hIn hOut hCons hProd hfo hta1 hta2 htb1 htb2 ?_ ?_ ?_
  · rcases w64 with g | g <;> rw [g] <;> simp [isBinop, binops]
  · rcases w64 with g | g <;> rw [g] <;> simp [opW]
  · intro oka okb
    simp only [Msg.ok, Nat.reduceAdd, Nat.reduceMul] at oka okb ⊢
    have r0 := lr 0 (by decide); have r1 := lr 1 (by decide); have r2 := lr 2 (by decide); have r3 := lr 3 (by decide)
    simp only [Nat.reduceAdd, Nat.reduceMul] at r0 r1 r2 r3
    refine ⟨⟨r0, r1, r2, r3, ?_⟩, ?_⟩
    · rcases w64 with g | g
      · left; obtain ⟨-, -, z4⟩ := hup g 4 (by omega) (by omega); obtain ⟨-, -, z5⟩ := hup g 5 (by omega) (by omega)
        obtain ⟨-, -, z6⟩ := hup g 6 (by omega) (by omega); obtain ⟨-, -, z7⟩ := hup g 7 (by omega) (by omega)
        simp only [Nat.reduceAdd] at z4 z5 z6 z7
        rw [z4, z5, z6, z7]; exact ⟨g, rfl, rfl⟩
      · right; exact g
    · rw [vA, vB, vR]
      rcases w64 with g | g <;> rw [g] at hmul ⊢ <;> simpa [opW, opK] using hmul


theorem mul_counts_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Mul.table.constraints, e.eval (natRow (rowNat tr 3 r) (tr.row pub 3 r)) = 0) :
    ∀ i ∈ Mul.inters, (i.count.eval (tr.row pub 3 r)).toNat ≤ 1 := by
  have bAct := hcon (Chips.bool (v Mul.act)) (by simp [Mul.table, Mul.constraints])
  simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow] at bAct
  have hb := bool_nat (rowNat_lt _ _ _ _) bAct
  intro i hi
  have hc : i.count = v Mul.act :=
    of_decide_eq_true (List.all_eq_true.mp
      (show Mul.inters.all (fun i => decide (i.count = v Mul.act)) = true by decide) i hi)
  rw [hc]
  simp only [v, Expr.eval_col, Trace.row]
  show rowNat tr 3 r Mul.act ≤ 1
  omega

theorem mul_counts {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseAir nloc ncode) pub tr) {r : Nat} (hr : r < tr.height 3) :
    ∀ i ∈ Mul.inters, (i.count.eval (tr.row pub 3 r)).toNat ≤ 1 :=
  mul_counts_of (table_constr H (by simp [air_len]) hr)

/-- (No `H`/`hr` needed: every MUL count is the activity column itself.) -/
theorem mul_inactive {pub : List F} {tr : Trace} {r : Nat}
    (hna : ¬ rowAct Mul.table tr pub 3 r) :
    ∀ i ∈ Mul.inters, (i.count.eval (tr.row pub 3 r)).toNat ≠ 1 := by
  intro i hi
  have hc : i.count = v Mul.act :=
    of_decide_eq_true (List.all_eq_true.mp
      (show Mul.inters.all (fun i => decide (i.count = v Mul.act)) = true by decide) i hi)
  rw [hc]
  simpa [rowAct, Mul.table, Mul.inters, stdState, stateIn] using hna

end WasmBase
