import WasmBase.Main.SegRowsX

/-!
# WasmBase.Main.SegRegKeep — instruction rows keep the register file (E2E M4b, S4)

**`seg_instr_regKeep`**: every active instruction row (tables 1–14, IF, CONV, UNREACH) of a
`HoldsX (wasmBaseSegAir …)` trace has `RegKeep` (its spec step leaves `registers` unchanged), for an
M2-checked module with the CODE binding.  So `InstrRegKeep` (a premise of the first `seg_sound` draft)
is a theorem.

The argument: the instruction a row executes is `NonHostI` (`StepRegs.step_registers`), because

1. the row's FETCH query (count = the row's activity) is a code record (`seg_fetchM2`) at the row's own
   pc (`loc_unique`), i.e. `recordAtM2 … pc` of the instruction at `pc`;
2. the record's opcode is the row's FETCH op, which is `< 0x1FF` (**`fetch_op_lt`**): every instruction
   chip's op is a linear form `c + Σ w·f` in bit columns whose one-hot group is the row's count, so its
   value is at most `c + max_{group} w + Σ_{others} w` (`FetchOpOk`, checked by `decide`; the bound
   uses that exactly one flag of the count group is set on an active row);
3. a record with opcode `< 0x1FF` is not a host call: calls of imports get `opHost = 0x1FF` or
   `opHostX = 0x242`, and `call_indirect` has no record (**`recordAtM2_nonHost`**).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 3. A record below `0x1FF` is not a host call -/

theorem recordAtM2_nonHost {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)}
    {H : Array Nat} {off pc : Nat} {cinfo : Nat → Option Nat} {rec : List Nat}
    (hr : recordAtM2 cfg p pf L H off cinfo pc = some rec) {ins : Instr} (hc : pf.code[pc]? = some ins)
    (hop : rec.getD 1 0 < 0x1FF) : StepRegs.NonHostI p ins := by
  cases ins with
  | call fi =>
    show p.m.imports.size ≤ fi
    refine Classical.byContradiction fun hlt => ?_
    have hlt' : fi < p.m.imports.size := by omega
    unfold recordAtM2 at hr
    rw [hc] at hr
    cases hf : feeUnits cfg pf.gas[pc]? with
    | none => simp [hf] at hr
    | some fee =>
      simp only [hf, hlt', if_true] at hr
      split at hr
      · cases hr; simp [Chips.opHost] at hop
      · split at hr
        · cases hr; simp [opHostX] at hop
        · cases hr
  | callIndirect a b =>
    exfalso
    unfold recordAtM2 at hr
    rw [hc] at hr
    cases hf : feeUnits cfg pf.gas[pc]? with
    | none => simp [hf] at hr
    | some fee => simp [hf, recordOf, kindOf] at hr
  | _ => trivial

theorem recordAtM2_pc {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)}
    {H : Array Nat} {off pc : Nat} {cinfo : Nat → Option Nat} {rec : List Nat}
    (hr : recordAtM2 cfg p pf L H off cinfo pc = some rec) : rec.getD 0 0 = off + pc := by
  unfold recordAtM2 at hr
  repeat' split at hr
  all_goals first
    | (cases hr; rfl)
    | (obtain ⟨op, x0, x1, x2, x3, rfl, -⟩ := recordOf_spec hr; rfl)
    | cases hr

/-! ## 2. Linear forms in bit columns -/

/-- An expression `c + Σ w·col` (constants, columns, `const * col`, sums). -/
def linE : Expr → Option (Nat × List (Nat × Nat))
  | .c n => some (n, [])
  | .col i => some (0, [(1, i)])
  | .mul (.c w) (.col i) => some (0, [(w, i)])
  | .add a b => match linE a, linE b with
    | some (c1, l1), some (c2, l2) => some (c1 + c2, l1 ++ l2)
    | _, _ => none
  | _ => none

/-- The natural value of a linear form at a row's cells. -/
def linN (rw : Row) (l : List (Nat × Nat)) : Nat := (l.map fun p => p.1 * (rw.cur p.2).toNat).sum

theorem linN_append (rw : Row) (l1 l2 : List (Nat × Nat)) : linN rw (l1 ++ l2) = linN rw l1 + linN rw l2 := by
  simp [linN, List.map_append, List.sum_append]

theorem linE_eval (rw : Row) : ∀ (e : Expr) (c : Nat) (l : List (Nat × Nat)), linE e = some (c, l) →
    e.eval rw = ((c + linN rw l : Nat) : F)
  | .c n, c, l, h => by
    simp only [linE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp [linN, Expr.eval]
  | .col i, c, l, h => by
    simp only [linE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp [linN, Expr.eval, Fp.cast_toNat]
  | .mul (.c w) (.col i), c, l, h => by
    simp only [linE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [linN, Expr.eval, Lean.Grind.Semiring.natCast_mul, Fp.cast_toNat]
  | .add a b, c, l, h => by
    simp only [linE] at h
    split at h
    · rename_i c1 l1 c2 l2 ha hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [Expr.eval, linE_eval rw a c1 l1 ha, linE_eval rw b c2 l2 hb, linN_append,
        ← Lean.Grind.Semiring.natCast_add]
      congr 1; omega
    · cases h
  | .nxt _, _, _, h => by simp [linE] at h
  | .pub _, _, _, h => by simp [linE] at h
  | .first, _, _, h => by simp [linE] at h
  | .last, _, _, h => by simp [linE] at h
  | .trans, _, _, h => by simp [linE] at h
  | .sub _ _, _, _, h => by simp [linE] at h
  | .mul (.c _) (.c _), _, _, h => by simp [linE] at h
  | .mul (.c _) (.nxt _), _, _, h => by simp [linE] at h
  | .mul (.c _) (.pub _), _, _, h => by simp [linE] at h
  | .mul (.c _) .first, _, _, h => by simp [linE] at h
  | .mul (.c _) .last, _, _, h => by simp [linE] at h
  | .mul (.c _) .trans, _, _, h => by simp [linE] at h
  | .mul (.c _) (.add _ _), _, _, h => by simp [linE] at h
  | .mul (.c _) (.sub _ _), _, _, h => by simp [linE] at h
  | .mul (.c _) (.mul _ _), _, _, h => by simp [linE] at h
  | .mul (.col _) _, _, _, h => by simp [linE] at h
  | .mul (.nxt _) _, _, _, h => by simp [linE] at h
  | .mul (.pub _) _, _, _, h => by simp [linE] at h
  | .mul .first _, _, _, h => by simp [linE] at h
  | .mul .last _, _, _, h => by simp [linE] at h
  | .mul .trans _, _, _, h => by simp [linE] at h
  | .mul (.add _ _) _, _, _, h => by simp [linE] at h
  | .mul (.sub _ _) _, _, _, h => by simp [linE] at h
  | .mul (.mul _ _) _, _, _, h => by simp [linE] at h

/-- A sum over a duplicate-free sublist-up-to-order is at most the sum over the list. -/
theorem sum_le_of_nodup_subset (b : Nat → Nat) :
    ∀ (l S : List Nat), l.Nodup → (∀ x ∈ l, x ∈ S) → (l.map b).sum ≤ (S.map b).sum
  | [], _, _, _ => by simp
  | x :: l, S, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have hx : x ∈ S := hsub x List.mem_cons_self
    have hp := (List.perm_cons_erase hx).map b
    rw [hp.sum_nat, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    have := sum_le_of_nodup_subset b l (S.erase x) hnd.2 (fun y hy => by
      have hne : y ≠ x := fun h => hnd.1 (h ▸ hy)
      exact (List.mem_erase_of_ne hne).mpr (hsub y (List.mem_cons_of_mem _ hy)))
    omega

/-- The bound of a linear form whose columns in `S` form a one-hot group. -/
def linBound (S : List Nat) (c : Nat) (l : List (Nat × Nat)) : Nat :=
  c + ((l.filter fun p => decide (p.2 ∈ S)).map Prod.fst).foldr max 0 +
    ((l.filter fun p => decide (p.2 ∉ S)).map Prod.fst).sum

theorem le_foldr_max {w : Nat} : ∀ {ws : List Nat}, w ∈ ws → w ≤ ws.foldr max 0
  | _ :: _, List.Mem.head _ => by simp [List.foldr]; omega
  | _ :: _, List.Mem.tail _ h => by have := le_foldr_max h; simp [List.foldr]; omega

theorem linN_bound (rw : Row) (S : List Nat) (l : List (Nat × Nat))
    (hbit : ∀ p ∈ l, (rw.cur p.2).toNat ≤ 1)
    (hS : ((l.filter fun p => decide (p.2 ∈ S)).map Prod.snd).Nodup)
    (hone : (S.map fun i => (rw.cur i).toNat).sum ≤ 1) :
    linN rw l ≤ ((l.filter fun p => decide (p.2 ∈ S)).map Prod.fst).foldr max 0 +
      ((l.filter fun p => decide (p.2 ∉ S)).map Prod.fst).sum := by
  obtain ⟨M, hMdef⟩ : ∃ M, M = ((l.filter fun p => decide (p.2 ∈ S)).map Prod.fst).foldr max 0 := ⟨_, rfl⟩
  rw [← hMdef]
  -- split the form
  have split : ∀ l' : List (Nat × Nat), linN rw l' =
      linN rw (l'.filter fun p => decide (p.2 ∈ S)) + linN rw (l'.filter fun p => decide (p.2 ∉ S)) := by
    intro l'
    induction l' with
    | nil => simp [linN]
    | cons p l' ih =>
      by_cases h : p.2 ∈ S
      · simp only [List.filter_cons, h, decide_true, decide_false, not_true_eq_false, not_false_eq_true, Bool.false_eq_true, if_true, if_false]
        simp only [linN, List.map_cons, List.sum_cons] at ih ⊢; omega
      · simp only [List.filter_cons, h, decide_true, decide_false, not_true_eq_false, not_false_eq_true, Bool.false_eq_true, if_true, if_false]
        simp only [linN, List.map_cons, List.sum_cons] at ih ⊢; omega
  rw [split]
  -- the outside part: each bit ≤ 1
  have hout : ∀ l' : List (Nat × Nat), (∀ p ∈ l', (rw.cur p.2).toNat ≤ 1) → linN rw l' ≤ (l'.map Prod.fst).sum := by
    intro l' h
    induction l' with
    | nil => simp [linN]
    | cons p l' ih =>
      have h1 := h p List.mem_cons_self
      have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp only [linN, List.map_cons, List.sum_cons] at ih' ⊢
      have : p.1 * (rw.cur p.2).toNat ≤ p.1 := by
        calc p.1 * (rw.cur p.2).toNat ≤ p.1 * 1 := Nat.mul_le_mul_left _ h1
          _ = p.1 := by omega
      omega
  -- the group part: ≤ M · (Σ bits) ≤ M
  have hin : ∀ l' : List (Nat × Nat), (∀ p ∈ l', p.1 ≤ M) →
      linN rw l' ≤ M * ((l'.map Prod.snd).map fun i => (rw.cur i).toNat).sum := by
    intro l' h
    induction l' with
    | nil => simp [linN]
    | cons p l' ih =>
      have h1 := h p List.mem_cons_self
      have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp only [linN, List.map_cons, List.sum_cons] at ih' ⊢
      have : p.1 * (rw.cur p.2).toNat ≤ M * (rw.cur p.2).toNat := Nat.mul_le_mul_right _ h1
      rw [Nat.mul_add]; omega
  have hle : ((((l.filter fun p => decide (p.2 ∈ S)).map Prod.snd).map fun i => (rw.cur i).toNat).sum) ≤ 1 := by
    refine Nat.le_trans (sum_le_of_nodup_subset _ _ S hS (fun x hx => ?_)) hone
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    simpa using (List.mem_filter.mp hp).2
  have h1 := hin (l.filter fun p => decide (p.2 ∈ S)) (fun p hp => hMdef ▸ le_foldr_max (List.mem_map_of_mem hp))
  have h2 := hout (l.filter fun p => decide (p.2 ∉ S)) (fun p hp => hbit p (List.mem_filter.mp hp).1)
  have h3 : M * ((((l.filter fun p => decide (p.2 ∈ S)).map Prod.snd).map fun i => (rw.cur i).toNat).sum) ≤ M := by
    calc _ ≤ M * 1 := Nat.mul_le_mul_left _ hle
      _ = M := by omega
  omega

theorem linN_ones (rw : Row) : ∀ S' : List (Nat × Nat), (∀ p ∈ S', p.1 = 1) →
    linN rw S' = ((S'.map Prod.snd).map fun i => (rw.cur i).toNat).sum
  | [], _ => rfl
  | p :: S', h => by
    have h1 := h p List.mem_cons_self
    have ih := linN_ones rw S' (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [linN, List.map_cons, List.sum_cons, h1, Nat.one_mul] at ih ⊢
    rw [ih]

theorem sum_bits_le (b : Nat → Nat) : ∀ S : List Nat, (∀ i ∈ S, b i ≤ 1) → (S.map b).sum ≤ S.length
  | [], _ => by simp
  | x :: S, h => by
    have := sum_bits_le b S (fun i hi => h i (List.mem_cons_of_mem _ hi))
    have := h x List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

theorem getD_map_eval (rw : Row) (es : List Expr) (k : Nat) :
    (es.map (·.eval rw)).getD k 0 = (es.getD k 0).eval rw := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases es[k]? <;> rfl

/-- The `k`-th field expression of a table's STATE receive. -/
def stE (T : Table) (k : Nat) : Expr := (T.inters.getD 0 default).msg.getD k 0

theorem stE_eval (T : Table) (tr : Trace) (pub : List F) (t r k : Nat) :
    (stE T k).eval (tr.row pub t r) = (rowIn T tr pub t r).getD k 0 := by
  simp only [stE, rowIn, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : (T.inters[0]?.getD default).msg[k]? <;> simp [h] <;> rfl

/-! ## The FETCH op of an instruction row is below `0x1FF` -/

/-- The decidable check: a FETCH send with the row's count, the row's pc, and an op whose linear-form
bound (one-hot group = the count's columns, all bit columns) is below `0x1FF`. -/
def FetchOpOk (T : Table) : Bool :=
  T.inters.any fun i =>
    decide (i.bus = busFetch) && i.send && decide (i.count = (T.inters.getD 0 default).count) &&
    decide (i.msg.head? = some (stE T 0)) &&
    match linE (i.msg.getD 1 0), linE i.count with
    | some (c, l), some (c0, S') =>
      decide (c0 = 0) && S'.all (fun p => decide (p.1 = 1)) && decide (S'.length < 1000) &&
      decide (((l.filter fun p => decide (p.2 ∈ S'.map Prod.snd)).map Prod.snd).Nodup) &&
      l.all (fun p => decide (p.2 ∈ bcOf T)) && S'.all (fun p => decide (p.2 ∈ bcOf T)) &&
      decide (linBound (S'.map Prod.snd) c l < 0x1FF)
    | _, _ => false

theorem instr_fetchOpOk : ∀ t, IsInstrM2 t → FetchOpOk (chipM2 t) = true := by
  intro t ht
  rcases ht with ⟨h1, h14⟩ | rfl | rfl | rfl
  · rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨
      t = 12 ∨ t = 13 ∨ t = 14 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  all_goals decide +kernel

/-- **The FETCH op bound** on an active row of a table passing `FetchOpOk` whose bit columns are
bits. -/
theorem fetch_op_lt {T : Table} (hok : FetchOpOk T = true) {tr : Trace} {pub : List F} {t r : Nat}
    (hbit : ∀ i ∈ bcOf T, (tr.cell t r i).toNat ≤ 1) (ha : rowAct T tr pub t r) :
    ∃ i : Inter, i ∈ T.inters ∧ i.bus = busFetch ∧ i.send = true ∧ (i.count.eval (tr.row pub t r)).toNat = 1 ∧
      (i.msg.map (·.eval (tr.row pub t r))).getD 0 0 = (rowIn T tr pub t r).getD 0 0 ∧
      ((i.msg.map (fun e : Expr => e.eval (tr.row pub t r))).getD 1 0).toNat < 0x1FF := by
  have hP := P_val
  obtain ⟨i, hi, hc⟩ := List.any_eq_true.mp hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hb, hs⟩, hcnt⟩, hpc⟩, hlin⟩ := hc
  have hact : (i.count.eval (tr.row pub t r)).toNat = 1 := by rw [hcnt]; exact ha
  refine ⟨i, hi, hb, hs, hact, ?_, ?_⟩
  · rw [getD_map_eval, List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, hpc, Option.getD_some, stE_eval]
  · split at hlin
    · rename_i c l c0 S' hl hS
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hlin
      obtain ⟨⟨⟨⟨⟨⟨hc0, hw1⟩, hSlen⟩, hlnd⟩, hlb⟩, hSb⟩, hbnd⟩ := hlin
      subst hc0
      have bitsOf : ∀ x ∈ bcOf T, ((tr.row pub t r).cur x).toNat ≤ 1 := fun x hx => hbit x hx
      -- the count: Σ_S bits = 1
      have ecnt := linE_eval (tr.row pub t r) _ _ _ hS
      rw [linN_ones _ S' (fun p hp => by simpa using hw1 p hp)] at ecnt
      have hle := sum_bits_le (fun i => ((tr.row pub t r).cur i).toNat) (S'.map Prod.snd) (fun x hx => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        exact bitsOf _ (by simpa using hSb p hp))
      have hlen : (S'.map Prod.snd).length = S'.length := by simp
      rw [ecnt, Fp.toNat_cast_of_lt (by omega)] at hact
      have hone : ((S'.map Prod.snd).map fun i => ((tr.row pub t r).cur i).toNat).sum ≤ 1 := by omega
      -- the op
      have eop := linE_eval (tr.row pub t r) _ _ _ hl
      have hbound := linN_bound (tr.row pub t r) (S'.map Prod.snd) l
        (fun p hp => bitsOf _ (by simpa using hlb p hp)) hlnd hone
      unfold linBound at hbnd
      rw [getD_map_eval, eop, Fp.toNat_cast_of_lt (by omega)]
      omega
    · cases hlin

/-! ## 1. The row's record and the conclusion -/

/-- The instruction tables of the segment AIR: same constraints as `chipM2 t`, and `chipM2 t`'s
interactions among theirs (RET + tombstone extends RET). -/
theorem seg_instr_tab (nloc ngl t : Nat) (htI : IsInstrM2 t) :
    ∃ ht : t < (wasmBaseSegAir nloc ngl).tables.length,
      ((wasmBaseSegAir nloc ngl).tables[t]'ht).constraints = (chipM2 t).constraints ∧
      ∀ i ∈ (chipM2 t).inters, i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters := by
  rcases htI with ⟨h1, h14⟩ | rfl | rfl | rfl
  · rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨
      t = 12 ∨ t = 13 ∨ t = 14 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact ⟨by simp [seg_air_len], rfl, fun i hi => hi⟩
        | exact ⟨by simp [seg_air_len], rfl, fun i hi => List.mem_append_left _ hi⟩
  all_goals exact ⟨by simp [seg_air_len], rfl, fun i hi => hi⟩

theorem getD_map_cast (l : List Nat) (k : Nat) :
    (l.map fun x => ((x : Nat) : F)).getD k 0 = ((l.getD k 0 : Nat) : F) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[k]? <;> rfl

/-- **Instruction rows keep the register file** (`InstrRegKeep`): the instruction an active instruction
row executes is `NonHostI`. -/
theorem seg_instr_regKeep (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hcode : CodeOK X.toCtx tr) :
    ∀ ρ ∈ actListM2 tr pub, ρ.1 ≠ 22 → RegKeep X.toCtx (rowInM tr pub ρ) := by
  intro ρ hρ hne
  have hP := P_val
  obtain ⟨t, r⟩ := ρ
  simp only at hne
  rcases mem_actListM2 hρ with ⟨h22, -, -⟩ | ⟨htI, hr, ha⟩
  · exact absurd h22 hne
  obtain ⟨ht, hcon, hint⟩ := seg_instr_tab nloc ngl t htI
  have hbit : ∀ i ∈ bcOf (chipM2 t), (tr.cell t r i).toNat ≤ 1 := by
    intro i hi
    have h := H.constr t ht r hr _ (by rw [hcon]; exact bcOf_mem hi)
    simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', Trace.row] at h
    have h' : ((rowNat tr t r i : Nat) : F) * (((rowNat tr t r i : Nat) : F) - ((1 : Nat) : F)) = 0 := by
      simp only [rowNat, Fp.cast_toNat]; exact h
    rcases bool_nat (rowNat_lt tr t r i) h' with h0 | h1 <;> (show rowNat tr t r i ≤ 1; omega)
  obtain ⟨i, hi, hb, hs, hc1, hpc, hop⟩ := fetch_op_lt (instr_fetchOpOk t htI) hbit ha
  have ho := row_occ (pub := pub) ht hr (hint i hi)
  obtain ⟨j, hj, hm⟩ := seg_fetchM2 H X hcode (o := (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)),
    (i.count.eval (tr.row pub t r)).toNat)) ho hb hs hc1
  simp only at hm
  have eI : rowInM tr pub (t, r) = rowIn (chipM2 t) tr pub t r := by
    have ec : chipTM2 t = chipM2 t := by simp [chipTM2, hne]
    simp [rowInM, ec]
  rw [eI]
  refine regKeep_of_code fun E s f tps tpl tt pc S live a b R hin ins hins => ?_
  -- the record of `j` is `recordAtM2` at a location `(k, l)`
  obtain ⟨k, l, hk, hl, hoff, hrj⟩ := X.recG hj
  have hrec := X.rec_at hk hl
  have hsz : l < (X.ckOf k).records.size := by rw [(X.factsOf hk).records]; exact hl
  rw [Array.getElem?_eq_getElem hsz] at hrec
  simp only [codeRecM2, hrj, Option.getD_some, Array.getElem?_eq_getElem hsz] at hm
  generalize (X.ckOf k).records[l] = rec at hrec hm
  -- its pc is the row's pc
  have hpc0 := recordAtM2_pc hrec
  have hop1 := recordAtM2_op_lt hrec
  have htot : X.M.codeSize < 2 ^ 20 := X.mf.total
  have hkE := R.kLt
  have hpcE := R.pcLt
  simp only [toCtx_nf, toCtx_pfOf] at hkE hpcE
  have hoffE := X.off_bound hkE
  have hoffk := X.off_bound hk
  have h0 := congrArg (fun m => m.getD 0 0) hm
  have h1 := congrArg (fun m => m.getD 1 0) hm
  simp only [getD_map_cast] at h0 h1
  rw [hpc, hin, hpc0] at h0
  have e0 : X.offOf k + l = X.offOf E.k + pc :=
    natEq (by simpa [stMsg] using h0.symm) (by omega) (by omega)
  obtain ⟨rfl, rfl⟩ := X.loc_unique hk hl hkE hpcE e0
  have hopN : rec.getD 1 0 < 0x1FF := by
    rw [h1, Fp.toNat_cast_of_lt (by omega)] at hop
    exact hop
  exact recordAtM2_nonHost hrec (by simpa using hins) hopN

#print axioms recordAtM2_nonHost
#print axioms fetch_op_lt
#print axioms seg_instr_regKeep

end WasmBase
