import WasmBase.Main.RegWalkG
import WasmBase.SegAir
/-!
# WasmBase.Main.SegHoldsX — the satisfaction relation of a segment trace with an external chip bus

`wasmBaseSegAir` receives on bus 103 (`Seg.busIf`), the interface of the **native** SHA-512
compression chip (`native/sha384-air4`), which is not a Lean table: the prover attaches it next to
the Lean tables, and the LogUp balance of bus 103 is between the chip's sends and the Lean tables'
receives.  `Holds (wasmBaseSegAir …)` states the balance of *every* bus over the Lean tables only,
so on bus 103 it demands that the Lean receives balance against **no** sends.  That is
unsatisfiable: CUTI's first row receives on bus 103 with count `kD + kP = 1`
(`Main/SegSha.seg_holds_false`).  Every theorem stated from `Holds (wasmBaseSegAir …)` is therefore
vacuous.

`HoldsX A pub tr` is `Holds` with the balance of bus `extBus = 103` removed (everything else —
publics, heights, constraints, the balance of every other bus, the per-bus load bound — is
unchanged).  `Holds A pub tr → HoldsX A pub tr` (`Holds.toX`, a coercion).  The bus-103 traffic is
then the separate named hypothesis `Main/SegSha.ChipIf` (the chip contract plus the bus-103 balance
with the chip's sends).

This file has the generic lemmas the segment files need, restated for `HoldsX` (they only use
constraints, heights, `busBound`, and the balance of buses `≠ 103`).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Local
set_option linter.unusedSimpArgs false

/-- The bus of the native SHA-512 compression chip (`Seg.busIf`). -/
def extBus : Nat := 103

theorem extBus_eq : extBus = Seg.busIf := rfl

/-- **The AIR relation with the external chip bus left open**: `Holds` without the balance of
bus `extBus` (103). -/
structure HoldsX (A : Air) (pub : List F) (tr : Trace) : Prop where
  pubLen : pub.length = A.numPub
  heightPos : ∀ t, t < A.tables.length → 4 ≤ tr.height t
  heightLe : ∀ t, t < A.tables.length → tr.height t ≤ 2 ^ maxLogHeight
  constr : ∀ t (ht : t < A.tables.length), ∀ r, r < tr.height t →
    ∀ e ∈ (A.tables[t]'ht).constraints, e.eval (tr.row pub t r) = 0
  balance : ∀ b m, b ≠ extBus → busNat A tr pub b true m % P = busNat A tr pub b false m % P
  busBound : ∀ b, busLoad A tr b < P

theorem Holds.toX {A : Air} {pub : List F} {tr : Trace} (H : Holds A pub tr) : HoldsX A pub tr :=
  ⟨H.pubLen, H.heightPos, H.heightLe, H.constr, fun b m _ => H.balance b m, H.busBound⟩

instance {A : Air} {pub : List F} {tr : Trace} : Coe (Holds A pub tr) (HoldsX A pub tr) := ⟨Holds.toX⟩

theorem HoldsX.toC {A : Air} {pub : List F} {tr : Trace} (H : HoldsX A pub tr) : HoldsC A pub tr :=
  ⟨H.constr⟩

section
variable {A : Air} {pub : List F} {tr : Trace} (H : HoldsX A pub tr)
include H

theorem table_constrX {t : Nat} (ht : t < A.tables.length) {r : Nat} (hr : r < tr.height t) :
    ∀ e ∈ (A.tables[t]'ht).constraints, e.eval (natRow (rowNat tr t r) (tr.row pub t r)) = 0 :=
  table_constrC H.toC ht hr

theorem table_constr_eqX {t : Nat} (ht : t < A.tables.length) (T : Table) (hT : A.tables[t]'ht = T)
    {r : Nat} (hr : r < tr.height t) :
    ∀ e ∈ T.constraints, e.eval (natRow (rowNat tr t r) (tr.row pub t r)) = 0 := by
  intro e he
  rw [← hT] at he
  exact table_constrX H ht hr e he

theorem busNat_ltX (b : Nat) (s : Bool) (m : List F)
    (hbit : ∀ o ∈ occs A tr pub, o.1 = b → o.2.1 = s → o.2.2.2 ≤ 1) :
    busNat A tr pub b s m < P := by
  have h1 : busNat A tr pub b s m ≤ ((occs A tr pub).filter fun o => o.1 = b ∧ o.2.1 = s ∧ o.2.2.1 = m).length := by
    unfold busNat
    have := sum_le_length (l := ((occs A tr pub).filter fun o => o.1 = b ∧ o.2.1 = s ∧ o.2.2.1 = m).map (·.2.2.2))
      (by
        intro a ha
        obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ha
        obtain ⟨ho, hf⟩ := List.mem_filter.mp ho
        simp only [decide_eq_true_eq] at hf
        exact hbit o ho hf.1 hf.2.1)
    simpa using this
  have h2 : ((occs A tr pub).filter fun o => o.1 = b ∧ o.2.1 = s ∧ o.2.2.1 = m).length ≤
      ((occs A tr pub).filter fun o => o.1 = b ∧ o.2.1 = s).length := by
    apply length_filter_mono
    intro x hx; simp only [decide_eq_true_eq] at hx ⊢; exact ⟨hx.1, hx.2.1⟩
  have h3 := length_filter_occs_le A tr pub b s
  have h4 := H.busBound b
  omega

/-- `lookup_sound` on a bus other than `extBus`. -/
theorem lookup_soundX (b : Nat) (hx : b ≠ extBus) (Q : List F → Prop)
    (hrecv : ∀ o ∈ occs A tr pub, o.1 = b → o.2.1 = false → o.2.2.2 ≠ 0 → Q o.2.2.1)
    (hsend : ∀ o ∈ occs A tr pub, o.1 = b → o.2.1 = true → o.2.2.2 ≤ 1)
    {o : Occ} (ho : o ∈ occs A tr pub) (hb : o.1 = b) (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    Q o.2.2.1 := by
  refine Classical.byContradiction fun hq => ?_
  have h0 : busNat A tr pub b false o.2.2.1 = 0 :=
    busNat_zero fun o' ho' hb' hs' hm' => Classical.byContradiction fun hc' => hq (hm' ▸ hrecv o' ho' hb' hs' hc')
  have hbal := H.balance b o.2.2.1 hx
  rw [h0] at hbal
  have hge := count_le_busNat ho hb hs rfl
  have hlt := busNat_ltX H b true o.2.2.1 hsend
  rw [Nat.mod_eq_of_lt hlt, Nat.zero_mod] at hbal
  omega

/-- `perm_exact` on a bus other than `extBus`. -/
theorem perm_exactX (b : Nat) (hx : b ≠ extBus)
    (hbit : ∀ o ∈ occs A tr pub, o.1 = b → o.2.2.2 ≤ 1) (m : List F) :
    busNat A tr pub b true m = busNat A tr pub b false m := by
  have h := H.balance b m hx
  rwa [Nat.mod_eq_of_lt (busNat_ltX H b true m (fun o ho hb _ => hbit o ho hb)),
    Nat.mod_eq_of_lt (busNat_ltX H b false m (fun o ho hb _ => hbit o ho hb))] at h

/-- `msgs_perm` on a bus other than `extBus`. -/
theorem msgs_permX (b : Nat) (hx : b ≠ extBus)
    (hbit : ∀ o ∈ occs A tr pub, o.1 = b → o.2.2.2 ≤ 1) :
    (msgs A tr pub b true).Perm (msgs A tr pub b false) := by
  rw [List.perm_iff_count]
  intro m
  rw [← busNat_eq_count b true (fun o ho hb _ => hbit o ho hb),
    ← busNat_eq_count b false (fun o ho hb _ => hbit o ho hb)]
  exact perm_exactX H b hx hbit m

theorem range16_valuesX {t : Nat} (ht : t < A.tables.length) (hT : A.tables[t]'ht = Range16.table) :
    tr.height t = 65536 ∧ ∀ r, r < tr.height t → rowNat tr t r Range16.val = r := by
  have hc := fun r hr => table_constrX H ht (r := r) hr
  rw [hT] at hc
  have hh := H.heightLe t ht
  have hpos := H.heightPos t ht
  unfold maxLogHeight at hh
  have hP' := P_val
  have hv : ∀ r, r < tr.height t → rowNat tr t r Range16.val = r := by
    simp only [Range16.val]
    intro r
    induction r with
    | zero =>
      intro h0
      have := hc 0 h0 (.first * v Range16.val) (by simp [Range16.table, Range16.constraints])
      simp only [Expr.eval, natRow, Trace.row, v, Range16.val, beq_self_eq_true, ite_true] at this
      exact natEq (by rw [show ((0 : Nat) : F) = 0 from rfl]; grind) (rowNat_lt _ _ _ _) (by decide)
    | succ r ih =>
      intro hr
      have ih' := ih (by omega)
      have := hc r (by omega) (.trans * (nv Range16.val - v Range16.val - 1))
        (by simp [Range16.table, Range16.constraints])
      have hne : (r + 1 == tr.height t) = false := by simp; omega
      simp only [Expr.eval, Expr.eval_sub', Expr.eval_nxt, Expr.eval_col, Expr.eval_ofNat', natRow, Trace.row, v, nv, Range16.val, Nat.mod_eq_of_lt hr, hne,
        Bool.false_eq_true, ite_false] at this
      have e : (tr.cell t (r + 1) 0) = ((r + 1 : Nat) : F) := by
        have h1 : ((rowNat tr t r 0 : Nat) : F) = (r : F) := by rw [ih']
        simp only [rowNat, Fp.cast_toNat] at h1
        rw [Lean.Grind.Semiring.natCast_add, ← h1]
        grind
      have := congrArg Fp.toNat e
      rw [Fp.toNat_cast_of_lt (by omega)] at this
      exact this
  refine ⟨?_, hv⟩
  have := hc (tr.height t - 1) (by omega) (.last * (v Range16.val - 65535))
    (by simp [Range16.table, Range16.constraints])
  simp only [Expr.eval, Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow, Trace.row, v, Range16.val, show tr.height t - 1 + 1 = tr.height t by omega,
    beq_self_eq_true, ite_true] at this
  have hv' := hv (tr.height t - 1) (by omega)
  have e : ((rowNat tr t (tr.height t - 1) 0 : Nat) : F) = ((65535 : Nat) : F) := by grind
  have := natEq e (rowNat_lt _ _ _ _) (by decide)
  simp only [Range16.val] at hv'
  omega

/-- `regG_r16_recv` for `HoldsX`. -/
theorem regG_r16_recvX {ti : Nat} (hA : RegAt A ti) :
    ∀ o ∈ occs A tr pub, o.1 = busR16 → o.2.1 = false →
      o.2.2.2 ≠ 0 → ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536 := by
  intro o ho hb hs hc
  obtain ⟨t, ht', r', hr', i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hb hs hc
  have hT : A.tables[t]'ht' = Range16.table := by
    rcases Classical.em (A.tables[t]'ht' = Range16.table) with he | hne
    · exact he
    · exact absurd (hA.r16only _ (List.getElem_mem _) hne i hi hb) (by simp [hs])
  obtain ⟨hh, hv⟩ := range16_valuesX H ht' hT
  rw [hT] at hi
  simp only [Range16.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
  subst hi
  refine ⟨((r' : Nat) : F), ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    rw [row_eq_natRow]
    simp only [v, Expr.eval_col, natRow, Range16.val]
    have e : rowNat tr t r' Range16.val = r' := hv r' hr'
    simp only [Range16.val] at e ⊢
    simpa using congrArg (fun n => ((n : Nat) : F)) e
  · rw [Fp.toNat_cast_of_lt (by rw [P_val]; omega)]; omega

/-- `lookup_r16G` for `HoldsX` (R16 is not the external bus). -/
theorem lookup_r16GX
    (hsend : ∀ o ∈ occs A tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1)
    (hrecv : ∀ o ∈ occs A tr pub, o.1 = busR16 → o.2.1 = false →
      o.2.2.2 ≠ 0 → ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536)
    {o : Occ} (ho : o ∈ occs A tr pub) (hb : o.1 = busR16)
    (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536 :=
  lookup_soundX H busR16 (by decide) (fun m => ∃ x : F, m = [x] ∧ x.toNat < 65536) hrecv
    (fun o' ho' hb' hs' => hsend o' ho' hb' hs') ho hb hs hc

end

end WasmBase
