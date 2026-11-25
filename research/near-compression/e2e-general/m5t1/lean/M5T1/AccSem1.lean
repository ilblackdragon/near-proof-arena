import M5T1.AccDef
import M5T1.MsgRowSch

/-!
# M5T1.AccSem1 — `ACC` row facts and bus facts (F-4, part of `AccSem`)

Natural-number semantics of the `ACC` (table 7) constraints on any `Holds (fullAir …)` trace, and
the bus facts `AccSem` needs: a send has a receiver (`send_receiver`), the only `ACCD` receiver is
`ACC`'s `lst` row, the only `IF384` sender is the chip stub (table 8).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace M5T1.AccSem

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound ZkFormal.Sha.View M5T1 M5T1.Bus M5T1.MsgRow
open M5T1.AccDef

abbrev Tp := List (Nat × Bool × List Nat)

/-! ## Expression evaluation through the DSL instances -/

section
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

@[simp] theorem evAdd (a b : Expr) : ev tr t r pub (a + b) = (ev tr t r pub a + ev tr t r pub b) % 2013265921 :=
  ev_add a b
@[simp] theorem evMul (a b : Expr) : ev tr t r pub (a * b) = ev tr t r pub a * ev tr t r pub b % 2013265921 :=
  ev_mul a b
@[simp] theorem evSub (a b : Expr) :
    ev tr t r pub (a - b) = (ev tr t r pub a + (2013265921 - ev tr t r pub b) % 2013265921) % 2013265921 := by
  show ev tr t r pub (.add a (.neg b)) = _
  simp
@[simp] theorem evK (v : Nat) : ev tr t r pub (K v) = v % 2013265921 := ev_const v
@[simp] theorem evOne : ev tr t r pub (1 : Expr) = 1 := by
  show ev tr t r pub (.const 1) = 1; simp
@[simp] theorem evZero : ev tr t r pub (0 : Expr) = 0 := by
  show ev tr t r pub (.const 0) = 0; simp
theorem evAc (s : String) (j : Nat) : ev tr 7 r pub (Acc.c s j) = accC tr r s j := rfl
theorem evAn {s : String} {j : Nat} (h : r + 1 < tr.height 7) :
    ev tr 7 r pub (Acc.n s j) = accC tr (r + 1) s j := by
  show ((tr.cell 7 ((r + 1) % tr.height 7) _)).toNat = _
  rw [Nat.mod_eq_of_lt h]; rfl
theorem evFirst0 : ev tr t 0 pub .isFirst = 1 := rfl
theorem evFirstS (h : r ≠ 0) : ev tr t r pub .isFirst = 0 := by
  show (Expr.eval .isFirst tr t r pub).toNat = 0
  simp only [Expr.eval, Expr.evalWith, rowEnv, h, ite_false]; rfl
theorem evTrans (h : r + 1 < tr.height t) : ev tr t r pub .isTransition = 1 := by
  show (Expr.eval .isTransition tr t r pub).toNat = 1
  simp only [Expr.eval, Expr.evalWith, rowEnv, show ¬ (r + 1 = tr.height t) by omega, ite_false]; rfl
theorem evPub (i : Nat) : ev tr t r pub (.pub i) = SegRt.pv pub i := rfl

theorem accC_lt (s : String) (j : Nat) : accC tr r s j < 2013265921 := Fp.toNat_lt _

/-- A gated difference: `g = 1` and `g · (a − b) = 0` give `a = b`. -/
theorem gate_eq {g a b : Expr} (hg : ev tr t r pub g = 1) (h : ev tr t r pub (g * (a - b)) = 0) :
    ev tr t r pub a = ev tr t r pub b := by
  have ha := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) a
  have hb := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) b
  rw [evMul, hg, Nat.one_mul, evSub] at h
  omega

/-- A boolean: `x · (x − 1) = 0`. -/
theorem bool_le {x : Expr} (h : ev tr t r pub (bool x) = 0) : ev tr t r pub x ≤ 1 := by
  unfold bool at h
  have hx := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) x
  rcases ev_mul_eq_zero (a := x) (b := x - 1) h with h | h
  · omega
  · simp only [evSub, evOne] at h; omega
end

/-! ## Bus facts -/

section
variable {A : Air} {pub : List Fp} {tr : Trace Fp}

/-- **A send is matched by a receive** (the dual of `Bus.recv_sender`). -/
theorem send_receiver (H : Holds A pub tr) {t : Nat} (ht : t < A.tables.length) {r : Nat}
    (hr : r < tr.height t) {i : Interaction} (hi : i ∈ (A.tables[t]'ht).interactions)
    (hs : i.send = true) (hm : 0 < i.multNat tr t r pub) :
    ∃ t' r', ∃ ht' : t' < A.tables.length, r' < tr.height t' ∧
      ∃ i' ∈ (A.tables[t']'ht').interactions, i'.bus = i.bus ∧ i'.send = false ∧
        i'.msgVal tr t' r' pub = i.msgVal tr t r pub ∧ 0 < i'.multNat tr t' r' pub := by
  classical
  have hsend : 0 < busCount A tr pub i.bus true (i.msgVal tr t r pub) := by
    rw [ZkFormal.Udr.Np.busCount_eq]
    refine Nat.lt_of_lt_of_le ?_ (le_sum_mem _ _ (List.mem_range.2 ht))
    rw [ZkFormal.Udr.Np.tableOf_lt ht, ZkFormal.Udr.Np.tableBusCount_eq]
    refine Nat.lt_of_lt_of_le ?_ (le_sum_mem _ _ (List.mem_range.2 hr))
    refine Nat.lt_of_lt_of_le ?_ (le_sum_mem _ _ hi)
    simp only [hs, and_self, ite_true]
    exact hm
  rw [H.balance, ZkFormal.Udr.Np.busCount_eq] at hsend
  obtain ⟨t', ht', h1⟩ := sum_pos_mem _ _ hsend
  have ht'' := List.mem_range.1 ht'
  rw [ZkFormal.Udr.Np.tableOf_lt ht'', ZkFormal.Udr.Np.tableBusCount_eq] at h1
  obtain ⟨r', hr', h2⟩ := sum_pos_mem _ _ h1
  obtain ⟨i', hi', h3⟩ := sum_pos_mem _ _ h2
  refine ⟨t', r', ht'', List.mem_range.1 hr', i', hi', ?_⟩
  by_cases hc : i'.bus = i.bus ∧ i'.send = false ∧ i'.msgVal tr t' r' pub = i.msgVal tr t r pub
  · exact ⟨hc.1, hc.2.1, hc.2.2, by simpa [hc] using h3⟩
  · simp [hc] at h3
end

/-- A table that never receives on bus `b`. -/
def NoRecv (T : Table) (b : Nat) : Bool := T.interactions.all fun i => !(i.bus == b && !i.send)

/-- **Premise** on a public tape: it receives nothing on bus `b`. -/
def NoRecvOn (b : Nat) (tape : Tp) : Prop := ∀ e ∈ tape, e.1 = b → e.2.1 = true

theorem noRecv_spec {T : Table} {b : Nat} (h : NoRecv T b = true) {i : Interaction}
    (hi : i ∈ T.interactions) (hb : i.bus = b) (hs : i.send = false) : False := by
  unfold NoRecv at h
  have := List.all_eq_true.1 h i hi
  simp [hb, hs] at this

theorem tape_receiver {b : Nat} {tape : Tp} (h : NoRecvOn b tape) {i : Interaction}
    (hi : i ∈ (tapeTable tape).interactions) (hb : i.bus = b) (hs : i.send = false) : False := by
  simp only [tapeTable, List.mem_map] at hi
  obtain ⟨e, he, rfl⟩ := hi
  have := h e he hb
  simp only at hs; rw [this] at hs; cases hs

/-- The `ACCD` receive of `ACC`. -/
def accdRcv : Interaction := rcv B_ACCD (Acc.c "lst") [Acc.c "hid"]

theorem acc_accd : ∀ i ∈ Acc.table.interactions, i.bus = B_ACCD → i = accdRcv := by decide +kernel

section
variable {tape xtape : Tp}

theorem tbl_eq (t : Nat) (ht : t < (fullAir tape xtape).tables.length) :
    (fullAir tape xtape).tables[t]'ht = ([shaTable, Rng.table, Scht.table, Msg.table, Dg.table,
      Rx.table, Rb.table, Acc.table, chipStub, tapeTable tape, tapeTable xtape].getD t default) := by
  simp only [fullAir_tables] at ht ⊢
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; rfl

/-- **The only `ACCD` receiver is `ACC`'s `lst` receive.** -/
theorem accd_receiver (hd1 : NoRecvOn B_ACCD tape) (hd2 : NoRecvOn B_ACCD xtape) {t : Nat}
    (ht : t < (fullAir tape xtape).tables.length) {i : Interaction}
    (hi : i ∈ ((fullAir tape xtape).tables[t]'ht).interactions) (hb : i.bus = B_ACCD)
    (hs : i.send = false) : t = 7 ∧ i = accdRcv := by
  have h11 : t < 11 := fullAir_len (tape := tape) (xtape := xtape) ▸ ht
  rw [tbl_eq t ht] at hi
  obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | t := t
  · exact (noRecv_spec (by decide +kernel : NoRecv shaTable B_ACCD = true) hi hb hs).elim
  · exact (noRecv_spec (by decide +kernel : NoRecv Rng.table B_ACCD = true) hi hb hs).elim
  · exact (noRecv_spec (by decide +kernel : NoRecv Scht.table B_ACCD = true) hi hb hs).elim
  · exact (noRecv_spec (by decide +kernel : NoRecv Msg.table B_ACCD = true) hi hb hs).elim
  · exact (noRecv_spec (by decide +kernel : NoRecv Dg.table B_ACCD = true) hi hb hs).elim
  · exact (noRecv_spec (by decide +kernel : NoRecv Rx.table B_ACCD = true) hi hb hs).elim
  · exact (noRecv_spec (by decide +kernel : NoRecv Rb.table B_ACCD = true) hi hb hs).elim
  · exact ⟨rfl, acc_accd i hi hb⟩
  · exact (noRecv_spec (by decide +kernel : NoRecv chipStub B_ACCD = true) hi hb hs).elim
  · exact (tape_receiver hd1 hi hb hs).elim
  · exact (tape_receiver hd2 hi hb hs).elim
  · omega

/-- **The only `IF384` sender is the chip stub** (table 8), with its one interaction. -/
theorem if_sender (hi1 : NoSendOn B_IF384 tape) (hi2 : NoSendOn B_IF384 xtape) {t : Nat}
    (ht : t < (fullAir tape xtape).tables.length) {i : Interaction}
    (hi : i ∈ ((fullAir tape xtape).tables[t]'ht).interactions) (hb : i.bus = B_IF384)
    (hs : i.send = true) : t = 8 ∧ i = stubIx := by
  have h11 : t < 11 := fullAir_len (tape := tape) (xtape := xtape) ▸ ht
  rw [tbl_eq t ht] at hi
  obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | t := t
  · exact (noSend_spec (by decide +kernel : NoSend shaTable B_IF384 = true) hi hb hs).elim
  · exact (noSend_spec (by decide +kernel : NoSend Rng.table B_IF384 = true) hi hb hs).elim
  · exact (noSend_spec (by decide +kernel : NoSend Scht.table B_IF384 = true) hi hb hs).elim
  · exact (noSend_spec (by decide +kernel : NoSend Msg.table B_IF384 = true) hi hb hs).elim
  · exact (noSend_spec (by decide +kernel : NoSend Dg.table B_IF384 = true) hi hb hs).elim
  · exact (noSend_spec (by decide +kernel : NoSend Rx.table B_IF384 = true) hi hb hs).elim
  · exact (noSend_spec (by decide +kernel : NoSend Rb.table B_IF384 = true) hi hb hs).elim
  · exact (noSend_spec (by decide +kernel : NoSend Acc.table B_IF384 = true) hi hb hs).elim
  · exact ⟨rfl, List.mem_singleton.1 hi⟩
  · exact (tape_sender hi1 hi hb hs).elim
  · exact (tape_sender hi2 hi hb hs).elim
  · omega
end

end M5T1.AccSem
