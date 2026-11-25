import M5T1.ResumeC
import M5T1.T1ResumeData

/-!
# M5T1.T1Resume — non-vacuity of the resume leaf's boundary rules and appends on T1 (F-4)

T1's resume leaf (`run.sh … leaves`, lane D's base configuration; `logs/F4-leaves.txt`) has the
public values `pubN` (1,531 bytes: the env / totals groups, `B_in` 834 B at 247, `B_out` 450 B at
1081; the records in lane E's M12 shape with the Lean run's `chainD Ser.enc` accumulators,
`rtbnd.resume_f4`) and `RB` row 0 `rbRowN`. In the kernel:

* `t1_rb_constr` — **every `RB` constraint vanishes on every row** of a 4-row trace whose row 0 is
  the leaf's `RB` row (rows 1..3 zero), on the leaf's own public values: the boundary rules of
  `BndLay.rbCons` (phase / `inCall` / Wasm tag, `vmAcc = bdigest []` in and out, copies,
  `receiptIdx + 1`, `rPrepaid = rBurnt = rUsed = 0`, `RX`'s totals) are satisfiable by T1's
  records;
* `t1_res_bytes` — the public values are bytes;
* `t1_acc0`, `t1_acc1` — **the two accumulator appends**: the output record's `outcomeAcc` /
  `outRcpt0` is `bdigest (input accumulator ‖ item)` with `item` the Lean run's `Ser.enc` of the
  receipt's outcome / refund receipt (2 + 3 SHA-512 compressions in the kernel), i.e. `ACC`'s
  `AccOK` conclusion and the `RsStep` message shape hold together on T1;

Not checked here (stand-ins on T1, README §F-4): lane B's `STC` (`RsJoint`: the leaf's `STMQ` /
`STMA` traffic is answered by the `XTAPE` stand-in, the metas are zero bytes) and the receipt-step
contract `RsStep` on T1's run (a 27-GB kernel evaluation, lane E's `T1Run`).
-/

namespace M5T1.T1Resume

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.View M5T1 M5T1.BndLay M5T1.SegRt M5T1.EnterC
open M5T1.RbSem M5T1.AccDef M5T1.T1ResumeData
open NearSpec NearSpecV3 NearSpecV3.E2E NearSpecV3.E2E.Bnd

def t1ResPub : List Fp := pubN.map Fp.ofNat

/-- A 4-row trace with `RB` row 0 the leaf's row (every other cell `0`). -/
def t1ResTr : Trace Fp :=
  ⟨fun _ => 2, fun t r j => if t = 6 ∧ r = 0 then Fp.ofNat (rbRowN.getD j 0) else 0⟩

theorem mem_chunks {α : Type} (n : Nat) : ∀ (m : Nat) (l : List α), l.length ≤ n * m →
    ∀ e ∈ l, ∃ k < m, e ∈ (l.drop (n * k)).take n
  | 0, l, h, e, he => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this; simp at he
  | m + 1, l, h, e, he => by
    rw [← List.take_append_drop n l, List.mem_append] at he
    rcases he with he | he
    · exact ⟨0, by omega, by simpa using he⟩
    · obtain ⟨k, hk, he'⟩ := mem_chunks n m (l.drop n)
        (by rw [List.length_drop]; rw [Nat.mul_succ] at h; omega) e he
      refine ⟨k + 1, by omega, ?_⟩
      rwa [List.drop_drop, show n + n * k = n * (k + 1) by rw [Nat.mul_succ]; omega] at he'

/-! Row 0: the 853 `RB` constraints (F-5: + 342 for the input's `fin` record), by kernel evaluation
in chunks of 100. -/
theorem rb0_0 : ∀ e ∈ (Rb.table.constraints.drop 0).take 100, e.eval t1ResTr 6 0 t1ResPub = 0 := by
  decide +kernel
theorem rb0_1 : ∀ e ∈ (Rb.table.constraints.drop 100).take 100, e.eval t1ResTr 6 0 t1ResPub = 0 := by
  decide +kernel
theorem rb0_2 : ∀ e ∈ (Rb.table.constraints.drop 200).take 100, e.eval t1ResTr 6 0 t1ResPub = 0 := by
  decide +kernel
theorem rb0_3 : ∀ e ∈ (Rb.table.constraints.drop 300).take 100, e.eval t1ResTr 6 0 t1ResPub = 0 := by
  decide +kernel
theorem rb0_4 : ∀ e ∈ (Rb.table.constraints.drop 400).take 100, e.eval t1ResTr 6 0 t1ResPub = 0 := by
  decide +kernel
theorem rb0_5 : ∀ e ∈ (Rb.table.constraints.drop 500).take 100, e.eval t1ResTr 6 0 t1ResPub = 0 := by
  decide +kernel
theorem rb0_6 : ∀ e ∈ (Rb.table.constraints.drop 600).take 100, e.eval t1ResTr 6 0 t1ResPub = 0 := by
  decide +kernel
theorem rb0_7 : ∀ e ∈ (Rb.table.constraints.drop 700).take 100, e.eval t1ResTr 6 0 t1ResPub = 0 := by
  decide +kernel
theorem rb0_8 : ∀ e ∈ (Rb.table.constraints.drop 800).take 100, e.eval t1ResTr 6 0 t1ResPub = 0 := by
  decide +kernel

theorem t1_rb_row0 : ∀ e ∈ Rb.table.constraints, e.eval t1ResTr 6 0 t1ResPub = 0 := by
  intro e he
  obtain ⟨k, hk, he⟩ := mem_chunks 100 9 _ (by decide +kernel) e he
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rb0_0 e he
  · exact rb0_1 e he
  · exact rb0_2 e he
  · exact rb0_3 e he
  · exact rb0_4 e he
  · exact rb0_5 e he
  · exact rb0_6 e he
  · exact rb0_7 e he
  · exact rb0_8 e he

/-- Every `RB` constraint is `isFirst`-gated or the booleanity of a carry column. -/
def rowZeroOK : Expr → Bool
  | .mul .isFirst _ => true
  | .mul (.col _ false) (.add (.col _ false) (.neg (.const 1))) => true
  | _ => false

theorem rb_shapes : ∀ e ∈ Rb.table.constraints, rowZeroOK e = true := by decide +kernel

theorem rowZero {e : Expr} (h : rowZeroOK e = true) {r : Nat} (hr : r ≠ 0) :
    e.eval t1ResTr 6 r t1ResPub = 0 := by
  match e, h with
  | .mul .isFirst x, _ =>
    show (if r = 0 then (1 : Fp) else 0) * x.eval t1ResTr 6 r t1ResPub = 0
    simp only [hr, ite_false]
    exact Lean.Grind.Semiring.zero_mul _
  | .mul (.col j false) (.add (.col j' false) (.neg (.const 1))), _ =>
    show t1ResTr.cell 6 r j * _ = 0
    simp only [t1ResTr, hr, and_false, ite_false]
    exact Lean.Grind.Semiring.zero_mul _

/-- **Every `RB` constraint vanishes on every row** of the T1 trace. -/
theorem t1_rb_constr : ∀ r < t1ResTr.height 6, ∀ e ∈ Rb.table.constraints,
    e.eval t1ResTr 6 r t1ResPub = 0 := by
  intro r _ e he
  by_cases hr : r = 0
  · subst hr; exact t1_rb_row0 e he
  · exact rowZero (rb_shapes e he) hr

theorem t1_res_lt : ∀ x ∈ pubN, x < 256 := by decide +kernel

theorem t1_res_bytes : ∀ i < 1531, pv t1ResPub i < 256 := by
  intro i _
  simp only [pv, t1ResPub, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : pubN[i]? with
  | none => show (Fp.ofNat 0).toNat < 256; rw [Fp.toNat_ofNat]; decide
  | some x =>
    have hx := t1_res_lt x (List.mem_of_getElem? h)
    simp only [Option.map_some, Option.getD_some, Fp.toNat_ofNat]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hx

/-! ## The two accumulator appends -/

theorem t1_accIn0 : accIn t1ResPub 0 = bs accIn0N := by decide +kernel
theorem t1_accOut0 : accOut t1ResPub 0 = bs accOut0N := by decide +kernel
theorem t1_accIn1 : accIn t1ResPub 1 = bs accIn1N := by decide +kernel
theorem t1_accOut1 : accOut t1ResPub 1 = bs accOut1N := by decide +kernel

/-- The outcome append (2 compressions). -/
theorem t1_sha0 : bdigest (bs accIn0N ++ bs item0N) = bs accOut0N := by decide +kernel
/-- The refund-receipt append (3 compressions). -/
theorem t1_sha1 : bdigest (bs accIn1N ++ bs item1N) = bs accOut1N := by decide +kernel

theorem t1_acc0 : accOut t1ResPub 0 = bdigest (accIn t1ResPub 0 ++ bs item0N) := by
  rw [t1_accOut0, t1_accIn0, t1_sha0]
theorem t1_acc1 : accOut t1ResPub 1 = bdigest (accIn t1ResPub 1 ++ bs item1N) := by
  rw [t1_accOut1, t1_accIn1, t1_sha1]

#print axioms t1_rb_constr
#print axioms t1_res_bytes
#print axioms t1_acc0
#print axioms t1_acc1

end M5T1.T1Resume
