import M5T1.SeC
import M5T1.T1SeData
import M5T1.T1Resume

/-!
# M5T1.T1Se — non-vacuity of the STATE engine half's rules on T1 (F-5)

T1's three STATE engine-half leaves (`segen.py`, lane D's base configuration; `logs/F5-leaves.txt`)
have the public values `pubA` / `pubB` / `pubF` (900 bytes: lane I's chain records c1 → c2, c7 → c8,
c8 → c9, `BndRec.encode`; F-7: the M14 chain) and `SE` row 0 `rowA` / `rowB` / `rowF` (the `STMQ`/`STMA`
metas; F-7: and the opening rows' columns — the opened `stRoot`, the remainder digests, `fin`). In the
kernel:

* `t1_se_constr` — **every `SE` constraint vanishes on every row** of each leaf's 4-row trace (row 0
  the leaf's row, the others zero), on the leaf's own public values: `SeSem.se_out`'s premises on
  the circuit side (phase 1, out of a call, the copies, `vmAcc = bdigest []`, `rPrepaid = rBurnt =
  rUsed = 0`, `gasUsed = gasBurnt`) are satisfiable by T1's records;
* `t1_se_bytes` — the public values are bytes;
* `t1_se_chain` — the leaves chain: seg B's output record is the finalize leaf's input record
  byte for byte (c8); F-7 (M14): seg B moves the record (c7 ≠ c8: the position tag and `rest`).

Not checked here (stand-ins on T1): the step contract `SeC.SeStep` (no STATE engine rows) and the
`STC` join (lane B's state halves are separate proofs whose `htape.json` traffic equals these
leaves' `XTAPE`, `stmcheck.py`).
-/

namespace M5T1.T1Se

open ZkFormal.Air ZkFormal.Algebra M5T1 M5T1.BndLay M5T1.SegRt M5T1.T1SeData

def pubF' (l : List Nat) : List Fp := l.map Fp.ofNat

/-- A 4-row trace with `SE` row 0 the leaf's row (every other cell `0`). -/
def trOf (row : List Nat) : Trace Fp :=
  ⟨fun _ => 2, fun t r j => if t = 0 ∧ r = 0 then Fp.ofNat (row.getD j 0) else 0⟩

/-- Chunk `k` (100 constraints) of `SE` vanishes on row 0. -/
def OkChunk (pub row : List Nat) (k : Nat) : Prop :=
  ∀ e ∈ (Se.table.constraints.drop (100 * k)).take 100, e.eval (trOf row) 0 0 (pubF' pub) = 0

theorem len_cons : Se.table.constraints.length ≤ 100 * 4 := by decide +kernel

theorem row0_of {pub row : List Nat} (h0 : OkChunk pub row 0) (h1 : OkChunk pub row 1)
    (h2 : OkChunk pub row 2) (h3 : OkChunk pub row 3) :
    ∀ e ∈ Se.table.constraints, e.eval (trOf row) 0 0 (pubF' pub) = 0 := by
  intro e he
  obtain ⟨k, hk, he⟩ := T1Resume.mem_chunks 100 4 _ len_cons e he
  have : OkChunk pub row k := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> assumption
  exact this e he

theorem a0 : ∀ e ∈ (Se.table.constraints.drop 0).take 100,
    e.eval (trOf rowA) 0 0 (pubF' pubA) = 0 := by decide +kernel
theorem a1 : ∀ e ∈ (Se.table.constraints.drop 100).take 100,
    e.eval (trOf rowA) 0 0 (pubF' pubA) = 0 := by decide +kernel
theorem a2 : ∀ e ∈ (Se.table.constraints.drop 200).take 100,
    e.eval (trOf rowA) 0 0 (pubF' pubA) = 0 := by decide +kernel
theorem a3 : ∀ e ∈ (Se.table.constraints.drop 300).take 100,
    e.eval (trOf rowA) 0 0 (pubF' pubA) = 0 := by decide +kernel
theorem b0 : ∀ e ∈ (Se.table.constraints.drop 0).take 100,
    e.eval (trOf rowB) 0 0 (pubF' pubB) = 0 := by decide +kernel
theorem b1 : ∀ e ∈ (Se.table.constraints.drop 100).take 100,
    e.eval (trOf rowB) 0 0 (pubF' pubB) = 0 := by decide +kernel
theorem b2 : ∀ e ∈ (Se.table.constraints.drop 200).take 100,
    e.eval (trOf rowB) 0 0 (pubF' pubB) = 0 := by decide +kernel
theorem b3 : ∀ e ∈ (Se.table.constraints.drop 300).take 100,
    e.eval (trOf rowB) 0 0 (pubF' pubB) = 0 := by decide +kernel
theorem f0 : ∀ e ∈ (Se.table.constraints.drop 0).take 100,
    e.eval (trOf rowF) 0 0 (pubF' pubF) = 0 := by decide +kernel
theorem f1 : ∀ e ∈ (Se.table.constraints.drop 100).take 100,
    e.eval (trOf rowF) 0 0 (pubF' pubF) = 0 := by decide +kernel
theorem f2 : ∀ e ∈ (Se.table.constraints.drop 200).take 100,
    e.eval (trOf rowF) 0 0 (pubF' pubF) = 0 := by decide +kernel
theorem f3 : ∀ e ∈ (Se.table.constraints.drop 300).take 100,
    e.eval (trOf rowF) 0 0 (pubF' pubF) = 0 := by decide +kernel

/-- Every `SE` constraint is `isFirst`-gated. -/
def gated : Expr → Bool
  | .mul .isFirst _ => true
  | _ => false

theorem se_gated : ∀ e ∈ Se.table.constraints, gated e = true := by decide +kernel

theorem rowZero {e : Expr} (h : gated e = true) {r : Nat} (hr : r ≠ 0) (row : List Nat) (pub : List Fp) :
    e.eval (trOf row) 0 r pub = 0 := by
  match e, h with
  | .mul .isFirst x, _ =>
    show (if r = 0 then (1 : Fp) else 0) * x.eval (trOf row) 0 r pub = 0
    simp only [hr, ite_false]
    exact Lean.Grind.Semiring.zero_mul _

theorem all_rows {pub row : List Nat} (h : ∀ e ∈ Se.table.constraints, e.eval (trOf row) 0 0 (pubF' pub) = 0) :
    ∀ r < (trOf row).height 0, ∀ e ∈ Se.table.constraints, e.eval (trOf row) 0 r (pubF' pub) = 0 := by
  intro r _ e he
  by_cases hr : r = 0
  · subst hr; exact h e he
  · exact rowZero (se_gated e he) hr row _

/-- **Every `SE` constraint vanishes on every row** of T1's three STATE engine-half traces. -/
theorem t1_se_constr :
    (∀ r < (trOf rowA).height 0, ∀ e ∈ Se.table.constraints, e.eval (trOf rowA) 0 r (pubF' pubA) = 0) ∧
    (∀ r < (trOf rowB).height 0, ∀ e ∈ Se.table.constraints, e.eval (trOf rowB) 0 r (pubF' pubB) = 0) ∧
    (∀ r < (trOf rowF).height 0, ∀ e ∈ Se.table.constraints, e.eval (trOf rowF) 0 r (pubF' pubF) = 0) :=
  ⟨all_rows (row0_of a0 a1 a2 a3), all_rows (row0_of b0 b1 b2 b3), all_rows (row0_of f0 f1 f2 f3)⟩

theorem t1_se_bytes : (∀ x ∈ pubA, x < 256) ∧ (∀ x ∈ pubB, x < 256) ∧ (∀ x ∈ pubF, x < 256) := by
  decide +kernel

/-- **The leaves chain**: seg B's output record is the finalize leaf's input record (c8). F-7 (M14): seg B
is no longer the identity on the record (c7 and c8 differ in `stRoot`: tags 7 → 8, lane E's `rest`). -/
theorem t1_se_chain : pubB.drop 450 = pubF.take 450 ∧ pubB.take 450 ≠ pubB.drop 450 := by
  decide +kernel

#print axioms t1_se_constr
#print axioms t1_se_bytes
#print axioms t1_se_chain

end M5T1.T1Se
