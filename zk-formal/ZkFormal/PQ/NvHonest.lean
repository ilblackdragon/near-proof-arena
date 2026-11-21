import ZkFormal.PQ.NvProg
import ZkFormal.PQ.NvHonestMem
import ZkFormal.PQ.NvHonestCheck0
import ZkFormal.PQ.NvHonestCheck1
import ZkFormal.PQ.NvHonestCheck2
import ZkFormal.PQ.NvHonestCheck3
import ZkFormal.PQ.NvHonestCheck4
import ZkFormal.PQ.NvHonestCheck5
import ZkFormal.PQ.NvHonestCheck6
import ZkFormal.PQ.NvHonestCheck7
import ZkFormal.PQ.NvHonestCheck8
import ZkFormal.PQ.NvHonestCheck9
import ZkFormal.PQ.NvHonestCheck10
import ZkFormal.PQ.NvHonestCheck11
import ZkFormal.PQ.NvHonestCheck12

/-!
# ZkFormal.PQ.NvHonest — non-vacuity on an honest NV trace

Lane E (E2E M11g, item 1), 2026-11-04.

M11f's non-vacuity was the all-zero trace, which satisfies `NvConstr ∧ MemBalance` but no
`PvdAt`. Here the trace is **honest**: `NvHonestExport.lean` is the NvAir trace (table 0) of a
small program run by the circuit's own trace generator (`NvCircuit::new(3, 12, 1)
.generate_program`, i.e. `nv_trace`), **proved and verified by the backend** (`prove_mats`) before
export (`nv-export/nv_export.rs`, `nv_export_trace`). The program (528 rows): 514 reserved
binding rows, the `Acc` row, two `Load` cells holding a statement digest exposed by two `PvD`
rows, `Const`/`Pv` (the level), `LoadF 5`, `Const 7`, `Add`, `LoadF 12`, and `assert_eq` of the
sum with `12` (`Sub` + `Zero`). 4,096 rows, 792 used.

## Proved on the honest trace (`hTr`, public values `hPubF`)

* `honest_constr`: **`NvConstr`** — all 548 exported constraints on all 4,096 rows: rows
  `0..791` and `4095` by kernel evaluation of the exported DAG (`NvDagEval.rowOK`, split over
  `NvHonestCheck{0..12}`), rows `792..4094` (zero, followed by zero) syntactically.
* `honest_mem`: **`MemBalance`** — the field balance of the mem bus over all rows.
* `honest_pvd`: **`PvdAt`** at rows 518 / 519 (addresses 516 / 517, halves 0 / 1).
* `honest_tape`: hence `nodeTape_of_pvd`'s hypotheses hold jointly, and its conclusion: the digest
  cells are the public statement digest.
* `honest_prog`: **`ProgBound`** for the exported program, `ProgWF`, the program's `AssertIn`
  pair, its cell equality, and `GlueByteBool` (no GLUE rows).

Not covered: the other three tables' traces (Sha512Air4, TableAir4, ByteAir; not exported), so the
balance of the buses NvAir shares (9, 11) is not checked here; `NvHold` as a whole is therefore
not exhibited, only the NvAir-local predicates the tape and assert lemmas consume.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace ZkFormal.PQ.NvHonest

open ZkFormal.Air ZkFormal.Algebra ZkFormal.PQ.NvAirExport ZkFormal.PQ.NvTape
open ZkFormal.PQ.NvDagEval ZkFormal.PQ.NvHonestRows ZkFormal.PQ.NvHonestExport ZkFormal.PQ.NvProg

set_option maxRecDepth 100000

/-! ## Zero rows -/

/-- Zero-ness ignoring public values and selectors: a column, a zero constant, a sum of zero
terms, a product with a zero factor. -/
def zeroAt' : Expr → Bool
  | .col _ _ => true
  | .const n => n == 0
  | .add a b => zeroAt' a && zeroAt' b
  | .mul a b => zeroAt' a || zeroAt' b
  | .neg a => zeroAt' a
  | _ => false

theorem zeroAt'_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp) (hz : ∀ c, tr.cell t r c = 0)
    (hz' : ∀ c, tr.cell t ((r + 1) % tr.height t) c = 0) :
    ∀ e, zeroAt' e = true → e.eval tr t r pub = 0
  | .col c nx, _ => by
    cases nx
    · exact hz c
    · exact hz' c
  | .const n, h => by
    have : n = 0 := by simpa [zeroAt'] using h
    subst this; rfl
  | .add a b, h => by
    simp only [zeroAt', Bool.and_eq_true] at h
    show a.eval tr t r pub + b.eval tr t r pub = 0
    rw [zeroAt'_eval tr t r pub hz hz' a h.1, zeroAt'_eval tr t r pub hz hz' b h.2]; decide
  | .mul a b, h => by
    simp only [zeroAt', Bool.or_eq_true] at h
    show a.eval tr t r pub * b.eval tr t r pub = 0
    rcases h with h | h
    · rw [zeroAt'_eval tr t r pub hz hz' a h]; grind
    · rw [zeroAt'_eval tr t r pub hz hz' b h]; grind
  | .neg a, h => by
    simp only [zeroAt'] at h
    show -(a.eval tr t r pub) = 0
    rw [zeroAt'_eval tr t r pub hz hz' a h]; decide
  | .pub _, h => by simp [zeroAt'] at h
  | .isFirst, h => by simp [zeroAt'] at h
  | .isLast, h => by simp [zeroAt'] at h
  | .isTransition, h => by simp [zeroAt'] at h

theorem zero_check' : nvConstraintIdx.all (fun j => j == 216 || zeroAt' (dag j)) = true := by
  decide +kernel

theorem hRows_len : hRows.length = 792 := by decide

theorem hRow_zero {r : Nat} (hr : 792 ≤ r) (c : Nat) : hTr.cell 0 r c = 0 := by
  show (((hRows.getD r []).getD c 0 : Nat) : Fp) = 0
  have : hRows.getD r [] = [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hRows_len]; exact hr)]; rfl
  rw [this]; rfl

/-- **Every exported constraint vanishes on a zero row followed by a zero row.** -/
theorem zero_row {r : Nat} (h1 : 792 ≤ r) (h2 : r + 1 < 4096) :
    ∀ j ∈ nvConstraintIdx, (dag j).eval hTr 0 r hPubF = 0 := by
  have hz := hRow_zero (r := r) h1
  have hz' : ∀ c, hTr.cell 0 ((r + 1) % hTr.height 0) c = 0 := by
    rw [hHeight, Nat.mod_eq_of_lt h2]; exact hRow_zero (by omega)
  intro j hj
  have hc := List.all_eq_true.1 zero_check' j hj
  by_cases e : j = 216
  · subst e
    rw [dag_stage, ev_stage_raw]
    simp only [cv, hz, hz']
    have : polyV (stageV 0 0 0 0 0 + -stageV 0 0 0 0 0) = 0 := by decide
    rw [this]; grind
  · have : zeroAt' (dag j) = true := by
      simp only [Bool.or_eq_true, beq_iff_eq, e, false_or] at hc; exact hc
    exact zeroAt'_eval hTr 0 r hPubF hz hz' _ this

/-! ## `NvConstr` on the honest trace -/

theorem used_rows : ∀ r, r < 792 → rowOK (hEnv r) = true := by
  intro r hr
  by_cases h0 : r < 64
  · exact NvHonestCheck0.rows r (by omega) h0
  by_cases h1 : r < 128
  · exact NvHonestCheck1.rows r (by omega) h1
  by_cases h2 : r < 192
  · exact NvHonestCheck2.rows r (by omega) h2
  by_cases h3 : r < 256
  · exact NvHonestCheck3.rows r (by omega) h3
  by_cases h4 : r < 320
  · exact NvHonestCheck4.rows r (by omega) h4
  by_cases h5 : r < 384
  · exact NvHonestCheck5.rows r (by omega) h5
  by_cases h6 : r < 448
  · exact NvHonestCheck6.rows r (by omega) h6
  by_cases h7 : r < 512
  · exact NvHonestCheck7.rows r (by omega) h7
  by_cases h8 : r < 576
  · exact NvHonestCheck8.rows r (by omega) h8
  by_cases h9 : r < 640
  · exact NvHonestCheck9.rows r (by omega) h9
  by_cases h10 : r < 704
  · exact NvHonestCheck10.rows r (by omega) h10
  by_cases h11 : r < 768
  · exact NvHonestCheck11.rows r (by omega) h11
  exact NvHonestCheck12.rows r (by omega) hr

/-- **All 548 exported NvAir constraints hold on every row of the honest trace.** -/
theorem honest_constr : NvConstr hTr 0 hPubF := by
  intro r hr j hj
  rw [hHeight] at hr
  by_cases hu : r < 792
  · exact rowOK_sound (hEnv r) hTr r hPubF (hAgrees r) (used_rows r hu) j hj
  by_cases hl : r = 4095
  · subst hl
    exact rowOK_sound (hEnv 4095) hTr 4095 hPubF (hAgrees 4095) NvHonestCheck12.lastRow j hj
  · exact zero_row (by omega) (by omega) j hj

/-! ## The program, `PvdAt`, the tape -/

/-- The exported program as `Instr`s. -/
def hProgI : List Instr := hProg.map fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩

theorem getD_get {α : Type} (l : List α) (d : α) {i : Nat} (h : i < l.length) :
    l.getD i d = l[i] := by simp [List.getD_eq_getElem?_getD, h]

theorem hProg_len : hProgI.length = 528 := by decide

/-- **Program binding holds on the honest trace** (its program columns are the program's words). -/
theorem honest_prog : ProgBound hTr hProgI := by
  refine ⟨by rw [hProg_len, hHeight]; decide, ?_⟩
  have h : ∀ y, y < 528 → ProgRow hTr y (hProgI.getD y ⟨0, 0, 0, 0, 0⟩) := by
    unfold ProgRow; decide +kernel
  intro y hy
  have := h y (by rw [hProg_len] at hy; exact hy)
  rwa [getD_get _ _ hy] at this

theorem honest_wf : ProgWF hProgI := by
  have h : hProgI.all (fun i => decide (i.op < 40 ∧ i.b < 2 ^ 24)) = true := by decide +kernel
  intro i hi
  exact of_decide_eq_true (List.all_eq_true.1 h i hi)

/-- The program's two `PvD` rows and its `assert_eq` (rows 526 `Sub 524 525`, 527 `Zero 526`). -/
theorem honest_rows : hProgI.getD 518 ⟨0, 0, 0, 0, 0⟩ = ⟨31, 516, 0, 0, 0⟩ ∧
    hProgI.getD 519 ⟨0, 0, 0, 0, 0⟩ = ⟨31, 517, 0, 1, 0⟩ ∧
    hProgI.getD 526 ⟨0, 0, 0, 0, 0⟩ = ⟨3, 524, 525, 0, 0⟩ ∧
    hProgI.getD 527 ⟨0, 0, 0, 0, 0⟩ = ⟨16, 526, 0, 0, 0⟩ := by decide +kernel

theorem honest_assertIn : AssertIn hProgI 524 525 := by
  have h := honest_rows
  refine ⟨526, 527, by rw [hProg_len]; decide, by rw [hProg_len]; decide, ?_, ?_, by decide,
    by decide, by decide⟩
  · rw [← getD_get _ ⟨0, 0, 0, 0, 0⟩]; exact h.2.2.1
  · rw [← getD_get _ ⟨0, 0, 0, 0, 0⟩]; exact h.2.2.2

/-- The asserted cells are equal on the honest trace (`5 + 7 = 12`). -/
theorem honest_celleq : CellEq hTr 524 525 := by unfold CellEq; decide +kernel

/-- **`PvdAt` holds at the program's two `PvD` rows.** -/
theorem honest_pvd : PvdAt hTr 0 518 516 0 ∧ PvdAt hTr 0 519 517 1 := by
  refine ⟨⟨by rw [hHeight]; decide, by decide, by decide +kernel, by decide +kernel, by decide,
    by decide, by decide⟩, ⟨by rw [hHeight]; decide, by decide, by decide +kernel,
    by decide +kernel, by decide, by decide, by decide⟩⟩

/-- **The tape lemma's hypotheses hold jointly on the honest trace**, and its conclusion: the
digest cells read by the two `PvD` rows are the public statement digest. -/
theorem honest_tape : NvConstr hTr 0 hPubF ∧ MemBalance hTr 0 hPubF ∧ hTr.height 0 ≤ 2 ^ 24 ∧
    PvdAt hTr 0 518 516 0 ∧ PvdAt hTr 0 519 517 1 ∧
    digCells hTr 0 516 517 = pvDigest hPubF :=
  ⟨honest_constr, NvHonestMem.honest_mem, by rw [hHeight]; decide, honest_pvd.1, honest_pvd.2,
    digCells_eq honest_constr NvHonestMem.honest_mem (by rw [hHeight]; decide) honest_pvd.1
      honest_pvd.2 (by decide) (by decide)⟩

/-- `GlueByteBool` holds on the honest trace (it has no GLUE rows). -/
theorem honest_glue : GlueByteBool hTr hPubF := by
  have hu : ∀ r, r < 792 → hTr.cell 0 r 2 = 0 := by decide +kernel
  intro r hr h1
  rw [hHeight] at hr
  have : hTr.cell 0 r 2 = 0 := by
    by_cases h : r < 792
    · exact hu r h
    · exact hRow_zero (by omega) 2
  rw [show cv hTr 0 r 2 = hTr.cell 0 r 2 from rfl, this] at h1
  exact absurd h1 (by decide)

#print axioms honest_constr
#print axioms honest_prog
#print axioms honest_tape
#print axioms honest_glue
#print axioms honest_celleq

end ZkFormal.PQ.NvHonest
