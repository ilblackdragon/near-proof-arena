import ZkFormal.PQ.NvAirExport
import ZkFormal.PQ.E2ENode

/-!
# ZkFormal.PQ.NvTape — `NodeTape` from the exported NvAir (E2E-M11f, item 2)

`E2ENode.NodeExec` asks that every trace of the pinned NV circuit satisfy four components; the
third, **`NodeTape`**, says the public statement digest the decode reads (`pubDig pub`) is the
digest the program computed (`R.outDig`). This file proves it from the **exported** NvAir
(`NvAirExport.lean`, generated from the e2e-tree stack by `nv-export/setup.sh`): the program's
two `PvD` rows read the digest cells from memory and constrain them to the public values, and the
memory bus makes those reads see the cells the program wrote.

## What is modelled, from the export

* `dag j`: the exported DAG node `j` as a `ZkFormal.Air.Expr` (`sub a b` ↦ `a + (-b)`). Every
  expression below is identified with its exported node by `decide` (`dag_*` lemmas), so the
  constraints used are the circuit's own, not a transcription.
* `NvConstr tr t pub`: every exported constraint (`nvConstraintIdx`, 548) vanishes on every row
  of table `t`.
* `MemBalance tr t pub`: the **field** LogUp balance of the memory bus (bus 3) over NvAir's rows:
  for every message `m`, the sum of the counts of the three exported mem interactions whose
  message evaluates to `m` is `0` in `Fp`. The counts are field elements (the ALU key side has
  count `−ka·mult + kb`, merged with a BIND lookup): `ZkFormal.Air.Interaction` (bit-decomposed
  natural multiplicities with a send flag) cannot express them, so `HoldsLogUp` over a
  `ZkFormal.Air` transcription is not the circuit's predicate; this file uses the backend's
  semantics directly.
* **Bus subset (vacuity guard).** Bus 3 is used by NvAir only (`busUsers`, from the exporter's
  keygen listing), so the global LogUp balance of bus 3 is `MemBalance` (`memBalance_of_global`).
  The tables needed to balance **all** of NvAir's buses are exactly NvAir, Sha512Air4, ByteAir
  and TableAir4 (`nv_closure`, by `decide`): a `Pin.air` with fewer tables makes `HoldsLogUp
  Pin.air` unsatisfiable for honest traces, and one with these four is `NvPinned`'s shape.

## Proved

* `y_row`: on every role row, `y = r` (from the first-row, transition, padding and stage
  constraints: role rows form a prefix).
* `mem_slots`: every mem-bus entry of every row is either an ALU key `(y_r, c_r)` or has count
  `0` or `1` (flags boolean and exclusive; the ALU selector halves one-hot).
* `hit` / `pvd_read`: a read `(addr, v)` with count `1` is matched by an ALU row `r` with
  `y_r = addr`, `c_r = v` (LogUp balance in the field with fewer than `p` entries), hence
  (`y_row`) row `addr` has `c = v`: **memory consistency**.
* `pvd_cells`: if rows `dlo`, `dhi` are `PvD` rows reading addresses `alo`, `ahi` (`P2` = 0 / 1),
  then the cells of rows `alo`, `ahi` are the public values 1..13 and 13..19 (and `0` above
  limb 6 in the high cell).
* `nodeTape_of_pvd`: `E2ENode.NodeTape` for a decode whose `outDig` reads those cells.
* `zero_holds`: `NvConstr ∧ MemBalance` is satisfiable (the all-zero trace; all 548 exported
  constraints checked, the stage constraint by evaluation). It does not exercise `PvdAt`.

## Premises not discharged here

* `PvdAt` (which rows are `PvD` rows, with which `P0`, `P2`): the program premise. It follows
  from program binding (`NvProgramTape`: the BIND/`Acc` evaluation of `P0..P3`) and the op decode
  (`P1 = op·2^24 + B`, `B` range-checked on the byte bus): both open.
* The LogUp field balance itself is the extractor's output modulo `gkrBad` (as `HoldsLogUp`).
* Heights: `tr.height t ≤ 2^24` (`ADDR_BITS`), so `3·height < p`.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace ZkFormal.PQ.NvTape

open ZkFormal.Air ZkFormal.Algebra ZkFormal.PQ.NvAirExport

set_option maxRecDepth 100000

/-! ## The exported DAG as expressions -/

def node (i : Nat) : DagNode := nvNodes.getD i (.k 0)

/-- Node `i` as an expression (children have smaller indices; `f` is fuel). -/
def toExpr : Nat → Nat → Expr
  | 0, _ => .const 0
  | f + 1, i =>
    match node i with
    | .v c nx => .col c nx
    | .p j => .pub j
    | .k n => .const n
    | .add a b => .add (toExpr f a) (toExpr f b)
    | .sub a b => .add (toExpr f a) (.neg (toExpr f b))
    | .mul a b => .mul (toExpr f a) (toExpr f b)
    | .neg a => .neg (toExpr f a)
    | .first => .isFirst
    | .last => .isLast
    | .trans => .isTransition

/-- **The exported node `i`.** -/
def dag (i : Nat) : Expr := toExpr (i + 1) i

/-! ## Column map (`uair.rs`: `NvCommon` then the ALU pool `AbCols`) -/

abbrev col (c : Nat) : Expr := .col c false
abbrev colN (c : Nat) : Expr := .col c true
abbrev esub (a b : Expr) : Expr := .add a (.neg b)

/-- `ka kb kg kh ks` = 0..4, `y` = 5, `P0..P3` = 6..9; ALU pool: `a` 10..21, `b` 22..33, `h`
34..41, `wit` 42, `mult` 43, `c` 46..57, `g` 58..62. -/
def cY : Nat := 5
def cP0 : Nat := 6
def cP2 : Nat := 8
def cA : Nat := 10
def cMult : Nat := 43
def cC : Nat := 46

def ksumE (nx : Bool) : Expr :=
  .add (.add (.add (.add (.col 0 nx) (.col 1 nx)) (.col 2 nx)) (.col 3 nx)) (.col 4 nx)

def stageE (nx : Bool) : Expr :=
  .add (.add (.add (.add (.col 1 nx) (.mul (.col 2 nx) (.const 2))) (.mul (.col 3 nx) (.const 3)))
    (.mul (.col 4 nx) (.const 4))) (.mul (esub (.const 1) (ksumE nx)) (.const 5))

def stageD : Expr := esub (stageE true) (stageE false)

/-- `d (d − 1) ⋯ (d − 5)`, as exported (left-nested). -/
def stagePoly : Expr :=
  .mul (.mul (.mul (.mul (.mul stageD (esub stageD (.const 1))) (esub stageD (.const 2)))
    (esub stageD (.const 3))) (esub stageD (.const 4))) (esub stageD (.const 5))

theorem dag_flag0 : dag 3 = .mul (col 0) (esub (col 0) (.const 1)) := by decide
theorem dag_flag1 : dag 6 = .mul (col 1) (esub (col 1) (.const 1)) := by decide
theorem dag_flag2 : dag 9 = .mul (col 2) (esub (col 2) (.const 1)) := by decide
theorem dag_flag3 : dag 12 = .mul (col 3) (esub (col 3) (.const 1)) := by decide
theorem dag_flag4 : dag 15 = .mul (col 4) (esub (col 4) (.const 1)) := by decide
theorem dag_ksum : dag 22 = .mul (ksumE false) (esub (ksumE false) (.const 1)) := by decide
theorem dag_yfirst : dag 25 = .mul .isFirst (col 5) := by decide
theorem dag_ystep : dag 40 =
    .mul .isTransition (.mul (ksumE true) (esub (esub (colN 5) (col 5)) (.const 1))) := by decide
theorem dag_ypad : dag 42 = .mul (esub (.const 1) (ksumE false)) (col 5) := by decide
theorem dag_stage : dag 216 = .mul .isTransition stagePoly := by decide

/-- The ALU selector halves: `ka·h_i·(h_i − 1)`, `ka·(Σ h − 1)`, the same for `g`. -/
theorem dag_hbool : (List.range 8).map (fun i => dag (240 + 3 * i)) =
    (List.range 8).map (fun i => .mul (.mul (col 0) (col (34 + i))) (esub (col (34 + i)) (.const 1))) := by
  decide
theorem dag_gbool : (List.range 5).map (fun i => dag (219 + 3 * i)) =
    (List.range 5).map (fun i => .mul (.mul (col 0) (col (58 + i))) (esub (col (58 + i)) (.const 1))) := by
  decide

def sumCols : Nat → Nat → Expr
  | a, 0 => col a
  | a, n + 1 => .add (sumCols a n) (col (a + n + 1))

theorem dag_hsum : dag 270 = .mul (col 0) (esub (sumCols 34 7) (.const 1)) := by decide
theorem dag_gsum : dag 237 = .mul (col 0) (esub (sumCols 58 4) (.const 1)) := by decide

/-- The `PvD` selector `s(PvD) = ka·h_7·g_3` (op 31 = 8·3 + 7). -/
def sPvd : Expr := .mul (.mul (col 0) (col 41)) (col 61)

theorem dag_pvd_bool : dag 1592 = .mul (.mul sPvd (col 8)) (esub (col 8) (.const 1)) := by decide

/-- The 12 `PvD` constraints: `s·(a_k − (1 − P2)·pv_{1+k} − P2·pv_{13+k})` (`k < 6`) and
`s·(a_k − (1 − P2)·pv_{1+k})` (`k ≥ 6`). -/
def pvdE (k : Nat) : Expr :=
  if k < 6 then .mul sPvd (esub (esub (col (10 + k)) (.mul (esub (.const 1) (col 8)) (.pub (1 + k))))
      (.mul (col 8) (.pub (13 + k))))
  else .mul sPvd (esub (col (10 + k)) (.mul (esub (.const 1) (col 8)) (.pub (1 + k))))

def pvdIdx : List Nat := [1600, 1607, 1614, 1621, 1628, 1635, 1639, 1643, 1647, 1651, 1655, 1659]

theorem dag_pvd : pvdIdx.map dag = (List.range 12).map pvdE := by decide

theorem constr_mem : (([3, 6, 9, 12, 15, 22, 25, 40, 42, 216, 270, 237, 1592] ++ pvdIdx ++
    (List.range 8).map (fun i => 240 + 3 * i) ++ (List.range 5).map (fun i => 219 + 3 * i)).all
      fun j => nvConstraintIdx.contains j) = true := by decide

/-! ## The memory bus (bus 3) -/

def memIdx : List (Nat × List Nat) :=
  (nvInteractionIdx.filter (·.1 = 3)).map fun x => (x.2.1, x.2.2)

theorem memIdx_eq : memIdx = [
    (4171, [4144, 4146, 4148, 4150, 4152, 4154, 4156, 4158, 4160, 4162, 4164, 4166, 4168]),
    (4229, [4174, 4177, 4180, 4183, 4186, 4189, 4192, 4195, 4198, 4201, 4204, 4207, 4210]),
    (4281, [4233, 4236, 4239, 4242, 4245, 4248, 4251, 4254, 4257, 4260, 4263, 4266, 4269])] := by
  decide

/-- `ka·x + kb·y`: a merged slot's message field. -/
def mix (x y : Expr) : Expr := .add (.mul (col 0) x) (.mul (col 1) y)

/-- A selector sum `Σ ka·h_i·g_j` over `(i, j)`, left-nested as exported. -/
def selE : List (Nat × Nat) → Expr
  | [] => .const 0
  | p :: ps => ps.foldl (fun e q => .add e (.mul (.mul (col 0) (col q.1)) (col q.2)))
      (.mul (.mul (col 0) (col p.1)) (col p.2))

/-- The ops that read `a` / `b`, as `(h column, g column)` (`isa.rs` `reads_a` / `reads_b`). -/
def readsA : List (Nat × Nat) :=
  [(35, 58), (36, 58), (37, 58), (41, 58), (35, 59), (38, 59), (39, 59), (41, 59), (34, 60),
   (38, 60), (39, 60), (40, 60), (41, 60), (34, 61), (40, 61), (41, 61), (38, 62), (39, 62),
   (41, 62)]
def readsB : List (Nat × Nat) :=
  [(35, 58), (36, 58), (37, 58), (39, 59), (38, 60), (39, 60), (41, 60), (34, 61), (34, 62),
   (35, 62), (36, 62), (37, 62), (39, 62), (41, 62)]

/-- Slot 0: the ALU key `(y, c)` (count `−ka·mult`) merged with BIND's `E1[ya]` lookup (`kb`). -/
theorem dag_slot0 : dag 4171 = .add (.neg (.mul (col 0) (col 43))) (col 1) ∧
    [4144, 4146, 4148, 4150, 4152, 4154, 4156, 4158, 4160, 4162, 4164, 4166, 4168].map dag =
      mix (col 5) (col 66) :: (List.range 12).map (fun k => mix (col (46 + k)) (col (10 + k))) := by
  decide

/-- Slot 1: the `a` read at `P0` (count `Σ reads_a`) merged with BIND's `E1[ya + 1]`. -/
theorem dag_slot1 : dag 4229 = .add (selE readsA) (col 1) ∧
    [4174, 4177, 4180, 4183, 4186, 4189, 4192, 4195, 4198, 4201, 4204, 4207, 4210].map dag =
      mix (col 6) (.add (col 66) (.const 1)) ::
        (List.range 12).map (fun k => mix (col (10 + k)) (col (22 + k))) := by
  decide

/-- Slot 2: the `b` read (count `Σ reads_b`) merged with BIND's `E2[yb]`. -/
theorem dag_slot2 : dag 4281 = .add (selE readsB) (col 1) := by decide

/-! ## The trace predicate -/

/-- **Every exported constraint vanishes on every row of table `t`.** -/
def NvConstr (tr : Trace Fp) (t : Nat) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height t → ∀ j ∈ nvConstraintIdx, (dag j).eval tr t r pub = 0

section Rows
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- Cell `c` of row `r`. -/
abbrev cv (tr : Trace Fp) (t r c : Nat) : Fp := tr.cell t r c

theorem cz (h : NvConstr tr t pub) {r : Nat} (hr : r < tr.height t) {j : Nat}
    (hj : j ∈ nvConstraintIdx) {e : Expr} (he : dag j = e) : e.eval tr t r pub = 0 :=
  he ▸ h r hr j hj

theorem bool_of (x : Fp) (h : x * (x + -((1 : Nat) : Fp)) = 0) : x = 0 ∨ x = 1 := by
  have : ((1 : Nat) : Fp) = 1 := rfl
  rw [this] at h
  grind

/-- The role flags of a row: one of the five roles, or padding. -/
def RoleFlags (a b c d e : Fp) : Prop :=
  (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0) ∨ (a = 0 ∧ b = 1 ∧ c = 0 ∧ d = 0 ∧ e = 0) ∨
  (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 0 ∧ e = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 1 ∧ e = 0) ∨
  (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 1) ∨ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0)

theorem roleFlags_of (a b c d e : Fp) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hc : c = 0 ∨ c = 1) (hd : d = 0 ∨ d = 1) (he : e = 0 ∨ e = 1)
    (hs : (a + b + c + d + e) * ((a + b + c + d + e) + -((1 : Nat) : Fp)) = 0) :
    RoleFlags a b c d e := by
  unfold RoleFlags
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> rcases he with rfl | rfl <;> revert hs <;> decide +kernel

/-- **The role flags of every row** (booleanity and `ksum ∈ {0, 1}`). -/
theorem flags (h : NvConstr tr t pub) {r : Nat} (hr : r < tr.height t) :
    RoleFlags (cv tr t r 0) (cv tr t r 1) (cv tr t r 2) (cv tr t r 3) (cv tr t r 4) := by
  have e0 := cz h hr (by decide +kernel) dag_flag0
  have e1 := cz h hr (by decide +kernel) dag_flag1
  have e2 := cz h hr (by decide +kernel) dag_flag2
  have e3 := cz h hr (by decide +kernel) dag_flag3
  have e4 := cz h hr (by decide +kernel) dag_flag4
  have es := cz h hr (by decide +kernel) dag_ksum
  exact roleFlags_of _ _ _ _ _ (bool_of _ e0) (bool_of _ e1) (bool_of _ e2) (bool_of _ e3)
    (bool_of _ e4) es

/-- A role row: one flag set. -/
def Role (tr : Trace Fp) (t r : Nat) : Prop :=
  cv tr t r 0 + cv tr t r 1 + cv tr t r 2 + cv tr t r 3 + cv tr t r 4 = 1

def stageV (a b c d e : Fp) : Fp :=
  b + c * ((2 : Nat) : Fp) + d * ((3 : Nat) : Fp) + e * ((4 : Nat) : Fp) +
    (((1 : Nat) : Fp) + -(a + b + c + d + e)) * ((5 : Nat) : Fp)

def polyV (d : Fp) : Fp :=
  d * (d + -((1 : Nat) : Fp)) * (d + -((2 : Nat) : Fp)) * (d + -((3 : Nat) : Fp)) *
    (d + -((4 : Nat) : Fp)) * (d + -((5 : Nat) : Fp))

theorem ev_stage_raw (r : Nat) :
    (Expr.mul .isTransition stagePoly).eval tr t r pub =
      (if r + 1 = tr.height t then 0 else 1) *
      polyV (stageV (cv tr t ((r + 1) % tr.height t) 0) (cv tr t ((r + 1) % tr.height t) 1)
        (cv tr t ((r + 1) % tr.height t) 2) (cv tr t ((r + 1) % tr.height t) 3)
        (cv tr t ((r + 1) % tr.height t) 4) + -stageV (cv tr t r 0) (cv tr t r 1) (cv tr t r 2)
        (cv tr t r 3) (cv tr t r 4)) := rfl

theorem ev_stage {r : Nat} (hr1 : r + 1 < tr.height t) :
    (Expr.mul .isTransition stagePoly).eval tr t r pub =
      polyV (stageV (cv tr t (r + 1) 0) (cv tr t (r + 1) 1) (cv tr t (r + 1) 2) (cv tr t (r + 1) 3)
        (cv tr t (r + 1) 4) + -stageV (cv tr t r 0) (cv tr t r 1) (cv tr t r 2) (cv tr t r 3)
        (cv tr t r 4)) := by
  have h1 : r + 1 ≠ tr.height t := by omega
  rw [ev_stage_raw, if_neg h1, Nat.mod_eq_of_lt hr1]
  exact Lean.Grind.Semiring.one_mul _

/-- **A padding row is followed by padding** (the stage constraint). -/
theorem pad_next (h : NvConstr tr t pub) {r : Nat} (hr1 : r + 1 < tr.height t)
    (hp : ¬ Role tr t r) : ¬ Role tr t (r + 1) := by
  have e := cz h (Nat.lt_of_succ_lt hr1) (by decide +kernel) dag_stage
  rw [ev_stage hr1] at e
  have f0 := flags h (Nat.lt_of_succ_lt hr1)
  have f1 := flags h hr1
  unfold Role at hp ⊢
  revert e hp f0 f1
  generalize cv tr t r 0 = a0; generalize cv tr t r 1 = a1; generalize cv tr t r 2 = a2
  generalize cv tr t r 3 = a3; generalize cv tr t r 4 = a4
  generalize cv tr t (r + 1) 0 = b0; generalize cv tr t (r + 1) 1 = b1
  generalize cv tr t (r + 1) 2 = b2; generalize cv tr t (r + 1) 3 = b3
  generalize cv tr t (r + 1) 4 = b4
  intro e hp f0 f1
  unfold RoleFlags at f0 f1
  rcases f0 with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
    rcases f1 with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
    revert e hp <;> decide +kernel

/-- Every row before a role row is a role row. -/
theorem role_prefix (h : NvConstr tr t pub) {r : Nat} (hr : r < tr.height t) (hR : Role tr t r) :
    ∀ s ≤ r, Role tr t s := by
  intro s hs
  induction r with
  | zero => have : s = 0 := by omega
            exact this ▸ hR
  | succ r ih =>
    by_cases hsr : s = r + 1
    · exact hsr ▸ hR
    · apply ih (by omega) _ (by omega)
      exact Classical.byContradiction fun hn => pad_next h hr hn hR

theorem ev_yfirst : (Expr.mul .isFirst (col 5)).eval tr t 0 pub = cv tr t 0 5 :=
  Lean.Grind.Semiring.one_mul _

theorem ev_ystep_raw (r : Nat) :
    (Expr.mul .isTransition (.mul (ksumE true) (esub (esub (colN 5) (col 5)) (.const 1)))).eval
      tr t r pub = (if r + 1 = tr.height t then 0 else 1) *
        ((cv tr t ((r + 1) % tr.height t) 0 + cv tr t ((r + 1) % tr.height t) 1 +
          cv tr t ((r + 1) % tr.height t) 2 + cv tr t ((r + 1) % tr.height t) 3 +
          cv tr t ((r + 1) % tr.height t) 4) *
        (cv tr t ((r + 1) % tr.height t) 5 + -cv tr t r 5 + -((1 : Nat) : Fp))) := rfl

theorem ev_ystep {r : Nat} (hr1 : r + 1 < tr.height t) :
    (Expr.mul .isTransition (.mul (ksumE true) (esub (esub (colN 5) (col 5)) (.const 1)))).eval
      tr t r pub = (cv tr t (r + 1) 0 + cv tr t (r + 1) 1 + cv tr t (r + 1) 2 + cv tr t (r + 1) 3 +
        cv tr t (r + 1) 4) * (cv tr t (r + 1) 5 + -cv tr t r 5 + -((1 : Nat) : Fp)) := by
  have h1 : r + 1 ≠ tr.height t := by omega
  rw [ev_ystep_raw, if_neg h1, Nat.mod_eq_of_lt hr1]
  exact Lean.Grind.Semiring.one_mul _

/-- **`y` is the row index on role rows.** -/
theorem y_row (h : NvConstr tr t pub) {r : Nat} (hr : r < tr.height t) (hR : Role tr t r) :
    cv tr t r 5 = ((r : Nat) : Fp) := by
  induction r with
  | zero =>
    have e := cz h hr (by decide +kernel) dag_yfirst
    rw [ev_yfirst] at e
    exact e
  | succ r ih =>
    have hR' := role_prefix h hr hR r (by omega)
    have e := cz h (Nat.lt_of_succ_lt hr) (by decide +kernel) dag_ystep
    rw [ev_ystep hr] at e
    unfold Role at hR
    rw [hR, ih (Nat.lt_of_succ_lt hr) hR'] at e
    have h3 : ((1 : Nat) : Fp) = 1 := rfl
    have h4 : (((r + 1 : Nat)) : Fp) = ((r : Nat) : Fp) + 1 := Lean.Grind.Semiring.natCast_succ r
    rw [h4]
    rw [h3] at e
    grind

end Rows

/-! ## ALU selector halves: one-hot -/

theorem dag_hb : ∀ i, i < 8 → dag (240 + 3 * i) =
    .mul (.mul (col 0) (col (34 + i))) (esub (col (34 + i)) (.const 1)) := by decide +kernel
theorem dag_gb : ∀ i, i < 5 → dag (219 + 3 * i) =
    .mul (.mul (col 0) (col (58 + i))) (esub (col (58 + i)) (.const 1)) := by decide +kernel
theorem mem_hb : ∀ i, i < 8 → 240 + 3 * i ∈ nvConstraintIdx := by decide +kernel
theorem mem_gb : ∀ i, i < 5 → 219 + 3 * i ∈ nvConstraintIdx := by decide +kernel

/-- Eight booleans summing to `1` form a unit vector. -/
abbrev OH8 (x0 x1 x2 x3 x4 x5 x6 x7 : Fp) : Prop :=
  (x0 = 1 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 ∧ x4 = 0 ∧ x5 = 0 ∧ x6 = 0 ∧ x7 = 0) ∨
  (x0 = 0 ∧ x1 = 1 ∧ x2 = 0 ∧ x3 = 0 ∧ x4 = 0 ∧ x5 = 0 ∧ x6 = 0 ∧ x7 = 0) ∨
  (x0 = 0 ∧ x1 = 0 ∧ x2 = 1 ∧ x3 = 0 ∧ x4 = 0 ∧ x5 = 0 ∧ x6 = 0 ∧ x7 = 0) ∨
  (x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 1 ∧ x4 = 0 ∧ x5 = 0 ∧ x6 = 0 ∧ x7 = 0) ∨
  (x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 ∧ x4 = 1 ∧ x5 = 0 ∧ x6 = 0 ∧ x7 = 0) ∨
  (x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 ∧ x4 = 0 ∧ x5 = 1 ∧ x6 = 0 ∧ x7 = 0) ∨
  (x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 ∧ x4 = 0 ∧ x5 = 0 ∧ x6 = 1 ∧ x7 = 0) ∨
  (x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 ∧ x4 = 0 ∧ x5 = 0 ∧ x6 = 0 ∧ x7 = 1)

abbrev OH5 (y0 y1 y2 y3 y4 : Fp) : Prop :=
  (y0 = 1 ∧ y1 = 0 ∧ y2 = 0 ∧ y3 = 0 ∧ y4 = 0) ∨ (y0 = 0 ∧ y1 = 1 ∧ y2 = 0 ∧ y3 = 0 ∧ y4 = 0) ∨
  (y0 = 0 ∧ y1 = 0 ∧ y2 = 1 ∧ y3 = 0 ∧ y4 = 0) ∨ (y0 = 0 ∧ y1 = 0 ∧ y2 = 0 ∧ y3 = 1 ∧ y4 = 0) ∨
  (y0 = 0 ∧ y1 = 0 ∧ y2 = 0 ∧ y3 = 0 ∧ y4 = 1)

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem oh8 (x0 x1 x2 x3 x4 x5 x6 x7 : Fp) (b0 : x0 = 0 ∨ x0 = 1) (b1 : x1 = 0 ∨ x1 = 1)
    (b2 : x2 = 0 ∨ x2 = 1) (b3 : x3 = 0 ∨ x3 = 1) (b4 : x4 = 0 ∨ x4 = 1) (b5 : x5 = 0 ∨ x5 = 1)
    (b6 : x6 = 0 ∨ x6 = 1) (b7 : x7 = 0 ∨ x7 = 1)
    (hs : x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + -((1 : Nat) : Fp) = 0) :
    OH8 x0 x1 x2 x3 x4 x5 x6 x7 := by
  unfold OH8
  rcases b0 with rfl | rfl <;> rcases b1 with rfl | rfl <;> rcases b2 with rfl | rfl <;>
    rcases b3 with rfl | rfl <;> rcases b4 with rfl | rfl <;> rcases b5 with rfl | rfl <;>
    rcases b6 with rfl | rfl <;> rcases b7 with rfl | rfl <;> revert hs <;> decide +kernel

theorem oh5 (y0 y1 y2 y3 y4 : Fp) (b0 : y0 = 0 ∨ y0 = 1) (b1 : y1 = 0 ∨ y1 = 1)
    (b2 : y2 = 0 ∨ y2 = 1) (b3 : y3 = 0 ∨ y3 = 1) (b4 : y4 = 0 ∨ y4 = 1)
    (hs : y0 + y1 + y2 + y3 + y4 + -((1 : Nat) : Fp) = 0) : OH5 y0 y1 y2 y3 y4 := by
  unfold OH5
  rcases b0 with rfl | rfl <;> rcases b1 with rfl | rfl <;> rcases b2 with rfl | rfl <;>
    rcases b3 with rfl | rfl <;> rcases b4 with rfl | rfl <;> revert hs <;> decide +kernel

theorem oh8_fn {f : Nat → Fp} (H : OH8 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)) :
    ∃ a, a < 8 ∧ ∀ i, i < 8 → f i = if i = a then 1 else 0 := by
  rcases H with ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ | ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ |
      ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ | ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ |
      ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ | ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ |
      ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ | ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩
  · exact ⟨0, by omega, fun i hi => by
        match i, hi with
        | 0, _ => exact e0 | 1, _ => exact e1 | 2, _ => exact e2 | 3, _ => exact e3
        | 4, _ => exact e4 | 5, _ => exact e5 | 6, _ => exact e6 | 7, _ => exact e7⟩
  · exact ⟨1, by omega, fun i hi => by
        match i, hi with
        | 0, _ => exact e0 | 1, _ => exact e1 | 2, _ => exact e2 | 3, _ => exact e3
        | 4, _ => exact e4 | 5, _ => exact e5 | 6, _ => exact e6 | 7, _ => exact e7⟩
  · exact ⟨2, by omega, fun i hi => by
        match i, hi with
        | 0, _ => exact e0 | 1, _ => exact e1 | 2, _ => exact e2 | 3, _ => exact e3
        | 4, _ => exact e4 | 5, _ => exact e5 | 6, _ => exact e6 | 7, _ => exact e7⟩
  · exact ⟨3, by omega, fun i hi => by
        match i, hi with
        | 0, _ => exact e0 | 1, _ => exact e1 | 2, _ => exact e2 | 3, _ => exact e3
        | 4, _ => exact e4 | 5, _ => exact e5 | 6, _ => exact e6 | 7, _ => exact e7⟩
  · exact ⟨4, by omega, fun i hi => by
        match i, hi with
        | 0, _ => exact e0 | 1, _ => exact e1 | 2, _ => exact e2 | 3, _ => exact e3
        | 4, _ => exact e4 | 5, _ => exact e5 | 6, _ => exact e6 | 7, _ => exact e7⟩
  · exact ⟨5, by omega, fun i hi => by
        match i, hi with
        | 0, _ => exact e0 | 1, _ => exact e1 | 2, _ => exact e2 | 3, _ => exact e3
        | 4, _ => exact e4 | 5, _ => exact e5 | 6, _ => exact e6 | 7, _ => exact e7⟩
  · exact ⟨6, by omega, fun i hi => by
        match i, hi with
        | 0, _ => exact e0 | 1, _ => exact e1 | 2, _ => exact e2 | 3, _ => exact e3
        | 4, _ => exact e4 | 5, _ => exact e5 | 6, _ => exact e6 | 7, _ => exact e7⟩
  · exact ⟨7, by omega, fun i hi => by
        match i, hi with
        | 0, _ => exact e0 | 1, _ => exact e1 | 2, _ => exact e2 | 3, _ => exact e3
        | 4, _ => exact e4 | 5, _ => exact e5 | 6, _ => exact e6 | 7, _ => exact e7⟩

theorem oh5_fn {f : Nat → Fp} (H : OH5 (f 0) (f 1) (f 2) (f 3) (f 4)) :
    ∃ b, b < 5 ∧ ∀ j, j < 5 → f j = if j = b then 1 else 0 := by
  rcases H with ⟨e0, e1, e2, e3, e4⟩ | ⟨e0, e1, e2, e3, e4⟩ | ⟨e0, e1, e2, e3, e4⟩ |
      ⟨e0, e1, e2, e3, e4⟩ | ⟨e0, e1, e2, e3, e4⟩
  · exact ⟨0, by omega, fun i hi => by
        match i, hi with
        | 0, _ => exact e0 | 1, _ => exact e1 | 2, _ => exact e2 | 3, _ => exact e3 | 4, _ => exact e4⟩
  · exact ⟨1, by omega, fun i hi => by
        match i, hi with
        | 0, _ => exact e0 | 1, _ => exact e1 | 2, _ => exact e2 | 3, _ => exact e3 | 4, _ => exact e4⟩
  · exact ⟨2, by omega, fun i hi => by
        match i, hi with
        | 0, _ => exact e0 | 1, _ => exact e1 | 2, _ => exact e2 | 3, _ => exact e3 | 4, _ => exact e4⟩
  · exact ⟨3, by omega, fun i hi => by
        match i, hi with
        | 0, _ => exact e0 | 1, _ => exact e1 | 2, _ => exact e2 | 3, _ => exact e3 | 4, _ => exact e4⟩
  · exact ⟨4, by omega, fun i hi => by
        match i, hi with
        | 0, _ => exact e0 | 1, _ => exact e1 | 2, _ => exact e2 | 3, _ => exact e3 | 4, _ => exact e4⟩

/-- The value of a selector sum on a row (`f` = the row's cells). -/
def selVal (f : Nat → Fp) : List (Nat × Nat) → Fp
  | [] => ((0 : Nat) : Fp)
  | p :: ps => ps.foldl (fun v q => v + f 0 * f q.1 * f q.2) (f 0 * f p.1 * f p.2)

/-- The selector-sum value at unit vectors `a` (`h`) and `b` (`g`), `ka = 1`. -/
def unitRow (a b : Nat) (c : Nat) : Fp :=
  if c = 0 then 1 else if 34 ≤ c ∧ c < 42 then (if c - 34 = a then 1 else 0) else
    if 58 ≤ c ∧ c < 63 then (if c - 58 = b then 1 else 0) else 0

theorem unitRow_h (a b c : Nat) (h1 : 34 ≤ c) (h2 : c < 42) :
    unitRow a b c = if c - 34 = a then 1 else 0 := by
  unfold unitRow
  rw [if_neg (by omega), if_pos (⟨h1, h2⟩ : 34 ≤ c ∧ c < 42)]

theorem unitRow_g (a b c : Nat) (h3 : 58 ≤ c) (h4 : c < 63) :
    unitRow a b c = if c - 58 = b then 1 else 0 := by
  unfold unitRow
  rw [if_neg (by omega), if_neg (by omega), if_pos (⟨h3, h4⟩ : 58 ≤ c ∧ c < 63)]

/-- On a one-hot ALU row, each read slot's selector sum is `0` or `1`. -/
theorem sel_bool : ∀ a, a < 8 → ∀ b, b < 5 →
    (selVal (unitRow a b) readsA = 0 ∨ selVal (unitRow a b) readsA = 1) ∧
    (selVal (unitRow a b) readsB = 0 ∨ selVal (unitRow a b) readsB = 1) := by
  decide +kernel

/-- `PvD` (`h` index 7, `g` index 3) reads `a`. -/
theorem sel_pvd : selVal (unitRow 7 3) readsA = 1 := by decide +kernel

theorem reads_range : (readsA ++ readsB).all
    (fun p => decide (34 ≤ p.1 ∧ p.1 < 42 ∧ 58 ≤ p.2 ∧ p.2 < 63)) = true := by decide

theorem selVal_congr (f f' : Nat → Fp) (S : List (Nat × Nat)) (h0 : f 0 = f' 0)
    (hS : ∀ p ∈ S, f p.1 = f' p.1 ∧ f p.2 = f' p.2) : selVal f S = selVal f' S := by
  have key : ∀ (qs : List (Nat × Nat)) (v : Fp), (∀ q ∈ qs, f q.1 = f' q.1 ∧ f q.2 = f' q.2) →
      qs.foldl (fun v q => v + f 0 * f q.1 * f q.2) v =
        qs.foldl (fun v q => v + f' 0 * f' q.1 * f' q.2) v := by
    intro qs
    induction qs with
    | nil => intro v _; rfl
    | cons q qs ih =>
      intro v hq
      simp only [List.foldl]
      have h1 := hq q (List.mem_cons_self ..)
      have h2 := ih (v + f 0 * f q.1 * f q.2) fun q' hq' => hq q' (List.mem_cons_of_mem _ hq')
      rw [h2, h0, h1.1, h1.2]
  cases S with
  | nil => rfl
  | cons p ps =>
    simp only [selVal]
    have hp := hS p (List.mem_cons_self ..)
    rw [key ps _ fun q hq => hS q (List.mem_cons_of_mem _ hq), h0, hp.1, hp.2]

theorem selVal_zero (f : Nat → Fp) (h0 : f 0 = 0) (S : List (Nat × Nat)) : selVal f S = 0 := by
  have key : ∀ (qs : List (Nat × Nat)) (v : Fp), v = 0 →
      qs.foldl (fun v q => v + f 0 * f q.1 * f q.2) v = 0 := by
    intro qs
    induction qs with
    | nil => intro v hv; exact hv
    | cons q qs ih => intro v hv; apply ih; rw [hv, h0]; grind
  cases S with
  | nil => rfl
  | cons p ps => exact key ps _ (by rw [h0]; grind)

section Sel
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem ev_fold (r : Nat) (ps : List (Nat × Nat)) (e : Expr) :
    (ps.foldl (fun e q => Expr.add e (.mul (.mul (col 0) (col q.1)) (col q.2))) e).eval tr t r pub =
      ps.foldl (fun v q => v + cv tr t r 0 * cv tr t r q.1 * cv tr t r q.2) (e.eval tr t r pub) := by
  induction ps generalizing e with
  | nil => rfl
  | cons q ps ih => exact ih _

theorem ev_selE (r : Nat) (S : List (Nat × Nat)) :
    (selE S).eval tr t r pub = selVal (cv tr t r) S := by
  cases S with
  | nil => rfl
  | cons p ps => exact ev_fold r ps _

/-- **One-hot selector halves on an ALU row.** -/
theorem alu_onehot (h : NvConstr tr t pub) {r : Nat} (hr : r < tr.height t)
    (hka : cv tr t r 0 = 1) :
    ∃ a, a < 8 ∧ ∃ b, b < 5 ∧ (∀ i, i < 8 → cv tr t r (34 + i) = if i = a then 1 else 0) ∧
      (∀ j, j < 5 → cv tr t r (58 + j) = if j = b then 1 else 0) := by
  have hb : ∀ i, i < 8 → cv tr t r (34 + i) = 0 ∨ cv tr t r (34 + i) = 1 := by
    intro i hi
    have e := cz h hr (mem_hb i hi) (dag_hb i hi)
    change cv tr t r 0 * cv tr t r (34 + i) * (cv tr t r (34 + i) + -((1 : Nat) : Fp)) = 0 at e
    rw [hka, Lean.Grind.Semiring.one_mul] at e
    exact bool_of _ e
  have gb : ∀ i, i < 5 → cv tr t r (58 + i) = 0 ∨ cv tr t r (58 + i) = 1 := by
    intro i hi
    have e := cz h hr (mem_gb i hi) (dag_gb i hi)
    change cv tr t r 0 * cv tr t r (58 + i) * (cv tr t r (58 + i) + -((1 : Nat) : Fp)) = 0 at e
    rw [hka, Lean.Grind.Semiring.one_mul] at e
    exact bool_of _ e
  have hs := cz h hr (by decide +kernel) dag_hsum
  have gs := cz h hr (by decide +kernel) dag_gsum
  change cv tr t r 0 * (cv tr t r 34 + cv tr t r 35 + cv tr t r 36 + cv tr t r 37 + cv tr t r 38 +
    cv tr t r 39 + cv tr t r 40 + cv tr t r 41 + -((1 : Nat) : Fp)) = 0 at hs
  change cv tr t r 0 * (cv tr t r 58 + cv tr t r 59 + cv tr t r 60 + cv tr t r 61 + cv tr t r 62 +
    -((1 : Nat) : Fp)) = 0 at gs
  rw [hka, Lean.Grind.Semiring.one_mul] at hs gs
  obtain ⟨a, ha, hx⟩ := oh8_fn (f := fun i => cv tr t r (34 + i)) (oh8 _ _ _ _ _ _ _ _
    (hb 0 (by omega)) (hb 1 (by omega)) (hb 2 (by omega)) (hb 3 (by omega)) (hb 4 (by omega))
    (hb 5 (by omega)) (hb 6 (by omega)) (hb 7 (by omega)) hs)
  obtain ⟨b, hb', hy⟩ := oh5_fn (f := fun j => cv tr t r (58 + j)) (oh5 _ _ _ _ _
    (gb 0 (by omega)) (gb 1 (by omega)) (gb 2 (by omega)) (gb 3 (by omega)) (gb 4 (by omega)) gs)
  exact ⟨a, ha, b, hb', hx, hy⟩

/-- The selector sum of a one-hot ALU row is the unit-vector value. -/
theorem selVal_onehot {r a b : Nat} (hka : cv tr t r 0 = 1)
    (hx : ∀ i, i < 8 → cv tr t r (34 + i) = if i = a then 1 else 0)
    (hy : ∀ j, j < 5 → cv tr t r (58 + j) = if j = b then 1 else 0) (S : List (Nat × Nat))
    (hS : S.all (fun p => decide (34 ≤ p.1 ∧ p.1 < 42 ∧ 58 ≤ p.2 ∧ p.2 < 63)) = true) :
    selVal (cv tr t r) S = selVal (unitRow a b) S := by
  apply selVal_congr
  · simp only [unitRow, if_true]; exact hka
  · intro p hp
    have := List.all_eq_true.mp hS p hp
    simp only [decide_eq_true_eq] at this
    obtain ⟨h1, h2, h3, h4⟩ := this
    have e1 := hx (p.1 - 34) (by omega)
    have e2 := hy (p.2 - 58) (by omega)
    rw [show 34 + (p.1 - 34) = p.1 by omega] at e1
    rw [show 58 + (p.2 - 58) = p.2 by omega] at e2
    exact ⟨e1.trans (unitRow_h a b _ h1 h2).symm, e2.trans (unitRow_g a b _ h3 h4).symm⟩

end Sel

/-! ## The memory bus: entries, classification, the lookup hit -/

/-- **The memory-bus entries** `(count, message)` of table `t`: the three exported mem
interactions on every row. -/
def memEntries (tr : Trace Fp) (t : Nat) (pub : List Fp) : List (Fp × List Fp) :=
  (List.range (tr.height t)).flatMap fun r => memIdx.map fun cm =>
    ((dag cm.1).eval tr t r pub, cm.2.map fun m => (dag m).eval tr t r pub)

/-- The total count of message `m`. -/
def fsumAt (m : List Fp) : List (Fp × List Fp) → Fp
  | [] => 0
  | e :: l => (if e.2 = m then e.1 else 0) + fsumAt m l

/-- **The memory bus balances in the field** (LogUp: per message, the counts sum to `0`). -/
def MemBalance (tr : Trace Fp) (t : Nat) (pub : List Fp) : Prop :=
  ∀ m, fsumAt m (memEntries tr t pub) = 0

/-- The ALU key of row `r`: `(y, c_0..c_11)`. -/
def keyMsg (tr : Trace Fp) (t r : Nat) : List Fp :=
  cv tr t r 5 :: (List.range 12).map fun k => cv tr t r (46 + k)

/-- The `a` read of row `r`: `(P0, a_0..a_11)`. -/
def readMsg (tr : Trace Fp) (t r : Nat) : List Fp :=
  cv tr t r 6 :: (List.range 12).map fun k => cv tr t r (10 + k)

/-- Number of entries `(1, m)`. -/
def cnt1 (m : List Fp) : List (Fp × List Fp) → Nat
  | [] => 0
  | e :: l => (if e.2 = m ∧ e.1 = 1 then 1 else 0) + cnt1 m l

theorem fsum_cnt (m : List Fp) : ∀ L : List (Fp × List Fp),
    (∀ e ∈ L, e.2 = m → e.1 = 0 ∨ e.1 = 1) → fsumAt m L = ((cnt1 m L : Nat) : Fp)
  | [], _ => rfl
  | e :: l, h => by
    have ih := fsum_cnt m l fun e' he' => h e' (List.mem_cons_of_mem _ he')
    simp only [fsumAt, cnt1, ih]
    by_cases hm : e.2 = m
    · rcases h e (List.mem_cons_self ..) hm with h0 | h1
      · have : ¬ (e.2 = m ∧ e.1 = 1) := fun hh => by rw [h0] at hh; exact absurd hh.2 (by decide)
        rw [if_pos hm, if_neg this, h0, Nat.zero_add]
        grind
      · rw [if_pos hm, if_pos ⟨hm, h1⟩, h1, Nat.add_comm, Lean.Grind.Semiring.natCast_succ]
        grind
    · have : ¬ (e.2 = m ∧ e.1 = 1) := fun hh => hm hh.1
      rw [if_neg hm, if_neg this, Nat.zero_add]
      grind

theorem cnt1_le (m : List Fp) : ∀ L : List (Fp × List Fp), cnt1 m L ≤ L.length
  | [] => Nat.le_refl _
  | e :: l => by
    have := cnt1_le m l
    simp only [cnt1, List.length_cons]
    split <;> omega

theorem cnt1_pos (m : List Fp) : ∀ L : List (Fp × List Fp), ((1 : Fp), m) ∈ L → 0 < cnt1 m L
  | [], h => absurd h (List.not_mem_nil)
  | e :: l, h => by
    simp only [cnt1]
    rcases List.mem_cons.mp h with rfl | h'
    · rw [if_pos ⟨rfl, rfl⟩]; omega
    · have := cnt1_pos m l h'; omega

/-- **LogUp lookup hit.** If every entry is a key or has count `0`/`1`, the bus balances at `m`,
there are fewer than `p` entries and `(1, m)` is an entry, then a key entry carries `m`. -/
theorem hit (L : List (Fp × List Fp)) (m : List Fp) (Key : Fp × List Fp → Prop)
    (hcls : ∀ e ∈ L, Key e ∨ e.1 = 0 ∨ e.1 = 1) (hbal : fsumAt m L = 0)
    (hin : ((1 : Fp), m) ∈ L) (hlen : L.length < P) : ∃ e ∈ L, Key e ∧ e.2 = m := by
  apply Classical.byContradiction
  intro hno
  have h' : ∀ e ∈ L, e.2 = m → e.1 = 0 ∨ e.1 = 1 := fun e he hm =>
    (hcls e he).resolve_left fun hk => hno ⟨e, he, hk, hm⟩
  rw [fsum_cnt m L h'] at hbal
  have h0 : ((cnt1 m L : Nat) : Fp) = ((0 : Nat) : Fp) := hbal
  have := ZkFormal.PQ.StatePort.nat_inj_of_lt (Nat.lt_of_le_of_lt (cnt1_le m L) hlen)
    (by decide) h0
  have := cnt1_pos m L hin
  omega

theorem length_flatMap3 {β : Type} (f : Nat → List β) (hf : ∀ a, (f a).length = 3) :
    ∀ l : List Nat, (l.flatMap f).length = 3 * l.length
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, hf, length_flatMap3 f hf l, List.length_cons]
    omega

theorem memEntries_length (tr : Trace Fp) (t : Nat) (pub : List Fp) :
    (memEntries tr t pub).length = 3 * tr.height t := by
  unfold memEntries
  rw [length_flatMap3 _ (fun a => by rw [memIdx_eq]; rfl), List.length_range]

section Mem
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem ev_mix (r : Nat) (x y : Expr) :
    (mix x y).eval tr t r pub = cv tr t r 0 * x.eval tr t r pub + cv tr t r 1 * y.eval tr t r pub :=
  rfl

theorem ev_mix_alu {r : Nat} (h0 : cv tr t r 0 = 1) (h1 : cv tr t r 1 = 0) (x y : Expr) :
    (mix x y).eval tr t r pub = x.eval tr t r pub := by
  rw [ev_mix, h0, h1]; grind

/-- The three entries of row `r`. -/
theorem row_entries (r : Nat) :
    (memIdx.map fun cm => ((dag cm.1).eval tr t r pub, cm.2.map fun m => (dag m).eval tr t r pub)) =
    [(-(cv tr t r 0 * cv tr t r 43) + cv tr t r 1, [4144, 4146, 4148, 4150, 4152, 4154, 4156, 4158, 4160, 4162, 4164, 4166, 4168].map fun m => (dag m).eval tr t r pub),
     (selVal (cv tr t r) readsA + cv tr t r 1, [4174, 4177, 4180, 4183, 4186, 4189, 4192, 4195, 4198, 4201, 4204, 4207, 4210].map fun m => (dag m).eval tr t r pub),
     (selVal (cv tr t r) readsB + cv tr t r 1, [4233, 4236, 4239, 4242, 4245, 4248, 4251, 4254, 4257, 4260, 4263, 4266, 4269].map fun m => (dag m).eval tr t r pub)] := by
  have c0 : (dag 4171).eval tr t r pub = -(cv tr t r 0 * cv tr t r 43) + cv tr t r 1 := by
    rw [dag_slot0.1]; rfl
  have c1 : (dag 4229).eval tr t r pub = selVal (cv tr t r) readsA + cv tr t r 1 := by
    rw [dag_slot1.1]
    show (selE readsA).eval tr t r pub + cv tr t r 1 = _
    rw [ev_selE]
  have c2 : (dag 4281).eval tr t r pub = selVal (cv tr t r) readsB + cv tr t r 1 := by
    rw [dag_slot2]
    show (selE readsB).eval tr t r pub + cv tr t r 1 = _
    rw [ev_selE]
  rw [memIdx_eq]
  simp only [List.map_cons, List.map_nil, c0, c1, c2]

theorem keyMsg_eq {r : Nat} (h0 : cv tr t r 0 = 1) (h1 : cv tr t r 1 = 0) :
    ([4144, 4146, 4148, 4150, 4152, 4154, 4156, 4158, 4160, 4162, 4164, 4166, 4168].map fun m => (dag m).eval tr t r pub) = keyMsg tr t r := by
  show List.map ((fun e : Expr => e.eval tr t r pub) ∘ dag) [4144, 4146, 4148, 4150, 4152, 4154, 4156, 4158, 4160, 4162, 4164, 4166, 4168] = _
  rw [← List.map_map, dag_slot0.2]
  simp only [List.map_cons, List.map_map, keyMsg]
  rw [ev_mix_alu h0 h1]
  congr 1
  apply List.map_congr_left
  intro k _
  exact ev_mix_alu h0 h1 _ _

theorem readMsg_eq {r : Nat} (h0 : cv tr t r 0 = 1) (h1 : cv tr t r 1 = 0) :
    ([4174, 4177, 4180, 4183, 4186, 4189, 4192, 4195, 4198, 4201, 4204, 4207, 4210].map fun m => (dag m).eval tr t r pub) = readMsg tr t r := by
  show List.map ((fun e : Expr => e.eval tr t r pub) ∘ dag) [4174, 4177, 4180, 4183, 4186, 4189, 4192, 4195, 4198, 4201, 4204, 4207, 4210] = _
  rw [← List.map_map, dag_slot1.2]
  simp only [List.map_cons, List.map_map, readMsg]
  rw [ev_mix_alu h0 h1]
  congr 1
  apply List.map_congr_left
  intro k _
  exact ev_mix_alu h0 h1 _ _

/-- A key entry: an ALU row's `(y, c)`. -/
def IsKey (tr : Trace Fp) (t : Nat) (e : Fp × List Fp) : Prop :=
  ∃ r, r < tr.height t ∧ cv tr t r 0 = 1 ∧ e.2 = keyMsg tr t r

theorem bool_add_zero (x : Fp) (hx : x = 0 ∨ x = 1) : x + 0 = 0 ∨ x + 0 = 1 := by
  rcases hx with rfl | rfl <;> decide

theorem zero_add_bool (x : Fp) (hx : x = 0 ∨ x = 1) : 0 + x = 0 ∨ 0 + x = 1 := by
  rcases hx with rfl | rfl <;> decide

/-- **Every memory-bus entry is an ALU key or has count `0` or `1`.** -/
theorem mem_slots (h : NvConstr tr t pub) :
    ∀ e ∈ memEntries tr t pub, IsKey tr t e ∨ e.1 = 0 ∨ e.1 = 1 := by
  intro e he
  unfold memEntries at he
  obtain ⟨r, hr, he⟩ := List.mem_flatMap.mp he
  have hr := List.mem_range.mp hr
  rw [row_entries] at he
  have fl := flags h hr
  unfold RoleFlags at fl
  have halu : cv tr t r 0 = 1 → cv tr t r 1 = 0 →
      ∀ e ∈ [(-(cv tr t r 0 * cv tr t r 43) + cv tr t r 1, [4144, 4146, 4148, 4150, 4152, 4154, 4156, 4158, 4160, 4162, 4164, 4166, 4168].map fun m => (dag m).eval tr t r pub),
       (selVal (cv tr t r) readsA + cv tr t r 1, [4174, 4177, 4180, 4183, 4186, 4189, 4192, 4195, 4198, 4201, 4204, 4207, 4210].map fun m => (dag m).eval tr t r pub),
       (selVal (cv tr t r) readsB + cv tr t r 1, [4233, 4236, 4239, 4242, 4245, 4248, 4251, 4254, 4257, 4260, 4263, 4266, 4269].map fun m => (dag m).eval tr t r pub)], IsKey tr t e ∨ e.1 = 0 ∨ e.1 = 1 := by
    intro h0 h1 e he
    obtain ⟨a, ha, b, hb, hx, hy⟩ := alu_onehot h hr h0
    have sA := selVal_onehot h0 hx hy readsA (by decide)
    have sB := selVal_onehot h0 hx hy readsB (by decide)
    have bb := sel_bool a ha b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact .inl ⟨r, hr, h0, keyMsg_eq h0 h1⟩
    · right; rw [sA, h1]; exact bool_add_zero _ bb.1
    · right; rw [sB, h1]; exact bool_add_zero _ bb.2
  have hother : cv tr t r 0 = 0 → (cv tr t r 1 = 0 ∨ cv tr t r 1 = 1) →
      ∀ e ∈ [(-(cv tr t r 0 * cv tr t r 43) + cv tr t r 1, [4144, 4146, 4148, 4150, 4152, 4154, 4156, 4158, 4160, 4162, 4164, 4166, 4168].map fun m => (dag m).eval tr t r pub),
       (selVal (cv tr t r) readsA + cv tr t r 1, [4174, 4177, 4180, 4183, 4186, 4189, 4192, 4195, 4198, 4201, 4204, 4207, 4210].map fun m => (dag m).eval tr t r pub),
       (selVal (cv tr t r) readsB + cv tr t r 1, [4233, 4236, 4239, 4242, 4245, 4248, 4251, 4254, 4257, 4260, 4263, 4266, 4269].map fun m => (dag m).eval tr t r pub)], IsKey tr t e ∨ e.1 = 0 ∨ e.1 = 1 := by
    intro h0 h1 e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    have z : -(cv tr t r 0 * cv tr t r 43) = 0 := by rw [h0]; grind
    rcases he with rfl | rfl | rfl
    · right; show -(cv tr t r 0 * cv tr t r 43) + cv tr t r 1 = 0 ∨ _ = 1
      rw [z]; exact zero_add_bool _ h1
    · right; show selVal (cv tr t r) readsA + cv tr t r 1 = 0 ∨ _ = 1
      rw [selVal_zero _ h0]; exact zero_add_bool _ h1
    · right; show selVal (cv tr t r) readsB + cv tr t r 1 = 0 ∨ _ = 1
      rw [selVal_zero _ h0]; exact zero_add_bool _ h1
  rcases fl with ⟨a0, a1, -, -, -⟩ | ⟨a0, a1, -, -, -⟩ | ⟨a0, a1, -, -, -⟩ | ⟨a0, a1, -, -, -⟩ |
      ⟨a0, a1, -, -, -⟩ | ⟨a0, a1, -, -, -⟩
  · exact halu a0 a1 e he
  all_goals first
    | exact hother a0 (.inl a1) e he
    | exact hother a0 (.inr a1) e he

end Mem

/-! ## `PvD` rows and the digest cells -/

/-- **Row `d` is a `PvD` row reading address `addr`, half `p2`** (the program premise). -/
structure PvdAt (tr : Trace Fp) (t d addr p2 : Nat) : Prop where
  lt : d < tr.height t
  ka : cv tr t d 0 = 1
  h : ∀ i, i < 8 → cv tr t d (34 + i) = if i = 7 then 1 else 0
  g : ∀ j, j < 5 → cv tr t d (58 + j) = if j = 3 then 1 else 0
  hp0 : cv tr t d 6 = ((addr : Nat) : Fp)
  hp2 : cv tr t d 8 = ((p2 : Nat) : Fp)
  hp2le : p2 ≤ 1

/-- The value the `PvD` constraints give limb `k` of the cell read at half `p2`. -/
def pvdVal (pub : List Fp) (p2 k : Nat) : Fp :=
  if p2 = 0 then pub.getD (1 + k) 0 else if k < 6 then pub.getD (13 + k) 0 else 0

theorem pvd_idx : ∀ k, k < 12 →
    dag (pvdIdx.getD k 0) = pvdE k ∧ pvdIdx.getD k 0 ∈ nvConstraintIdx := by decide +kernel

section Pvd
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem kb_of_ka (h : NvConstr tr t pub) {r : Nat} (hr : r < tr.height t) (h0 : cv tr t r 0 = 1) :
    cv tr t r 1 = 0 := by
  have fl := flags h hr
  unfold RoleFlags at fl
  rcases fl with ⟨-, e, -⟩ | ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨e0, -⟩
  · exact e
  all_goals (rw [h0] at e0; exact absurd e0 (by decide))

theorem role_of_ka (h : NvConstr tr t pub) {r : Nat} (hr : r < tr.height t) (h0 : cv tr t r 0 = 1) :
    Role tr t r := by
  have fl := flags h hr
  unfold RoleFlags at fl
  unfold Role
  rcases fl with ⟨a, b, c, d, e⟩ | ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨e0, -⟩
  · rw [a, b, c, d, e]; decide
  all_goals (rw [h0] at e0; exact absurd e0 (by decide))

/-- **The `PvD` row's `a` limbs are the public values.** -/
theorem pvd_a (h : NvConstr tr t pub) {d addr p2 : Nat} (hd : PvdAt tr t d addr p2) :
    ∀ k, k < 12 → cv tr t d (10 + k) = pvdVal pub p2 k := by
  intro k hk
  obtain ⟨hdag, hmem⟩ := pvd_idx k hk
  have e := cz h hd.lt hmem hdag
  have s1 : sPvd.eval tr t d pub = 1 := by
    show cv tr t d 0 * cv tr t d 41 * cv tr t d 61 = 1
    have h7 := hd.h 7 (by omega)
    have g3 := hd.g 3 (by omega)
    simp only [if_true] at h7 g3
    rw [hd.ka, h7, g3]; decide
  have hp2 := hd.hp2
  have one : ((1 : Nat) : Fp) = 1 := rfl
  unfold pvdE at e
  unfold pvdVal
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd.hp2le with rfl | rfl
  · simp only [if_true]
    by_cases k6 : k < 6
    · rw [if_pos k6] at e
      change sPvd.eval tr t d pub * (cv tr t d (10 + k) + -((((1 : Nat) : Fp) + -cv tr t d 8) *
        pub.getD (1 + k) 0) + -(cv tr t d 8 * pub.getD (13 + k) 0)) = 0 at e
      rw [s1, hp2, one] at e
      have z : ((0 : Nat) : Fp) = 0 := rfl
      rw [z] at e
      grind
    · rw [if_neg k6] at e
      change sPvd.eval tr t d pub * (cv tr t d (10 + k) + -((((1 : Nat) : Fp) + -cv tr t d 8) *
        pub.getD (1 + k) 0)) = 0 at e
      rw [s1, hp2, one] at e
      have z : ((0 : Nat) : Fp) = 0 := rfl
      rw [z] at e
      grind
  · simp only [show ¬ (1 = 0) by decide, if_false]
    by_cases k6 : k < 6
    · rw [if_pos k6] at e
      rw [if_pos k6]
      change sPvd.eval tr t d pub * (cv tr t d (10 + k) + -((((1 : Nat) : Fp) + -cv tr t d 8) *
        pub.getD (1 + k) 0) + -(cv tr t d 8 * pub.getD (13 + k) 0)) = 0 at e
      rw [s1, hp2, one] at e
      grind
    · rw [if_neg k6] at e
      rw [if_neg k6]
      change sPvd.eval tr t d pub * (cv tr t d (10 + k) + -((((1 : Nat) : Fp) + -cv tr t d 8) *
        pub.getD (1 + k) 0)) = 0 at e
      rw [s1, hp2, one] at e
      grind

/-- **Memory consistency for a `PvD` read**: the cell of row `addr` is what row `d` read. -/
theorem pvd_read (h : NvConstr tr t pub) (hb : MemBalance tr t pub) (hH : tr.height t ≤ 2 ^ 24)
    {d addr p2 : Nat} (hd : PvdAt tr t d addr p2) (haddr : addr < 2 ^ 24) :
    addr < tr.height t ∧ ∀ k, k < 12 → cv tr t addr (46 + k) = cv tr t d (10 + k) := by
  have h1 := kb_of_ka h hd.lt hd.ka
  have hin : ((1 : Fp), readMsg tr t d) ∈ memEntries tr t pub := by
    unfold memEntries
    refine List.mem_flatMap.mpr ⟨d, List.mem_range.mpr hd.lt, ?_⟩
    rw [row_entries]
    have sA := selVal_onehot hd.ka hd.h hd.g readsA (by decide)
    have e1 : selVal (cv tr t d) readsA + cv tr t d 1 = 1 := by
      rw [sA, sel_pvd, h1]; decide
    rw [e1, readMsg_eq hd.ka h1]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have hlen : (memEntries tr t pub).length < P := by
    rw [memEntries_length]
    have : (3 : Nat) * 2 ^ 24 < P := by decide
    omega
  obtain ⟨e, -, ⟨r, hr, hka, hkey⟩, hm⟩ := hit _ _ (IsKey tr t) (mem_slots h) (hb _) hin hlen
  rw [hm] at hkey
  unfold readMsg keyMsg at hkey
  have hy := List.cons.inj hkey
  have hyr := y_row h hr (role_of_ka h hr hka)
  have hra : r = addr := by
    rw [hd.hp0, hyr] at hy
    exact ZkFormal.PQ.StatePort.nat_inj_of_lt (Nat.lt_of_lt_of_le hr (Nat.le_trans hH (by decide)))
      (Nat.lt_of_lt_of_le haddr (by decide)) hy.1.symm
  subst hra
  refine ⟨hr, fun k hk => ?_⟩
  have := congrArg (fun l : List Fp => l.getD k 0) hy.2
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some] at this
  exact this.symm

/-- **The digest cells are the public values.** -/
theorem pvd_cells (h : NvConstr tr t pub) (hb : MemBalance tr t pub) (hH : tr.height t ≤ 2 ^ 24)
    {d addr p2 : Nat} (hd : PvdAt tr t d addr p2) (haddr : addr < 2 ^ 24) :
    addr < tr.height t ∧ ∀ k, k < 12 → cv tr t addr (46 + k) = pvdVal pub p2 k := by
  obtain ⟨ha, hc⟩ := pvd_read h hb hH hd haddr
  exact ⟨ha, fun k hk => (hc k hk).trans (pvd_a h hd k hk)⟩

end Pvd

/-! ## `NodeTape` -/

/-- The 18 digest limbs the program exposes: the low cell's 12 and the high cell's first 6. -/
def digCells (tr : Trace Fp) (t alo ahi : Nat) : List Fp :=
  (List.range 12).map (fun k => cv tr t alo (46 + k)) ++ (List.range 6).map (fun k => cv tr t ahi (46 + k))

/-- The statement digest in the public values (`pv[1..19]`). -/
def pvDigest (pub : List Fp) : List Fp := (List.range 18).map fun i => pub.getD (1 + i) 0

theorem digCells_eq {tr : Trace Fp} {t : Nat} {pub : List Fp} (h : NvConstr tr t pub)
    (hb : MemBalance tr t pub) (hH : tr.height t ≤ 2 ^ 24) {dlo dhi alo ahi : Nat}
    (hlo : PvdAt tr t dlo alo 0) (hhi : PvdAt tr t dhi ahi 1) (halo : alo < 2 ^ 24)
    (hahi : ahi < 2 ^ 24) : digCells tr t alo ahi = pvDigest pub := by
  have cl := (pvd_cells h hb hH hlo halo).2
  have ch := (pvd_cells h hb hH hhi hahi).2
  unfold digCells pvDigest
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_append, List.length_map, List.length_range] at h1
  by_cases hi : i < 12
  · rw [List.getElem_append_left (by simpa using hi)]
    simp only [List.getElem_map, List.getElem_range]
    rw [cl i hi]; simp [pvdVal]
  · rw [List.getElem_append_right (by simpa using hi)]
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    rw [ch (i - 12) (by omega)]
    simp only [pvdVal, show ¬ (1 = 0) by decide, if_false, if_pos (show i - 12 < 6 by omega)]
    congr 1; omega

/-- **`NodeTape` from the exported NvAir.** For a decode whose `outDig` is a function `dec` of
the program's digest cells and whose `pubDig` is `dec` of the public digest limbs, the third
component of `E2ENode.NodeExec` holds on every trace satisfying the exported constraints and the
memory bus, given the program's two `PvD` rows. -/
theorem nodeTape_of_pvd {K : E2ENode.NodeKey} {Dg Proof : Type} (dec : List Fp → Dg)
    {tr : Trace Fp} {t : Nat} {pub : List Fp} (R : E2ENode.NodeRead K Dg Proof)
    (h : NvConstr tr t pub) (hb : MemBalance tr t pub) (hH : tr.height t ≤ 2 ^ 24)
    {dlo dhi alo ahi : Nat} (hlo : PvdAt tr t dlo alo 0) (hhi : PvdAt tr t dhi ahi 1)
    (halo : alo < 2 ^ 24) (hahi : ahi < 2 ^ 24) (hR : R.outDig = dec (digCells tr t alo ahi)) :
    E2ENode.NodeTape (fun p => dec (pvDigest p)) R pub := by
  show dec (pvDigest pub) = R.outDig
  rw [hR, digCells_eq h hb hH hlo hhi halo hahi]

/-! ## Vacuity guard: which tables balance NvAir's buses -/

/-- The circuit's AIRs and the buses each uses (exporter keygen listing, `NvAirExport` header). -/
def busUsers : List (String × List Nat) :=
  [("NvAir", [0, 1, 2, 3, 4, 5, 9, 11, 12, 14, 15]), ("Sha512Air4", [6, 7, 8, 9]),
   ("TableAir4", [6, 7]), ("ByteAir", [11])]

/-- NvAir's bus list is the exported one. -/
theorem nvAir_buses : (nvInteractionIdx.map (·.1)).eraseDups = (busUsers.head!).2 := by decide

/-- One closure step: add every table sharing a bus with the set. -/
def closeStep (S : List String) : List String :=
  busUsers.filterMap fun (n, bs) =>
    if S.contains n || busUsers.any (fun (m, cs) => S.contains m && cs.any bs.contains) then some n
    else none

/-- **The tables that balance NvAir's buses**, transitively: all four AIRs. A model whose
`Pin.air` omits one of them makes the global LogUp balance unsatisfiable for honest traces. -/
theorem nv_closure : closeStep (closeStep ["NvAir"]) = ["NvAir", "Sha512Air4", "TableAir4", "ByteAir"] ∧
    closeStep ["NvAir", "Sha512Air4", "TableAir4", "ByteAir"] =
      ["NvAir", "Sha512Air4", "TableAir4", "ByteAir"] := by decide

/-- **Bus 3 (mem) is NvAir's alone**, so its global balance is `MemBalance` (no other table
contributes entries). -/
theorem mem_users : busUsers.filter (fun p => p.2.contains 3) = [("NvAir", [0, 1, 2, 3, 4, 5, 9, 11, 12, 14, 15])] := by
  decide

/-- The global field LogUp balance of one bus over a list of tables' entries, and the subset
lemma: if only table `0` has entries on the bus, the global balance is table 0's. -/
def globalBalance (entries : List (List (Fp × List Fp))) : Prop :=
  ∀ m, fsumAt m entries.flatten = 0

theorem fsumAt_append (m : List Fp) (a b : List (Fp × List Fp)) :
    fsumAt m (a ++ b) = fsumAt m a + fsumAt m b := by
  induction a with
  | nil => show fsumAt m b = 0 + fsumAt m b; grind
  | cons e a ih =>
    simp only [List.cons_append, fsumAt, ih]
    grind

theorem memBalance_of_global {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (others : List (List (Fp × List Fp))) (hnil : ∀ l ∈ others, l = [])
    (hg : globalBalance (memEntries tr t pub :: others)) : MemBalance tr t pub := by
  intro m
  have := hg m
  have hf : others.flatten = [] := List.flatten_eq_nil_iff.mpr hnil
  rw [List.flatten_cons, hf, List.append_nil] at this
  exact this

#print axioms y_row
#print axioms mem_slots
#print axioms hit
#print axioms pvd_cells
#print axioms digCells_eq
#print axioms nodeTape_of_pvd
#print axioms nv_closure
#print axioms memBalance_of_global

/-! ## Non-vacuity of the trace predicate -/

/-- The all-zero two-row trace. -/
def zeroTr : Trace Fp := ⟨fun _ => 1, fun _ _ _ => 0⟩

/-- A syntactic check that an expression vanishes when every column and public value is `0`. -/
def zeroAt : Expr → Bool
  | .col _ _ => true
  | .pub _ => true
  | .const n => n == 0
  | .add a b => zeroAt a && zeroAt b
  | .mul a b => zeroAt a || zeroAt b
  | .neg a => zeroAt a
  | _ => false

theorem zeroAt_eval : ∀ (e : Expr) (r : Nat), zeroAt e = true → e.eval zeroTr 0 r [] = 0
  | .col _ _, _, _ => rfl
  | .pub i, _, _ => by show ([] : List Fp).getD i 0 = 0; rfl
  | .const n, _, h => by
    have : n = 0 := by simpa [zeroAt] using h
    subst this; rfl
  | .add a b, r, h => by
    simp only [zeroAt, Bool.and_eq_true] at h
    show a.eval zeroTr 0 r [] + b.eval zeroTr 0 r [] = 0
    rw [zeroAt_eval a r h.1, zeroAt_eval b r h.2]; decide
  | .mul a b, r, h => by
    simp only [zeroAt, Bool.or_eq_true] at h
    show a.eval zeroTr 0 r [] * b.eval zeroTr 0 r [] = 0
    rcases h with h | h
    · rw [zeroAt_eval a r h]; grind
    · rw [zeroAt_eval b r h]; grind
  | .neg a, r, h => by
    simp only [zeroAt] at h
    show -(a.eval zeroTr 0 r []) = 0
    rw [zeroAt_eval a r h]; decide
  | .isFirst, _, h => by simp [zeroAt] at h
  | .isLast, _, h => by simp [zeroAt] at h
  | .isTransition, _, h => by simp [zeroAt] at h

theorem fsumAt_zero (m : List Fp) : ∀ L : List (Fp × List Fp), (∀ e ∈ L, e.1 = 0) → fsumAt m L = 0
  | [], _ => rfl
  | e :: l, h => by
    simp only [fsumAt]
    rw [fsumAt_zero m l fun e' he' => h e' (List.mem_cons_of_mem _ he'), h e (List.mem_cons_self ..)]
    split <;> grind

/-- **`NvConstr ∧ MemBalance` is satisfiable** (the all-zero trace: the AIR admits all-zero rows,
`uair.rs`'s padding). Every one of the 548 exported constraints passes the syntactic zero check;
this does not exercise `PvdAt` (an honest NV trace is needed for that). -/
theorem zero_stage (r : Nat) : (dag 216).eval zeroTr 0 r [] = 0 := by
  rw [dag_stage, ev_stage_raw]
  have : polyV (stageV 0 0 0 0 0 + -stageV 0 0 0 0 0) = 0 := by decide
  show (if r + 1 = zeroTr.height 0 then 0 else 1) *
    polyV (stageV 0 0 0 0 0 + -stageV 0 0 0 0 0) = 0
  rw [this]; grind

theorem zero_check : nvConstraintIdx.all (fun j => j == 216 || zeroAt (dag j)) = true := by
  decide +kernel

theorem zero_constr (r j : Nat) (hj : j ∈ nvConstraintIdx) : (dag j).eval zeroTr 0 r [] = 0 := by
  have h1 : (j == 216 || zeroAt (dag j)) = true := List.all_eq_true.mp zero_check j hj
  by_cases e : j = 216
  · subst e; exact zero_stage r
  · have h2 : zeroAt (dag j) = true := by
      cases h3 : zeroAt (dag j)
      · rw [h3, Bool.or_false] at h1
        exact absurd (beq_iff_eq.mp h1) e
      · rfl
    exact zeroAt_eval _ r h2

theorem zero_holds : NvConstr zeroTr 0 [] ∧ MemBalance zeroTr 0 [] := by
  refine ⟨fun r _ j hj => zero_constr r j hj, ?_⟩
  intro m
  apply fsumAt_zero
  intro e he
  unfold memEntries at he
  obtain ⟨r, -, he⟩ := List.mem_flatMap.mp he
  rw [row_entries] at he
  have h0 : cv zeroTr 0 r 0 = 0 := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · show -((0 : Fp) * 0) + 0 = 0
    decide
  · show selVal (cv zeroTr 0 r) readsA + (0 : Fp) = 0
    rw [selVal_zero _ h0]; decide
  · show selVal (cv zeroTr 0 r) readsB + (0 : Fp) = 0
    rw [selVal_zero _ h0]; decide

#print axioms zero_holds

end ZkFormal.PQ.NvTape
