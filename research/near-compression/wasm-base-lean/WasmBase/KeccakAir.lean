import WasmBase.ChiAir
import WasmBase.Local.Add
import NearSpecV3.Wasm.Crypto
/-!
# WasmBase.KeccakAir — the Keccak-f[1600] round as an AIR row (definition)

`results/pq-keccak-air/README.md` §3 records the composition plan: the state is 1,600 bit columns and
each round is a full-state row chained through `nxt`, with `chi` (§2, `WasmBase.ChiAir`) as the only
non-trivial step.  This file writes that row **as a definition**: columns, constraints, and the
constant tables (`rc`, `rotc`, `pi`) taken from the spec's own arrays.

## What a row is

A row is one Keccak-f round.  Columns, in order:

| group | columns | meaning |
|---|---:|---|
| `A` | 1,600 | the state entering the round, lane `l` bit `k` at `64·l + k` |
| `C` | 320 | `theta` column parities `C[x][k]` |
| `CA` | 960 | the 3 chain auxiliaries per `C` bit (degree-lowering of the 5-way XOR) |
| `D` | 320 | `D[x][k] = C[x−1][k] ^ C[x+1][k+1]` |
| `T` | 1,600 | `A ^ D` (rho and pi are *wiring* on `T`, no columns) |
| `X` | 64 | `chi`'s result on lane 0, before `iota` |
| `sel` | 24 | one-hot round selector (`iota`'s `rc` index) |
| `hdr` | 2 | `ts` (clock) and `sp` (`sel₀`, the permutation-start flag) |

4,890 columns.  Rows are **25 per permutation**: 24 round rows and one hold row, so the wrap that
`nxt` needs (row `r` reads `nxt` of row `r`) lands on a row whose round constraints are disabled by
`trans`, and the permutation's output is readable from the hold row's `A`.

## The constraints

Per bit, in the order `theta → D → T → chi → iota`:

* **booleanity** — `A`, `C`, `CA`, `D`, `T`, `X`, `sel` are bits (`b·(b−1) = 0`), and `Σ sel = 1`.
* **theta** — `CA[x][k][0] = A[x]^A[x+5]`, `CA[·][1] = CA[·][0]^A[x+10]`, `CA[·][2] = CA[·][1]^A[x+15]`,
  `C[x] = CA[·][2]^A[x+20]`: four XOR-of-two equations per bit, each degree 2.
* **D** — `D[x][k] = C[x−1][k] ^ C[x+1][(k+1) mod 64]`.  The `rotl 1` is a **column index**, so the
  rotation by a constant costs nothing.  Degree 2.
* **T** — `T[l][k] = A[l][k] ^ D[l mod 5][k]`.  Degree 2.
* **rho/pi** — no constraint.  `B[m][j] = T[piSrc m][(j + 64 − rotc(piSrc m)) mod 64]`: a fixed
  column permutation, because every one of the 24 offsets is a constant (`Crypto.lean:29-30`).
* **chi** — `nxt A[m][k] = B[m][k] ^ ((1 − B[m+1][k]) · B[m+2][k])`, one degree-3 constraint per bit
  (lane 0 writes to `X` so that `iota` can add `rc` afterwards).
* **iota** — `nxt A[0][k] = X[k] ^ (sel · rc)`, with `rc_k = Σ_r sel_r · rcBit(r, k)`; the product is
  degree 2 and the round constant is selected by the one-hot, never by a polynomial in `r`.

Max degree **3** (the round), 0 interactions (rounds chain through `nxt`).  The exported table gates
each constraint by `trans` so the 25th row can hold the output; that gate is one multiplication, so
the gated list is degree 4.

## What this file does not do

The absorb (2,690-column, 17-message) and squeeze (1,602-column, 5-message) rows of
`model.py` are *not* here: this is the round table only, and it has **no interactions**.  The state
bus between the boundary rows and this table, and the lemmas that the constraints imply
`NearSpecV3.Wasm.Crypto.keccakF`'s round function, are separate steps.
-/
namespace WasmBase
namespace Chips
namespace Keccak

open Expr

/-! ## Geometry -/

def W : Nat := 64
def L : Nat := 25
def NB : Nat := 1600
def ROUNDS : Nat := 24

def aC : Nat := 0        -- 0 .. 1599     state
def cC : Nat := 1600     -- 1600 .. 1919  theta parities
def caC : Nat := 1920    -- 1920 .. 2879  chain auxiliaries
def dC : Nat := 2880     -- 2880 .. 3199  theta D
def tC : Nat := 3200     -- 3200 .. 4799  `A ^ D`
def xC : Nat := 4800     -- 4800 .. 4863  chi on lane 0
def selC : Nat := 4864   -- 4864 .. 4887  one-hot round selector
def hTs : Nat := 4888
def hSp : Nat := 4889
def ncols : Nat := 4890

def aBit (l k : Nat) : Nat := aC + W * l + k
def cBit (x k : Nat) : Nat := cC + W * x + k
def caBit (x k t : Nat) : Nat := caC + 3 * (W * x + k) + t
def dBit (x k : Nat) : Nat := dC + W * x + k
def tBit (l k : Nat) : Nat := tC + W * l + k
def xBit (k : Nat) : Nat := xC + k
def selE (r : Nat) : Nat := selC + r

def cols : List String :=
  ((List.range L).flatMap fun l => (List.range W).map fun k => s!"A{l}_{k}") ++
  ((List.range 5).flatMap fun x => (List.range W).map fun k => s!"C{x}_{k}") ++
  ((List.range 5).flatMap fun x => (List.range W).flatMap fun k =>
    (List.range 3).map fun t => s!"CA{x}_{k}_{t}") ++
  ((List.range 5).flatMap fun x => (List.range W).map fun k => s!"D{x}_{k}") ++
  ((List.range L).flatMap fun l => (List.range W).map fun k => s!"T{l}_{k}") ++
  (List.range W).map (fun k => s!"X{k}") ++
  (List.range ROUNDS).map (fun r => s!"sel{r}") ++ ["ts", "sp"]

/-! ## The spec's constants, read out of `NearSpecV3.Wasm.Crypto`

Nothing is re-typed: `rc` and `rotc` are the spec's arrays (`Crypto.lean:20-30`), and `piSrc` is
computed from the spec's own index formula `y + 5·((2x+3y) mod 5)`. -/

/-- `rc[r]` as a natural (the spec's `UInt64` constant). -/
def rcVal (r : Nat) : Nat := (NearSpecV3.Wasm.Crypto.rc.toList.map (·.toNat)).getD r 0

/-- Bit `k` of the round constant `rc[r]`. -/
def rcBit (r k : Nat) : Nat := rcVal r >>> k % 2 ^ 1

/-- `rotc[s]`, the rho offset of source lane `s`. -/
def rotcVal (s : Nat) : Nat := (NearSpecV3.Wasm.Crypto.rotc.toList.map (·.toNat)).getD s 0

/-- The spec's pi target of source lane `s = x + 5y`: `y + 5·((2x+3y) mod 5)`
(`Crypto.lean:47-50`). -/
def piTgt (s : Nat) : Nat := s / 5 + 5 * ((2 * (s % 5) + 3 * (s / 5)) % 5)

/-- The inverse of `pi`: for target lane `m`, the source lane whose rotated value lands there. -/
def piSrc (m : Nat) : Nat := ((List.range L).find? (fun s => piTgt s == m)).getD 0

/-- `chi`'s three input lanes for output lane `m` (all in lane `y = m / 5`). -/
def chi1 (m : Nat) : Nat := (m % 5 + 1) % 5 + 5 * (m / 5)
def chi2 (m : Nat) : Nat := (m % 5 + 2) % 5 + 5 * (m / 5)

/-- **rho/pi as wiring**: bit `j` of `B` lane `m` is bit `(j + 64 − rotc(s)) mod 64` of `T` lane
`s = piSrc m`.  No column, no constraint. -/
def bBit (m j : Nat) : Nat := tBit (piSrc m) ((j + W - rotcVal (piSrc m)) % W)

def v (i : Nat) : Expr := .col i
def nv (i : Nat) : Expr := .nxt i

/-! ## Expression builders

The state is bit-sliced, so every operation is a bit operation.  `xor2 a b = a + b − 2ab` is
XOR on two bits; `boolE b = b·(b−1)` is booleanity.  `and_not` (`WasmBase.Chips.Chi`) is what makes
the `chi` constraint below the spec's `a ^ (~b & c)` rather than a re-statement of it. -/

/-- The numerals, named: `simp` cannot see through `OfNat Expr`, so the degree lemmas below want
`Expr.c 1` on the nose. -/
def e0 : Expr := .c 0
def e1 : Expr := .c 1
def e2 : Expr := .c 2

def boolE (e : Expr) : Expr := e * (e - e1)
def xor2 (a b : Expr) : Expr := a + b - e2 * (a * b)
def xorEq (a b r : Expr) : Expr := xor2 a b - r

/-- `theta`'s 5-way XOR, chained through the three `CA` auxiliaries of lane column `x`, bit `k`. -/
def thetaConstr (x k : Nat) : List Expr :=
  [xorEq (v (aBit x k)) (v (aBit (x + 5) k)) (v (caBit x k 0)),
   xorEq (v (caBit x k 0)) (v (aBit (x + 10) k)) (v (caBit x k 1)),
   xorEq (v (caBit x k 1)) (v (aBit (x + 15) k)) (v (caBit x k 2)),
   xorEq (v (caBit x k 2)) (v (aBit (x + 20) k)) (v (cBit x k))]

/-- `D[x][k] = C[x−1][k] ^ C[x+1][k+1]`: the `rotl 1` is the `+1` in the index. -/
def dConstr (x k : Nat) : Expr :=
  xorEq (v (cBit ((x + 4) % 5) k)) (v (cBit ((x + 1) % 5) ((k + 1) % W))) (v (dBit x k))

/-- `T[l][k] = A[l][k] ^ D[l mod 5][k]`. -/
def tConstr (l k : Nat) : Expr :=
  xorEq (v (aBit l k)) (v (dBit (l % 5) k)) (v (tBit l k))

/-- `chi`: `nxt A[m][k] = B0 ^ ((1 − B1)·B2)`.  For lane 0 the right side is `X` (iota's input),
for every other lane it is `nxt A`. -/
def chiRhs (m k : Nat) : Expr :=
  let b0 := v (bBit m k)
  let b1 := v (bBit (chi1 m) k)
  let b2 := v (bBit (chi2 m) k)
  xor2 b0 ((e1 - b1) * b2)

def chiConstr (m k : Nat) : Expr :=
  chiRhs m k - (if m = 0 then v (xBit k) else nv (aBit m k))

/-- `rc` selected by the one-hot `sel`: `Σ_{r<24} sel_r · rc_r(k)`.  Written recursively (not as a
`List.foldr`) so that its degree is one short induction. -/
def rcSelAux (k : Nat) : Nat → Expr
  | 0 => e0
  | n + 1 => rcSelAux k n + v (selE n) * Expr.c (rcBit n k)

def rcSel (k : Nat) : Expr := rcSelAux k ROUNDS

def iotaConstr (k : Nat) : Expr :=
  xor2 (v (xBit k)) (rcSel k) - nv (aBit 0 k)

/-- `Σ_r sel_r`, the one-hot sum. -/
def onehotAux : Nat → Expr
  | 0 => e0
  | n + 1 => onehotAux n + v (selE n)

def onehotSum : Expr := onehotAux ROUNDS

/-- `∏_{i<n} ∏_{j<m} boolE (v (f i j))`: the shape of every booleanity family.  Naming the shape is
what makes the degree lemma one application instead of a case split over eight concatenations. -/
def boolFam (n m : Nat) (f : Nat → Nat → Nat) : List Expr :=
  (List.range n).flatMap fun i => (List.range m).map fun j => boolE (v (f i j))

/-- The booleanity families, as a list: every state, `theta`, `chi` and selector column. -/
def boolFams : List (List Expr) :=
  [boolFam L W aBit, boolFam 5 W cBit, boolFam 5 W (fun x k => caBit x k 0),
   boolFam 5 W (fun x k => caBit x k 1), boolFam 5 W (fun x k => caBit x k 2),
   boolFam 5 W dBit, boolFam L W tBit, boolFam W 1 (fun k _ => xBit k),
   boolFam ROUNDS 1 (fun r _ => selE r), boolFam 1 1 (fun _ _ => hSp)]

def boolConstraints : List Expr := boolFams.flatten

/-- The one-hot round selector: each `sel_r` is a bit and they sum to 1; `sp` mirrors `sel_0`. -/
def selConstraints : List Expr := [onehotSum - e1, v (selE 0) - v hSp]

/-- `theta`: one 4-equation chain per `C` bit. -/
def thetaConstraints : List Expr :=
  (List.range 5).flatMap (fun x => (List.range W).flatMap fun k => thetaConstr x k)

/-- `theta`'s `D` lane. -/
def dConstraints : List Expr :=
  (List.range 5).flatMap (fun x => (List.range W).map fun k => dConstr x k)

/-- Theta-applied state `T = A ^ D`. -/
def tConstraints : List Expr :=
  (List.range L).flatMap (fun l => (List.range W).map fun k => tConstr l k)

/-- `chi` on every lane. -/
def chiConstraints : List Expr :=
  (List.range L).flatMap (fun l => (List.range W).map fun k => chiConstr l k)

/-- `iota` on every bit of lane 0. -/
def iotaConstraints : List Expr := (List.range W).map iotaConstr

/-- **The round's constraints**, ungated: booleanity, one-hot, the `theta`/`D`/`T`/`chi`/`iota`
equations.  This is the list the round lemma reasons about. -/
def roundConstraints : List Expr :=
  boolConstraints ++ selConstraints ++ thetaConstraints ++ dConstraints ++ tConstraints ++
  chiConstraints ++ iotaConstraints

/-- The exported constraint list: the round equations gated by `trans`, so the hold row (the 25th of
each permutation, where `trans = 0`) leaves `nxt` free and its `A` is the round's output.  Gating is
one multiplication, so the gated list is degree 4 where the round itself is degree 3. -/
def constraints : List Expr := roundConstraints.map (fun e => trans * e)

/-- The round table has **no interactions**: rounds chain through `nxt`. -/
def inters : List Inter := []

def table : Table := ⟨"KECCAK", cols, constraints, inters⟩

/-! ## Shape facts -/

theorem ncols_eq : ncols = 4890 := rfl

theorem cols_len : cols.length = ncols := by
  simp only [cols, ncols, W, L, ROUNDS,
    List.length_append, List.length_flatMap, List.length_map, List.length_range]
  decide

/-! ### Degree

`chi` is the only triple product in the round; everything else is degree ≤ 2.  Proved structurally
(unfolding the whole 1,600-constraint list would be both slow and unreadable).

The numerals are named `e0`/`e1`/`e2` because `simp` cannot see through `OfNat Expr` (`(1 : Expr)`
does not syntactically match `Expr.c 1`), and `omega` needs the numeral's degree as a hypothesis. -/

theorem deg_c (n : Nat) : (Expr.c n).degree = 0 := rfl
theorem deg_e0 : e0.degree = 0 := rfl
theorem deg_e1 : e1.degree = 0 := rfl
theorem deg_e2 : e2.degree = 0 := rfl
theorem deg_col (i : Nat) : (Expr.col i).degree = 1 := rfl
theorem deg_nxt (i : Nat) : (Expr.nxt i).degree = 1 := rfl
theorem deg_add (a b : Expr) : (a + b).degree = max a.degree b.degree := rfl
theorem deg_sub (a b : Expr) : (a - b).degree = max a.degree b.degree := rfl
theorem deg_mul (a b : Expr) : (a * b).degree = a.degree + b.degree := rfl

theorem deg_v (i : Nat) : (v i).degree = 1 := rfl
theorem deg_nv (i : Nat) : (nv i).degree = 1 := rfl

theorem xor2_le (a b : Expr) (ha : a.degree ≤ 1) (hb : b.degree ≤ 1) :
    (xor2 a b).degree ≤ 2 := by
  simp only [xor2, deg_mul, deg_sub, deg_add, deg_e2]
  have h1 := Nat.le_max_left a.degree b.degree
  have h2 := Nat.le_max_right a.degree b.degree
  omega

theorem xorEq_le (a b r : Expr) (ha : a.degree ≤ 1) (hb : b.degree ≤ 1) (hr : r.degree ≤ 1) :
    (xorEq a b r).degree ≤ 2 := by
  simp only [xorEq, deg_sub, deg_add]
  have := xor2_le a b ha hb
  omega

theorem thetaConstr_le (x k : Nat) : ∀ e ∈ thetaConstr x k, e.degree ≤ 3 := by
  intro e he
  simp only [thetaConstr, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    (simp only [xorEq, xor2, deg_sub, deg_add, deg_mul, deg_v, deg_e1, deg_e2]; omega)

theorem dConstr_le (x k : Nat) : (dConstr x k).degree ≤ 3 := by
  simp only [dConstr, xorEq, xor2, deg_sub, deg_add, deg_mul, deg_v, deg_e1, deg_e2]
  omega

theorem tConstr_le (l k : Nat) : (tConstr l k).degree ≤ 3 := by
  simp only [tConstr, xorEq, xor2, deg_sub, deg_add, deg_mul, deg_v, deg_e1, deg_e2]
  omega

theorem chiRhs_le (m k : Nat) : (chiRhs m k).degree ≤ 3 := by
  simp only [chiRhs, xor2, v, deg_e1, deg_e2, deg_col, deg_nxt, deg_add, deg_sub, deg_mul]
  omega

theorem chiConstr_le (m k : Nat) : (chiConstr m k).degree ≤ 3 := by
  simp only [chiConstr, deg_sub, deg_add]
  have := chiRhs_le m k
  split
  · simp only [deg_v]; omega
  · simp only [deg_nv]; omega

theorem rcSelAux_le (k n : Nat) : (rcSelAux k n).degree ≤ 1 := by
  induction n with
  | zero => exact Nat.zero_le 1
  | succ m ih =>
    simp only [rcSelAux, deg_add, deg_mul, deg_v, deg_c]
    omega

theorem rcSel_le (k : Nat) : (rcSel k).degree ≤ 1 := rcSelAux_le k ROUNDS

theorem onehotAux_le (n : Nat) : (onehotAux n).degree ≤ 1 := by
  induction n with
  | zero => exact Nat.zero_le 1
  | succ m ih =>
    simp only [onehotAux, deg_add, deg_v]
    omega

theorem iotaConstr_le (k : Nat) : (iotaConstr k).degree ≤ 2 := by
  simp only [iotaConstr, xor2, deg_sub, deg_add, deg_mul, deg_v, deg_nv, deg_e2]
  have := rcSel_le k
  omega

theorem boolFam_le (n m : Nat) (f : Nat → Nat → Nat) :
    ∀ e ∈ boolFam n m f, e.degree ≤ 3 := by
  intro e he
  simp only [boolFam, List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨i, _, j, _, rfl⟩ := he
  simp only [boolE, v, deg_sub, deg_mul, deg_col, deg_e1]
  omega

theorem boolFams_le : ∀ l ∈ boolFams, ∀ e ∈ l, e.degree ≤ 3 := by
  intro l hl e he
  simp only [boolFams, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact boolFam_le _ _ _ e he

theorem boolConstraints_le : ∀ e ∈ boolConstraints, e.degree ≤ 3 := by
  intro e he
  simp only [boolConstraints, List.mem_flatten] at he
  obtain ⟨l, hl, hel⟩ := he
  exact boolFams_le l hl e hel

theorem selConstraints_le : ∀ e ∈ selConstraints, e.degree ≤ 3 := by
  intro e he
  simp only [selConstraints, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · simp only [onehotSum, deg_sub, deg_v, deg_e1]
    have := onehotAux_le ROUNDS
    omega
  · simp only [deg_sub, deg_v]; omega

theorem thetaConstraints_le : ∀ e ∈ thetaConstraints, e.degree ≤ 3 := by
  intro e he
  simp only [thetaConstraints, List.mem_flatMap, List.mem_range] at he
  obtain ⟨x, _, k, _, he⟩ := he
  exact thetaConstr_le x k e he

theorem dConstraints_le : ∀ e ∈ dConstraints, e.degree ≤ 3 := by
  intro e he
  simp only [dConstraints, List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨x, _, k, _, rfl⟩ := he
  exact dConstr_le x k

theorem tConstraints_le : ∀ e ∈ tConstraints, e.degree ≤ 3 := by
  intro e he
  simp only [tConstraints, List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨l, _, k, _, rfl⟩ := he
  exact tConstr_le l k

theorem chiConstraints_le : ∀ e ∈ chiConstraints, e.degree ≤ 3 := by
  intro e he
  simp only [chiConstraints, List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨l, _, k, _, rfl⟩ := he
  exact chiConstr_le l k

theorem iotaConstraints_le : ∀ e ∈ iotaConstraints, e.degree ≤ 3 := by
  intro e he
  simp only [iotaConstraints, List.mem_map, List.mem_range] at he
  obtain ⟨k, _, rfl⟩ := he
  exact Nat.le_trans (iotaConstr_le k) (by decide)

/-- Every round constraint is degree ≤ 3 — `chi` is the only triple product. -/
theorem roundConstraints_le : ∀ e ∈ roundConstraints, e.degree ≤ 3 := by
  intro e he
  simp only [roundConstraints, List.mem_append] at he
  rcases he with (((((he | he) | he) | he) | he) | he) | he
  · exact boolConstraints_le e he
  · exact selConstraints_le e he
  · exact thetaConstraints_le e he
  · exact dConstraints_le e he
  · exact tConstraints_le e he
  · exact chiConstraints_le e he
  · exact iotaConstraints_le e he

/-- The exported (gated) list is degree ≤ 4: gating by `trans` adds exactly one. -/
theorem constraints_le : ∀ e ∈ constraints, e.degree ≤ 4 := by
  intro e he
  simp only [constraints, List.mem_map] at he
  obtain ⟨e', he', rfl⟩ := he
  have h := roundConstraints_le e' he'
  show (trans * e').degree ≤ 4
  simp only [deg_mul, Expr.degree]
  omega

/-! ## Counts -/

set_option maxRecDepth 1000000

theorem thetaConstr_len : (thetaConstr 0 0).length = 4 := rfl

theorem boolE_degree_two (i : Nat) : (boolE (v i)).degree = 2 := by
  simp only [boolE, v, deg_sub, deg_mul, deg_col, deg_e1]; omega

theorem constraints_len : constraints.length = 9755 := by
  simp only [constraints, roundConstraints, boolConstraints, boolFams, boolFam, selConstraints,
    thetaConstraints, dConstraints, tConstraints, chiConstraints, iotaConstraints,
    List.length_append, List.length_flatten, List.length_flatMap, List.length_map,
    List.length_range, List.length_cons, List.length_nil, W, L, ROUNDS]
  decide

/-- Rounds carry no interaction at all. -/
theorem inters_len : inters.length = 0 := rfl

end Keccak
end Chips
end WasmBase
