import WasmBase.Chips
import NearSpecV3.Wasm.Crypto
/-!
# WasmBase.RipemdAir — the RIPEMD-160 step as an AIR row (definition)

`results/pq-hash-air/README.md` §3.6 lists `ripemd160` (host id 56) as the next hash to build: same
block count as SHA-256, "a separate schedule and a 5-word feed-forward".  This file writes that row
**as a definition** — columns, constraints, the spec's own constant arrays — in the style of
`WasmBase.KeccakAir` (row definition only; generator, differential vectors and the round-agreement
lemma are separate steps).

## What a row is

A row is **one RIPEMD-160 compression step** `j ∈ [0,80)`, carrying both branches at once (the spec
runs the left and right lines in lockstep, `Crypto.lean:129-133`):

```
t  := rotl32 (al + f j  bl cl dl + x[rl[j]] + kl[j/16]) sl[j] + el        -- left line
t' := rotl32 (ar + f (79-j) br cr dr + x[rr[j]] + kr[j/16]) sr[j] + er   -- right line
al := el; el := dl; dl := rotl32 cl 10; cl := bl; bl := t               -- shift
```

Columns, in order (1,608; every column is a bit):

| group | columns | meaning |
|---|---:|---|
| `L` | 160 | left working words `al,bl,cl,dl,el`, word `w` bit `k` at `32w+k` |
| `R` | 160 | right working words `ar,br,cr,dr,er` |
| `X` | 512 | the block's 16 message words (little-endian), constant along a block |
| `fL`,`fR` | 64 | the `f` value of each line (`rf j bl cl dl`, `rf (79-j) br cr dr`) |
| `xL`,`xR` | 64 | the selected message word `x[rl[j]]` / `x[rr[j]]` |
| `t` | 256 | the four chained sums of each line: `t1 = al+fL`, `t2 = t1+xL`, `t3 = t2+kL`, `tf = rot+el` |
| `rot` | 64 | `rotl32 t3 sl[j]` (left), `rotl32 t6 sr[j]` (right) |
| `cy` | 248 | the carry of each binary addition, 31 per addition (bit 31's carry is dropped: mod 2³²) |
| `sel` | 80 | one-hot step selector |

## The constraints

Bit-sliced, so `f` and the message selection are polynomials in the row's bits:

* **booleanity** — all 1,608 columns are bits, and `Σ sel = 1`.
* **`f`** — five forms, one per 16-step group (`Crypto.lean:110-115`), gated by the group's selector
  sum: `gsel_g · (fBit_k − form_g(bl,cl,dl)_k) = 0`.  The right line takes group `4−g`, i.e. `rf (79−j)`.
  The five forms are `xor3`, `ch`, `(b ∨ ¬c) ⊕ d`, `(b ∧ d) + (c ∧ ¬d)` (the two terms are disjoint,
  so their sum is the `∨`, degree 2), `b ⊕ (c ∨ ¬d)`.
* **message selection** — `Σ_j sel_j · (xL_k − X[rl[j]]_k) = 0`, and the same with `rr` for `xR`.
* **rotation** — `Σ_j sel_j · (rot_k − t3[(k − sl[j]) mod 32]) = 0`; each step's offset is a constant,
  so the rotation is a selector-gated index map, not a barrel shifter.
* **additions** — the four chained binary additions per line, as full adders
  `t_k = x_k ⊕ y_k ⊕ cyIn_k`, `cy_k = maj(x_k, y_k, cyIn_k)` (degree 3); carry-in to bit 0 is 0.
* **shift** — `nxt al = el`, `nxt bl = tf`, `nxt cl = bl`, `nxt dl = rotl32 cl 10` (an index shift),
  `nxt el = dl`; mirrored on the right line.

Max degree **4** (the group-gated `f` form: selector × degree-3 form).  No interactions: steps chain
through `nxt`, so the row's `nxt` is the next step's input state.

## What this file does not do

* **The feed-forward** (`Crypto.lean:134-135`, `h := h + [cl+dr, dl+er, el+ar, al+br, bl+cr]`) and the
  block-boundary/digest rows are not here — as with `KeccakAir`, this is the step table only.
* **The message-word binding**: that the `X` columns are the block's bytes at the call's `(ptr, len)`.
  That is the same stated join obligation `Sha.HashInputLink` is (`HOSTB`/memory ↔ bytes), and the `X`
  columns carry no interaction to enforce it.
* **The generator and the differential vectors** (`RipemdVectors.lean`, the analogue of
  `KeccakVectors`): the row's columns filled from these equations and read back against
  `NearSpecV3.Wasm.Crypto.ripemd160` on the padding boundaries.  Nothing in this file is a numeric
  claim, so nothing here can silently disagree with the spec — but nothing here *checks* the step
  against the spec either.  That check is the next file.
-/
namespace WasmBase
namespace Chips
namespace Ripemd

open Expr

/-! ## Geometry -/

def W : Nat := 32          -- bits per word
def STEPS : Nat := 80      -- steps per block
def NWORDS : Nat := 16     -- message words per block
def GROUPS : Nat := 5      -- 16-step groups, one `f` form each

def lC : Nat := 0          -- 0 .. 159      left working words
def rC : Nat := 160        -- 160 .. 319    right working words
def xC : Nat := 320        -- 320 .. 831    message words
def flC : Nat := 832       -- 832 .. 863    `f` of the left line
def frC : Nat := 864       -- 864 .. 895    `f` of the right line
def xlC : Nat := 896       -- 896 .. 927    selected word, left
def xrC : Nat := 928       -- 928 .. 959    selected word, right
def tC : Nat := 960        -- 960 .. 1215   chained sums, 8 words
def rotC : Nat := 1216     -- 1216 .. 1279  rotated `t3`, 2 words
def cyC : Nat := 1280      -- 1280 .. 1527  carries, 8 × 31
def selC : Nat := 1528     -- 1528 .. 1607  one-hot step selector
def ncols : Nat := 1608

def lBit (w k : Nat) : Nat := lC + W * w + k
def rBit (w k : Nat) : Nat := rC + W * w + k
def xBit (i k : Nat) : Nat := xC + W * i + k
def flBit (k : Nat) : Nat := flC + k
def frBit (k : Nat) : Nat := frC + k
def xlBit (k : Nat) : Nat := xlC + k
def xrBit (k : Nat) : Nat := xrC + k
def tBit (n k : Nat) : Nat := tC + W * n + k
def rotBit (b k : Nat) : Nat := rotC + W * b + k
def cyBit (n k : Nat) : Nat := cyC + 31 * n + k
def selE (j : Nat) : Nat := selC + j

def cols : List String :=
  ((List.range 5).flatMap fun w => (List.range W).map fun k => s!"L{w}_{k}") ++
  ((List.range 5).flatMap fun w => (List.range W).map fun k => s!"R{w}_{k}") ++
  ((List.range NWORDS).flatMap fun i => (List.range W).map fun k => s!"X{i}_{k}") ++
  ((List.range W).map fun k => s!"fL{k}") ++
  ((List.range W).map fun k => s!"fR{k}") ++
  ((List.range W).map fun k => s!"xL{k}") ++
  ((List.range W).map fun k => s!"xR{k}") ++
  ((List.range 8).flatMap fun n => (List.range W).map fun k => s!"t{n}_{k}") ++
  ((List.range 2).flatMap fun b => (List.range W).map fun k => s!"rot{b}_{k}") ++
  ((List.range 8).flatMap fun n => (List.range 31).map fun k => s!"cy{n}_{k}") ++
  ((List.range STEPS).map fun j => s!"sel{j}")

/-! ## The spec's constants and index arrays

Nothing is re-typed: `rl`, `rr`, `sl`, `sr`, `kl`, `kr` are read out of `NearSpecV3.Wasm.Crypto`
(`Crypto.lean:85-106`).  `sl`/`sr` are the rotation amounts, `rl`/`rr` the message-word indices and
`kl`/`kr` the group constants. -/

/-- `rl[j]`: the message word the left line reads at step `j`. -/
def rlVal (j : Nat) : Nat := NearSpecV3.Wasm.Crypto.rl.toList.getD j 0

/-- `rr[j]`: the message word the right line reads at step `j`. -/
def rrVal (j : Nat) : Nat := NearSpecV3.Wasm.Crypto.rr.toList.getD j 0

/-- `sl[j]`: the left line's rotation amount at step `j`. -/
def slVal (j : Nat) : Nat := (NearSpecV3.Wasm.Crypto.sl.toList.map (·.toNat)).getD j 0

/-- `sr[j]`: the right line's rotation amount at step `j`. -/
def srVal (j : Nat) : Nat := (NearSpecV3.Wasm.Crypto.sr.toList.map (·.toNat)).getD j 0

/-- `kl[g]`: the left line's constant for group `g`. -/
def klVal (g : Nat) : Nat := (NearSpecV3.Wasm.Crypto.kl.toList.map (·.toNat)).getD g 0

/-- `kr[g]`: the right line's constant for group `g`. -/
def krVal (g : Nat) : Nat := (NearSpecV3.Wasm.Crypto.kr.toList.map (·.toNat)).getD g 0

/-- Bit `k` of a natural: `(x >>> k) % 2`.  Parenthesised on purpose — `>>>` and `%` do not
associate the way the expression reads. -/
def bitOf (x k : Nat) : Nat := (x >>> k) % 2

def klBit (g k : Nat) : Nat := bitOf (klVal g) k
def krBit (g k : Nat) : Nat := bitOf (krVal g) k

/-! ## Expression builders

The state is bit-sliced, so every operation is a bit operation.  `xor2 a b = a + b − 2ab` is XOR on
two bits, `xor3` on three (`a+b+c−2(ab+ac+bc)+4abc`), `majE` the adder's carry (`ab+ac+bc`),
`chE a b c = ab + (1−a)c` the choice form.  Numerals are named because `simp` cannot see through
`OfNat Expr`. -/

def e0 : Expr := .c 0
def e1 : Expr := .c 1
def e2 : Expr := .c 2
def e4 : Expr := .c 4

def boolE (e : Expr) : Expr := e * (e - e1)
def xor2 (a b : Expr) : Expr := a + b - e2 * (a * b)
def andE (a b : Expr) : Expr := a * b
def notE (a : Expr) : Expr := e1 - a
def orE (a b : Expr) : Expr := a + b - a * b
def xor3 (a b c : Expr) : Expr := a + b + c - e2 * (a * b + a * c + b * c) + e4 * (a * b * c)
def chE (a b c : Expr) : Expr := a * b + (e1 - a) * c
/-- Boolean majority: `ab + ac + bc − 2abc`.  The naive `ab + ac + bc` is the *integer* sum of the
pairwise products, which is `3` (not `1`) when all three bits are set — so it is not a carry. -/
def majE (a b c : Expr) : Expr := a * b + a * c + b * c - e2 * (a * b * c)

def v (i : Nat) : Expr := .col i
def nv (i : Nat) : Expr := .nxt i

/-! ### The five `f` forms

`rf j b c d` (`Crypto.lean:110-115`) has five arms, chosen by `j/16`.  Bit `k` of each arm is a
polynomial in the bits of `b`, `c`, `d`. -/

def formBit (g : Nat) (b c d : Expr) : Expr :=
  match g with
  | 0 => xor3 b c d
  | 1 => chE b c d
  | 2 => xor2 (orE b (notE c)) d
  | 3 => b * d + c * (e1 - d)
  | _ => xor2 b (orE c (notE d))

/-- The left line's `f` bit: the three inputs are `bl, cl, dl`. -/
def formLB (g k : Nat) : Expr := formBit g (v (lBit 1 k)) (v (lBit 2 k)) (v (lBit 3 k))

/-- The right line's `f` bit: inputs `br, cr, dr`, at the mirrored group `4−g` (`rf (79−j)`). -/
def formRB (g k : Nat) : Expr := formBit (4 - g) (v (rBit 1 k)) (v (rBit 2 k)) (v (rBit 3 k))

def formB (b g k : Nat) : Expr := if b = 0 then formLB g k else formRB g k

/-- The row's `f` column bit: `fL` on the left line (`b = 0`), `fR` on the right. -/
def fColB (b k : Nat) : Expr := v ((if b = 0 then flC else frC) + k)

/-! ### Selector-gated selections

Every row-dependent quantity is a one-hot sum over the 80 steps: the group's selector sum (for the
`f` form), the message word `x[rl[j]]`, the rotation offset `sl[j]`, and the group constant
`kl[j/16]`.  Each is linear or degree 2, so gating a degree-3 form by a selector stays degree 4. -/

/-- `Σ_{j<16} sel_{16g+j}`: the selector sum of group `g`. -/
def gselAux (g : Nat) : Nat → Expr
  | 0 => e0
  | n + 1 => gselAux g n + v (selE (16 * g + n))

def gsel (g : Nat) : Expr := gselAux g 16

/-- The `f` form constraint: `Σ_g gsel_g · (fB_k − form_g)`, zero on every row. -/
def fSumAux (b k : Nat) : Nat → Expr
  | 0 => e0
  | n + 1 => fSumAux b k n + gselAux n 16 * (fColB b k - formB b n k)

def fConstrB (b k : Nat) : Expr := fSumAux b k GROUPS

/-- Bit `k` of the group constant `kl[j/16]` (left) or `kr[j/16]` (right), selected by the row. -/
def kSelAux (b k : Nat) : Nat → Expr
  | 0 => e0
  | n + 1 => kSelAux b k n + v (selE n) * Expr.c (if b = 0 then klBit (n / 16) k else krBit (n / 16) k)

def kSelB (b k : Nat) : Expr := kSelAux b k STEPS

/-- The message-word selection constraint: `Σ_j sel_j · (x_k − X[rl[j]]_k)`. -/
def xselAux (b k : Nat) : Nat → Expr
  | 0 => e0
  | n + 1 => xselAux b k n + v (selE n) * (v ((if b = 0 then xlC else xrC) + k) - v (xBit (if b = 0 then rlVal n else rrVal n) k))

def xselConstrB (b k : Nat) : Expr := xselAux b k STEPS

/-- The rotation constraint: `Σ_j sel_j · (rot_k − t3[(k − sl[j]) mod 32])`, and the right line's
`sr[j]` from `t6`. -/
def rotAux (b k : Nat) : Nat → Expr
  | 0 => e0
  | n + 1 => rotAux b k n + v (selE n) * (v (rotBit b k) - v (tBit (if b = 0 then 2 else 6) ((k + W - (if b = 0 then slVal n else srVal n)) % W)))

def rotConstrB (b k : Nat) : Expr := rotAux b k STEPS

/-! ### The adder chain

Each line is four binary additions: `t1 = al + fL`, `t2 = t1 + xL`, `t3 = t2 + kL`, `tf = rot + el`
(`n = 0..3` left, `n = 4..7` right).  A full adder per bit: sum `x ⊕ y ⊕ cyIn`, carry `maj`, with the
carry into bit 0 equal to zero and bit 31's carry dropped (mod 2³²). -/

def cyIn (n k : Nat) : Expr := if k = 0 then e0 else v (cyBit n (k - 1))

def addSum (n k : Nat) (x y : Expr) : Expr := xor3 x y (cyIn n k) - v (tBit n k)

def addCarry (n k : Nat) (x y : Expr) : Expr := majE x y (cyIn n k) - v (cyBit n k)

/-! Operand accessors: word `w` of the left line is `v (lBit w k)`, of the right line `v (rBit w k)`. -/

def alB (k : Nat) : Expr := v (lBit 0 k)
def blB (k : Nat) : Expr := v (lBit 1 k)
def clB (k : Nat) : Expr := v (lBit 2 k)
def dlB (k : Nat) : Expr := v (lBit 3 k)
def elB (k : Nat) : Expr := v (lBit 4 k)
def arB (k : Nat) : Expr := v (rBit 0 k)
def brB (k : Nat) : Expr := v (rBit 1 k)
def crB (k : Nat) : Expr := v (rBit 2 k)
def drB (k : Nat) : Expr := v (rBit 3 k)
def erB (k : Nat) : Expr := v (rBit 4 k)
def t0B (k : Nat) : Expr := v (tBit 0 k)
def t1B (k : Nat) : Expr := v (tBit 1 k)
def t2B (k : Nat) : Expr := v (tBit 2 k)
def t3B (k : Nat) : Expr := v (tBit 3 k)
def t4B (k : Nat) : Expr := v (tBit 4 k)
def t5B (k : Nat) : Expr := v (tBit 5 k)
def t6B (k : Nat) : Expr := v (tBit 6 k)
def t7B (k : Nat) : Expr := v (tBit 7 k)
def flB (k : Nat) : Expr := v (flBit k)
def frB (k : Nat) : Expr := v (frBit k)
def xlB (k : Nat) : Expr := v (xlBit k)
def xrB (k : Nat) : Expr := v (xrBit k)
def rotLB (k : Nat) : Expr := v (rotBit 0 k)
def rotRB (k : Nat) : Expr := v (rotBit 1 k)
def kSelLB (k : Nat) : Expr := kSelB 0 k
def kSelRB (k : Nat) : Expr := kSelB 1 k

def addSums (n : Nat) (x y : Nat → Expr) : List Expr :=
  (List.range W).map fun k => addSum n k (x k) (y k)

def addCarries (n : Nat) (x y : Nat → Expr) : List Expr :=
  (List.range 31).map fun k => addCarry n k (x k) (y k)

def addFam (n : Nat) (x y : Nat → Expr) : List Expr := addSums n x y ++ addCarries n x y

/-! ## The constraint families -/

def boolFam (n m : Nat) (f : Nat → Nat → Nat) : List Expr :=
  (List.range n).flatMap fun i => (List.range m).map fun j => boolE (v (f i j))

def boolFams : List (List Expr) :=
  [boolFam 5 W lBit, boolFam 5 W rBit, boolFam NWORDS W xBit,
   boolFam W 1 (fun k _ => flBit k), boolFam W 1 (fun k _ => frBit k),
   boolFam W 1 (fun k _ => xlBit k), boolFam W 1 (fun k _ => xrBit k),
   boolFam 8 W tBit, boolFam 2 W rotBit, boolFam 8 31 cyBit,
   boolFam STEPS 1 (fun j _ => selE j)]

def boolConstraints : List Expr := boolFams.flatten

def onehotAux : Nat → Expr
  | 0 => e0
  | n + 1 => onehotAux n + v (selE n)

def onehotSum : Expr := onehotAux STEPS

/-- The selector is one-hot: `Σ_j sel_j = 1`. -/
def selConstraints : List Expr := [onehotSum - e1]

def fConstraints : List Expr :=
  (List.range 2).flatMap fun b => (List.range W).map fun k => fConstrB b k

def xselConstraints : List Expr :=
  (List.range 2).flatMap fun b => (List.range W).map fun k => xselConstrB b k

def rotConstraints : List Expr :=
  (List.range 2).flatMap fun b => (List.range W).map fun k => rotConstrB b k

def adderConstraints : List Expr :=
  addFam 0 alB flB ++ addFam 1 t0B xlB ++ addFam 2 t1B kSelLB ++ addFam 3 rotLB elB ++
  addFam 4 arB frB ++ addFam 5 t4B xrB ++ addFam 6 t5B kSelRB ++ addFam 7 rotRB erB

/-- The shift: `al' = el`, `bl' = tf`, `cl' = bl`, `dl' = rotl32 cl 10`, `el' = dl`; mirrored on the
right line.  `rotl32 · 10` is a constant index shift, so it costs no column. -/
def shiftConstraints : List Expr :=
  (List.range W).flatMap fun k =>
    [nv (lBit 0 k) - elB k, nv (lBit 1 k) - t3B k, nv (lBit 2 k) - blB k,
     nv (lBit 3 k) - clB ((k + W - 10) % W), nv (lBit 4 k) - dlB k,
     nv (rBit 0 k) - erB k, nv (rBit 1 k) - t7B k, nv (rBit 2 k) - brB k,
     nv (rBit 3 k) - crB ((k + W - 10) % W), nv (rBit 4 k) - drB k]

/-- The row's constraints: booleanity, one-hot, `f`, message selection, rotation, additions, shift. -/
def constraints : List Expr :=
  boolConstraints ++ selConstraints ++ fConstraints ++ xselConstraints ++ rotConstraints ++
  adderConstraints ++ shiftConstraints

/-- Steps chain through `nxt`: no interaction. -/
def inters : List Inter := []

def table : Table := ⟨"RIPEMD160", cols, constraints, inters⟩

/-! ## Shape facts -/

theorem ncols_eq : ncols = 1608 := rfl

theorem cols_len : cols.length = ncols := by
  simp only [cols, ncols, W, STEPS, NWORDS, List.length_append, List.length_flatMap,
    List.length_map, List.length_range]
  decide

/-! ### The spec's constants, spot-checked against the arrays

These are the values the row's selector-gated constants must reproduce; each is a `decide` on the
spec's own literal array. -/

theorem rl_zero : rlVal 0 = 0 := by decide
theorem rl_last : rlVal 79 = 13 := by decide
theorem rr_zero : rrVal 0 = 5 := by decide
theorem rr_last : rrVal 79 = 11 := by decide
theorem sl_zero : slVal 0 = 11 := by decide
theorem sl_last : slVal 79 = 6 := by decide
theorem sr_zero : srVal 0 = 8 := by decide
theorem sr_last : srVal 79 = 11 := by decide
theorem kl_g4 : klVal 4 = 0xA953FD4E := by decide
theorem kr_g0 : krVal 0 = 0x50A28BE6 := by decide
theorem kr_g4 : krVal 4 = 0 := by decide
theorem klBit_g0_0 : klBit 0 0 = 0 := by decide
theorem krBit_g4_0 : krBit 4 0 = 0 := by decide
/-- **The index arrays are in range on every step.**  `xBit (rlVal j) k` is the column of message
word `rl[j]`, so `rlVal j ≥ 16` would silently point outside the `X` group; likewise `sl`/`sr` must
be `< 32` for the rotation index to be a rotation.  Kernel-checked over all 80 steps. -/
theorem rlVal_lt : ∀ j, j < STEPS → rlVal j < NWORDS := by decide
theorem rrVal_lt : ∀ j, j < STEPS → rrVal j < NWORDS := by decide
theorem slVal_lt : ∀ j, j < STEPS → slVal j < W := by decide
theorem srVal_lt : ∀ j, j < STEPS → srVal j < W := by decide

/-- **The five `f` forms are the spec's boolean functions.**  For every group and every bit triple,
the polynomial's value equals bit 0 of `NearSpecV3.Wasm.Crypto.rf` at that group's first step
(`j = 16g`).  This is what pins `formBit` to `rf` rather than to a re-statement of it. -/
def formValNat (g b c d : Nat) : Nat :=
  ((formBit g (Expr.c b) (Expr.c c) (Expr.c d)).eval
    ⟨fun _ => 0, fun _ => 0, fun _ => 0, false, false⟩).toNat

def rfBit (g b c d : Nat) : Nat :=
  (NearSpecV3.Wasm.Crypto.rf (16 * g) (UInt32.ofNat b) (UInt32.ofNat c)
    (UInt32.ofNat d)).toNat % 2

theorem formBit_is_spec :
    (List.range 5).all (fun g => (List.range 2).all (fun b => (List.range 2).all (fun c =>
      (List.range 2).all (fun d => formValNat g b c d == rfBit g b c d)))) = true := by
  decide

/-- **The check has teeth.**  Group 0 (`xor3`) and group 1 (`ch`) differ at `(1,1,0)`, so a table that
used one form for every group would fail `formBit_is_spec` — the equality is not `rfl`-shaped. -/
theorem formBit_groups_differ : formValNat 0 1 1 0 = 0 ∧ formValNat 1 1 1 0 = 1 := by
  decide

/-! ### Degree

The gated `f` form is the only degree-4 constraint; everything else is degree ≤ 3. -/

theorem deg_c (n : Nat) : (Expr.c n).degree = 0 := rfl
theorem deg_e0 : e0.degree = 0 := rfl
theorem deg_e1 : e1.degree = 0 := rfl
theorem deg_e2 : e2.degree = 0 := rfl
theorem deg_e4 : e4.degree = 0 := rfl
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

theorem xor3_le (a b c : Expr) (ha : a.degree ≤ 1) (hb : b.degree ≤ 1) (hc : c.degree ≤ 1) :
    (xor3 a b c).degree ≤ 3 := by
  simp only [xor3, deg_mul, deg_sub, deg_add, deg_e2, deg_e4]
  have h1 := Nat.le_max_left a.degree b.degree
  have h2 := Nat.le_max_right a.degree b.degree
  have h3 := Nat.le_max_left (max a.degree b.degree) c.degree
  have h4 := Nat.le_max_right (max a.degree b.degree) c.degree
  omega

theorem majE_le (a b c : Expr) (ha : a.degree ≤ 1) (hb : b.degree ≤ 1) (hc : c.degree ≤ 1) :
    (majE a b c).degree ≤ 3 := by
  simp only [majE, deg_mul, deg_add, deg_sub, deg_e2]
  have h1 := Nat.le_max_left a.degree b.degree
  have h2 := Nat.le_max_right a.degree b.degree
  have h3 := Nat.le_max_left (max a.degree b.degree) c.degree
  have h4 := Nat.le_max_right (max a.degree b.degree) c.degree
  omega

/-- **The majority polynomial is the boolean majority.**  On all eight bit triples:
`maj(a,b,c) = 1` iff at least two inputs are 1.  This is what makes `majE` a carry rather than a
count; the negative control below (`2` when all three are set) is what the first draft of this file
got wrong, and what `rowOk` caught. -/
def majValNat (a b c : Nat) : Nat :=
  ((majE (Expr.c a) (Expr.c b) (Expr.c c)).eval
    ⟨fun _ => 0, fun _ => 0, fun _ => 0, false, false⟩).toNat

theorem majE_is_carry :
    (List.range 2).all (fun a => (List.range 2).all (fun b => (List.range 2).all (fun c =>
      majValNat a b c == (if 2 ≤ a + b + c then 1 else 0)))) = true := by
  decide

/-- The negative control: the naive pairwise sum reads `3` at `(1,1,1)`, so `majE` is not it. -/
theorem majE_discriminates :
    (((Expr.c 1) * (Expr.c 1) + (Expr.c 1) * (Expr.c 1) + (Expr.c 1) * (Expr.c 1)).eval
      ⟨fun _ => 0, fun _ => 0, fun _ => 0, false, false⟩).toNat = 3 ∧ majValNat 1 1 1 = 1 := by
  decide

theorem chE_le (a b c : Expr) (ha : a.degree ≤ 1) (hb : b.degree ≤ 1) (hc : c.degree ≤ 1) :
    (chE a b c).degree ≤ 2 := by
  simp only [chE, deg_mul, deg_add, deg_sub, deg_e1]
  have h1 := Nat.le_max_left a.degree b.degree
  have h2 := Nat.le_max_right a.degree b.degree
  have h3 := Nat.le_max_left a.degree c.degree
  have h4 := Nat.le_max_right a.degree c.degree
  omega

theorem orE_le (a b : Expr) (ha : a.degree ≤ 1) (hb : b.degree ≤ 1) :
    (orE a b).degree ≤ 2 := by
  simp only [orE, deg_mul, deg_add, deg_sub]
  have h1 := Nat.le_max_left a.degree b.degree
  have h2 := Nat.le_max_right a.degree b.degree
  omega

theorem notE_le (a : Expr) (ha : a.degree ≤ 1) : (notE a).degree ≤ 1 := by
  simp only [notE, deg_sub, deg_e1]
  omega

theorem formBit_le (g : Nat) (b c d : Expr) (hb : b.degree ≤ 1) (hc : c.degree ≤ 1)
    (hd : d.degree ≤ 1) : (formBit g b c d).degree ≤ 3 := by
  unfold formBit
  split
  · exact xor3_le b c d hb hc hd
  · simp only [chE, deg_mul, deg_add, deg_sub, deg_e1]
    have h1 := Nat.le_max_left b.degree c.degree
    have h2 := Nat.le_max_right b.degree c.degree
    have h3 := Nat.le_max_left b.degree d.degree
    have h4 := Nat.le_max_right b.degree d.degree
    omega
  · have hnc : (notE c).degree ≤ 1 := notE_le c hc
    have hor : (orE b (notE c)).degree ≤ 2 := orE_le b (notE c) hb hnc
    simp only [xor2, deg_mul, deg_add, deg_sub, deg_e2]
    omega
  · simp only [deg_mul, deg_add, deg_sub, deg_e1]
    have h1 := Nat.le_max_left b.degree d.degree
    have h2 := Nat.le_max_right b.degree d.degree
    have h3 := Nat.le_max_left c.degree d.degree
    have h4 := Nat.le_max_right c.degree d.degree
    omega
  · have hnd : (notE d).degree ≤ 1 := notE_le d hd
    have hor : (orE c (notE d)).degree ≤ 2 := orE_le c (notE d) hc hnd
    simp only [xor2, deg_mul, deg_add, deg_sub, deg_e2]
    omega

theorem formLB_le (g k : Nat) : (formLB g k).degree ≤ 3 :=
  formBit_le g _ _ _ (by simp only [blB, deg_v]; omega)
    (by simp only [clB, deg_v]; omega) (by simp only [dlB, deg_v]; omega)

theorem formRB_le (g k : Nat) : (formRB g k).degree ≤ 3 :=
  formBit_le (4 - g) _ _ _ (by simp only [brB, deg_v]; omega)
    (by simp only [crB, deg_v]; omega) (by simp only [drB, deg_v]; omega)

theorem formB_le (b g k : Nat) : (formB b g k).degree ≤ 3 := by
  unfold formB
  split
  · exact formLB_le g k
  · exact formRB_le g k

theorem gselAux_le (g n : Nat) : (gselAux g n).degree ≤ 1 := by
  induction n with
  | zero => exact Nat.zero_le 1
  | succ m ih =>
    simp only [gselAux, deg_add, deg_mul, deg_v, deg_c]
    omega

theorem fColB_le (b k : Nat) : (fColB b k).degree ≤ 1 := by
  simp only [fColB, deg_v]
  omega

theorem fSumAux_le (b k n : Nat) : (fSumAux b k n).degree ≤ 4 := by
  induction n with
  | zero => exact Nat.zero_le 4
  | succ m ih =>
    simp only [fSumAux, deg_add, deg_mul, deg_sub, deg_v]
    have h1 := gselAux_le m 16
    have h2 := formB_le b m k
    have h3 := fColB_le b k
    omega

theorem fConstrB_le (b k : Nat) : (fConstrB b k).degree ≤ 4 := fSumAux_le b k GROUPS

theorem kSelAux_le (b k n : Nat) : (kSelAux b k n).degree ≤ 1 := by
  induction n with
  | zero => exact Nat.zero_le 1
  | succ m ih =>
    simp only [kSelAux, deg_add, deg_mul, deg_v, deg_c]
    omega

theorem kSelB_le (b k : Nat) : (kSelB b k).degree ≤ 1 := kSelAux_le b k STEPS

theorem xselAux_le (b k n : Nat) : (xselAux b k n).degree ≤ 2 := by
  induction n with
  | zero => exact Nat.zero_le 2
  | succ m ih =>
    simp only [xselAux, deg_add, deg_mul, deg_sub, deg_v]
    omega

theorem xselConstrB_le (b k : Nat) : (xselConstrB b k).degree ≤ 2 := xselAux_le b k STEPS

theorem rotAux_le (b k n : Nat) : (rotAux b k n).degree ≤ 2 := by
  induction n with
  | zero => exact Nat.zero_le 2
  | succ m ih =>
    simp only [rotAux, deg_add, deg_mul, deg_sub, deg_v]
    omega

theorem rotConstrB_le (b k : Nat) : (rotConstrB b k).degree ≤ 2 := rotAux_le b k STEPS

theorem deg_cyIn (n k : Nat) : (cyIn n k).degree ≤ 1 := by
  unfold cyIn
  split
  · simp only [deg_e0]; omega
  · simp only [deg_v]; omega

theorem addSum_le (n k : Nat) (x y : Expr) (hx : x.degree ≤ 1) (hy : y.degree ≤ 1) :
    (addSum n k x y).degree ≤ 3 := by
  simp only [addSum, deg_sub, deg_v]
  have h := xor3_le x y (cyIn n k) hx hy (deg_cyIn n k)
  omega

theorem addCarry_le (n k : Nat) (x y : Expr) (hx : x.degree ≤ 1) (hy : y.degree ≤ 1) :
    (addCarry n k x y).degree ≤ 3 := by
  simp only [addCarry, deg_sub, deg_v]
  have h := majE_le x y (cyIn n k) hx hy (deg_cyIn n k)
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
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact boolFam_le _ _ _ e he

theorem boolConstraints_le : ∀ e ∈ boolConstraints, e.degree ≤ 3 := by
  intro e he
  simp only [boolConstraints, List.mem_flatten] at he
  obtain ⟨l, hl, hel⟩ := he
  exact boolFams_le l hl e hel

theorem onehotAux_le (n : Nat) : (onehotAux n).degree ≤ 1 := by
  induction n with
  | zero => exact Nat.zero_le 1
  | succ m ih =>
    simp only [onehotAux, deg_add, deg_v]
    omega

theorem onehotSum_le : onehotSum.degree ≤ 1 := onehotAux_le STEPS

theorem selConstraints_le : ∀ e ∈ selConstraints, e.degree ≤ 3 := by
  intro e he
  simp only [selConstraints, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl
  simp only [deg_sub, deg_e1]
  have h := onehotSum_le
  omega

theorem fConstraints_le : ∀ e ∈ fConstraints, e.degree ≤ 4 := by
  intro e he
  simp only [fConstraints, List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨b, _, k, _, rfl⟩ := he
  exact fConstrB_le b k

theorem xselConstraints_le : ∀ e ∈ xselConstraints, e.degree ≤ 2 := by
  intro e he
  simp only [xselConstraints, List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨b, _, k, _, rfl⟩ := he
  exact xselConstrB_le b k

theorem rotConstraints_le : ∀ e ∈ rotConstraints, e.degree ≤ 2 := by
  intro e he
  simp only [rotConstraints, List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨b, _, k, _, rfl⟩ := he
  exact rotConstrB_le b k

theorem addSums_le (n : Nat) (x y : Nat → Expr) (hx : ∀ k, (x k).degree ≤ 1)
    (hy : ∀ k, (y k).degree ≤ 1) : ∀ e ∈ addSums n x y, e.degree ≤ 3 := by
  intro e he
  simp only [addSums, List.mem_map, List.mem_range] at he
  obtain ⟨k, _, rfl⟩ := he
  exact addSum_le n k (x k) (y k) (hx k) (hy k)

theorem addCarries_le (n : Nat) (x y : Nat → Expr) (hx : ∀ k, (x k).degree ≤ 1)
    (hy : ∀ k, (y k).degree ≤ 1) : ∀ e ∈ addCarries n x y, e.degree ≤ 3 := by
  intro e he
  simp only [addCarries, List.mem_map, List.mem_range] at he
  obtain ⟨k, _, rfl⟩ := he
  exact addCarry_le n k (x k) (y k) (hx k) (hy k)

theorem addFam_le (n : Nat) (x y : Nat → Expr) (hx : ∀ k, (x k).degree ≤ 1)
    (hy : ∀ k, (y k).degree ≤ 1) : ∀ e ∈ addFam n x y, e.degree ≤ 3 := by
  intro e he
  simp only [addFam, List.mem_append] at he
  rcases he with h | h
  · exact addSums_le n x y hx hy e h
  · exact addCarries_le n x y hx hy e h

theorem shiftConstraints_le : ∀ e ∈ shiftConstraints, e.degree ≤ 2 := by
  intro e he
  simp only [shiftConstraints, List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨k, _, he⟩ := he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [deg_sub, v, nv, deg_col, deg_nxt, elB, t3B, blB, clB, dlB, erB, t7B, brB, crB,
      drB]; omega)

theorem adderConstraints_le : ∀ e ∈ adderConstraints, e.degree ≤ 3 := by
  intro e he
  simp only [adderConstraints, List.mem_append] at he
  rcases he with (((((((h | h) | h) | h) | h) | h) | h) | h)
  · exact addFam_le 0 _ _ (by intro k; simp only [alB, deg_v]; omega)
      (by intro k; simp only [flB, deg_v]; omega) e h
  · exact addFam_le 1 _ _ (by intro k; simp only [t0B, deg_v]; omega)
      (by intro k; simp only [xlB, deg_v]; omega) e h
  · exact addFam_le 2 _ _ (by intro k; simp only [t1B, deg_v]; omega)
      (by intro k; exact kSelB_le 0 k) e h
  · exact addFam_le 3 _ _ (by intro k; simp only [rotLB, deg_v]; omega)
      (by intro k; simp only [elB, deg_v]; omega) e h
  · exact addFam_le 4 _ _ (by intro k; simp only [arB, deg_v]; omega)
      (by intro k; simp only [frB, deg_v]; omega) e h
  · exact addFam_le 5 _ _ (by intro k; simp only [t4B, deg_v]; omega)
      (by intro k; simp only [xrB, deg_v]; omega) e h
  · exact addFam_le 6 _ _ (by intro k; simp only [t5B, deg_v]; omega)
      (by intro k; exact kSelB_le 1 k) e h
  · exact addFam_le 7 _ _ (by intro k; simp only [rotRB, deg_v]; omega)
      (by intro k; simp only [erB, deg_v]; omega) e h

theorem constraints_le : ∀ e ∈ constraints, e.degree ≤ 4 := by
  intro e he
  simp only [constraints, List.mem_append] at he
  rcases he with ((((((he | he) | he) | he) | he) | he) | he)
  · exact Nat.le_trans (boolConstraints_le e he) (by decide)
  · exact Nat.le_trans (selConstraints_le e he) (by decide)
  · exact fConstraints_le e he
  · exact Nat.le_trans (xselConstraints_le e he) (by decide)
  · exact Nat.le_trans (rotConstraints_le e he) (by decide)
  · exact Nat.le_trans (adderConstraints_le e he) (by decide)
  · exact Nat.le_trans (shiftConstraints_le e he) (by decide)

/-! ## Counts -/

set_option maxRecDepth 1000000

theorem boolFams_len : boolFams.length = 11 := rfl

theorem adderConstraints_len : adderConstraints.length = 504 := by
  simp only [adderConstraints, addFam, addSums, addCarries, List.length_append, List.length_map,
    List.length_range, W]

theorem constraints_len : constraints.length = 2625 := by
  simp only [constraints, boolConstraints, boolFams, boolFam, selConstraints, fConstraints,
    xselConstraints, rotConstraints, adderConstraints, shiftConstraints, addFam, addSums,
    addCarries, List.length_append, List.length_flatten, List.length_flatMap, List.length_map,
    List.length_range, List.length_cons, List.length_nil, W, STEPS, NWORDS, GROUPS]
  decide

/-- Steps carry no interaction at all. -/
theorem inters_len : inters.length = 0 := rfl

end Ripemd
end Chips
end WasmBase
