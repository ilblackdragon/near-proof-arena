/-!
# GF(2⁸) arithmetic and matrices of `reed-solomon-erasure` 6.0.0 (`galois_8`)

Leaf module of `near/pv86/chunk-validation/v0`, used by `NearSpecV3.ReedSolomon`
(the chunk-body erasure code of `validate_chunk_with_encoded_merkle_root`).
Paths below are relative to the crate root
`~/.cargo/registry/src/index.crates.io-*/reed-solomon-erasure-6.0.0/`.

## Field (`build.rs`, `src/galois_8.rs`)
* `GENERATING_POLYNOMIAL = 29` (`build.rs:11`); `gen_log_table` (`build.rs:13-28`) walks
  `b = 1, 2, 4, …` with `b <<= 1; if b ≥ 256 { b = (b − 256) ^ 29 }`, i.e. powers of the
  generator `2` modulo `x⁸+x⁴+x³+x²+1` (`0x11D`), and records `LOG[b] = log`;
  `gen_exp_table` (`build.rs:32-42`) is its inverse, duplicated to 510 entries;
  `multiply` (`build.rs:44-53`) = `0` if either operand is `0`, else `EXP[LOG a + LOG b]`;
  `MUL_TABLE[a][b]` (`build.rs:55-68`) tabulates it, and `galois_8::mul`
  (`src/galois_8.rs:68-70`) is that table lookup.
* `add` = XOR (`src/galois_8.rs:57-61`).
* `div a b` (`src/galois_8.rs:73-88`): `0` if `a = 0`, panic if `b = 0`, else
  `EXP[(LOG a − LOG b) mod 255]`.
* `exp a n` (`src/galois_8.rs:90-103`): `1` if `n = 0` (so `0⁰ = 1`), `0` if `a = 0`,
  else `EXP[(LOG a · n) mod 255]`.
* `nth n = n as u8` (`src/galois_8.rs:37-39`, `src/lib.rs:84-93`, panics for `n ≥ 256`).

We define multiplication as the carry-less ("Russian peasant") product reduced modulo
`0x11D` (`gfMul`), which is kernel-cheap. Because `2` is primitive for `0x11D`, the
crate's log/exp tables describe exactly this multiplication; to make that a checked fact
rather than an argument we also transcribe `build.rs` literally (`logTable`, `expTable`,
`gfMulTable`, `gfDivTable`, `gfExpTable`) and the test executable `nearspec-v3-test-rs`
compares them on all 256 × 256 operand pairs. Division is `a · b²⁵⁴` and `exp` is
iterated multiplication, also compared exhaustively against the table versions.

## Matrices (`src/matrix.rs`)
Row-major `List (List Nat)` with entries in `[0, 256)`.
* `vandermonde rows cols` (`matrix.rs:263-276`): `V[r][c] = exp(nth r, c) = r^c`.
* `multiply` (`matrix.rs:119-139`), `augment` (`:141-160`), `sub_matrix` (`:162-170`),
  `identity` (`:95-101`).
* `gaussian_elim` (`matrix.rs:195-247`) and `invert` (`matrix.rs:249-261`): transcribed
  step by step (`gaussElim`, `invert`), including the row-swap pivot search and the
  `SingularMatrix` error (`none`). (The inverse of an invertible matrix is unique, so any
  correct Gauss–Jordan would give the same result; transcribing the crate's also pins
  down *when* it fails.)

Everything is structurally recursive over `Nat`/`List`, kernel-reducible.
-/

namespace NearSpecV3

/-! ## Field arithmetic -/

/-- The reduction polynomial `x⁸+x⁴+x³+x²+1` (`build.rs:11`: `29 = 0x11D − 0x100`). -/
def gfPoly : Nat := 0x11D

/-- Carry-less multiply-and-reduce, 8 rounds (one per bit of `b`). -/
def gfMulAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, a, b, acc =>
    let acc := if b % 2 = 1 then acc ^^^ a else acc
    let a2 := a <<< 1
    let a2 := if a2 ≥ 256 then a2 ^^^ gfPoly else a2
    gfMulAux n a2 (b >>> 1) acc

/-- GF(2⁸) product of `a, b < 256` (= `galois_8::mul`, `src/galois_8.rs:68-70`). -/
def gfMul (a b : Nat) : Nat := gfMulAux 8 a b 0

/-- `a ^ n` by repeated multiplication; `a⁰ = 1` (so `0⁰ = 1`), matching `galois_8::exp`
(`src/galois_8.rs:90-103`). -/
def gfPow (a : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => gfMul (gfPow a n) a

/-- Multiplicative inverse `b⁻¹ = b²⁵⁴` (for `b ≠ 0`; `gfInv 0 = 0`). -/
def gfInv (b : Nat) : Nat := gfPow b 254

/-- `galois_8::div` (`src/galois_8.rs:73-88`) for `b ≠ 0`. (`b = 0` panics in the crate;
the only call site, `gaussian_elim`'s pivot scaling `div(1, pivot)`, has `pivot ≠ 0`.) -/
def gfDiv (a b : Nat) : Nat := if a = 0 then 0 else gfMul a (gfInv b)

/-! ## Literal transcription of `build.rs` tables (checked equal in the test exe) -/

/-- `gen_log_table(29)` (`build.rs:13-28`). Entry `0` stays `0` (never used). -/
def logTable : Array Nat :=
  let rec go : Nat → Nat → Nat → Array Nat → Array Nat
    | 0, _, _, t => t
    | n + 1, log, b, t =>
      let t := t.set! b log
      let b := b <<< 1
      let b := if 256 ≤ b then (b - 256) ^^^ 29 else b
      go n (log + 1) b t
  go 255 0 1 (Array.replicate 256 0)

/-- `gen_exp_table` (`build.rs:32-42`): 510 entries, `EXP[l] = EXP[l + 255]`. -/
def expTable : Array Nat :=
  (List.range 255).foldl (fun t j =>
    let i := j + 1
    let l := logTable[i]!
    (t.set! l i).set! (l + 255) i) (Array.replicate 510 0)

/-- `multiply` / `MUL_TABLE` (`build.rs:44-68`). -/
def gfMulTable (a b : Nat) : Nat :=
  if a = 0 ∨ b = 0 then 0 else expTable[logTable[a]! + logTable[b]!]!

/-- `galois_8::div` (`src/galois_8.rs:73-88`), `b ≠ 0`. -/
def gfDivTable (a b : Nat) : Nat :=
  if a = 0 then 0 else expTable[(logTable[a]! + 255 - logTable[b]!) % 255]!

/-- `galois_8::exp` (`src/galois_8.rs:90-103`). -/
def gfExpTable (a n : Nat) : Nat :=
  if n = 0 then 1 else if a = 0 then 0 else expTable[(logTable[a]! * n) % 255]!

/-! ## Matrices over GF(2⁸) (`src/matrix.rs`) -/

abbrev GFMat := List (List Nat)

def GFMat.get (m : GFMat) (r c : Nat) : Nat := (m.getD r []).getD c 0

/-- `Matrix::identity` (`matrix.rs:95-101`). -/
def GFMat.identity (n : Nat) : GFMat :=
  (List.range n).map fun i => (List.range n).map fun j => if i = j then 1 else 0

/-- `Matrix::vandermonde` (`matrix.rs:263-276`): `V[r][c] = exp(nth r, c)`. -/
def GFMat.vandermonde (rows cols : Nat) : GFMat :=
  (List.range rows).map fun r => (List.range cols).map fun c => gfPow r c

/-- XOR-sum of a list of field elements (`F::add` fold, `matrix.rs:129-134`). -/
def gfSum (l : List Nat) : Nat := l.foldl (· ^^^ ·) 0

/-- `Matrix::multiply` (`matrix.rs:119-139`): `result[r][c] = Σᵢ lhs[r][i] · rhs[i][c]`;
column count of `lhs` = row count of `rhs` (always true here by construction). The columns
of `rhs` are extracted once (a transpose) so each entry is a `zipWith` over a row and a
column. -/
def GFMat.multiply (lhs rhs : GFMat) : GFMat :=
  let cols := (List.range (rhs.headD []).length).map fun c => rhs.map fun row => row.getD c 0
  lhs.map fun row => cols.map fun col => gfSum (List.zipWith gfMul row col)

/-- `Matrix::augment` (`matrix.rs:141-160`). -/
def GFMat.augment (lhs rhs : GFMat) : GFMat := List.zipWith (· ++ ·) lhs rhs

/-- `Matrix::sub_matrix(rmin, cmin, rmax, cmax)` (`matrix.rs:162-170`). -/
def GFMat.subMatrix (m : GFMat) (rmin cmin rmax cmax : Nat) : GFMat :=
  ((m.drop rmin).take (rmax - rmin)).map fun row => (row.drop cmin).take (cmax - cmin)

/-- `Matrix::swap_rows` (`matrix.rs:178-189`). -/
def GFMat.swapRows (m : GFMat) (r1 r2 : Nat) : GFMat :=
  if r1 = r2 then m else
    let a := m.getD r1 []
    let b := m.getD r2 []
    (m.set r1 b).set r2 a

/-- `row_dst ← row_dst + scale · row_src` (the elimination step, `matrix.rs:219-228`,
`:233-245`). -/
def GFMat.addScaledRow (m : GFMat) (dst src scale : Nat) : GFMat :=
  let s := m.getD src []
  m.set dst (List.zipWith (fun x y => x ^^^ gfMul scale y) (m.getD dst []) s)

/-- Pivot search (`matrix.rs:197-204`): first `r_below ∈ (r, n)` with a nonzero entry in
column `r`; swap it up. -/
def GFMat.pivot (m : GFMat) (n r : Nat) : GFMat :=
  if m.get r r = 0 then
    match (List.range' (r + 1) (n - (r + 1))).find? (fun rb => m.get rb r != 0) with
    | some rb => m.swapRows r rb
    | none => m
  else m

/-- Forward-elimination step for row `r` (`matrix.rs:196-230`); `none` = `SingularMatrix`. -/
def GFMat.forwardStep (n : Nat) (m : GFMat) (r : Nat) : Option GFMat :=
  let m := m.pivot n r
  let p := m.get r r
  if p = 0 then none else
  -- Scale to 1 (`matrix.rs:209-215`): row r ← div(1, p) · row r.
  let m := if p ≠ 1 then
      let scale := gfDiv 1 p
      m.set r ((m.getD r []).map fun x => gfMul scale x)
    else m
  -- Clear below (`matrix.rs:216-229`).
  some <| (List.range' (r + 1) (n - (r + 1))).foldl (fun m rb =>
    let s := m.get rb r
    if s ≠ 0 then m.addScaledRow rb r s else m) m

/-- `Matrix::gaussian_elim` (`matrix.rs:195-247`) on a matrix with `n` rows. -/
def GFMat.gaussElim (m : GFMat) (n : Nat) : Option GFMat := do
  let m ← (List.range n).foldlM (GFMat.forwardStep n) m
  -- Clear above the diagonal (`matrix.rs:232-245`).
  pure <| (List.range n).foldl (fun m d =>
    (List.range d).foldl (fun m ra =>
      let s := m.get ra d
      if s ≠ 0 then m.addScaledRow ra d s else m) m) m

/-- `Matrix::invert` (`matrix.rs:249-261`) of an `n × n` matrix; `none` iff singular. -/
def GFMat.invert (m : GFMat) (n : Nat) : Option GFMat := do
  let w ← (m.augment (GFMat.identity n)).gaussElim n
  pure (w.subMatrix 0 n n (2 * n))

end NearSpecV3
