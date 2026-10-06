import ZkFormal.Chacha.Sound.Contract

/-!
# ZkFormal.Chacha.Gen — the honest trace of the ChaCha20 block table `chachaV3`

One request `(key, ctr, used)` asks for block `ctr` of `key`; `used[w]` says whether
word `w` of the block is provided on `busChacha`.  Every request is laid out as one
86-row block (`I0, I1`, 80 quarter-round rows `Q dr p`, `F0..F3`), in list order, and
the table is padded with all-zero rows up to `2^honestLog` rows.

`rowCell X c` gives every cell as a `Nat < 2^16` (limbs, bits, carries, flags), so the
field embedding `Fp.ofNat` is injective on honest cells.  The definitions read the
`Nat`-level spec (ZkFormal.Chacha.Spec) directly.

This file is also the reference for a Rust trace generator: the cell formulas below
are the specification, column by column (see the layout table in
ZkFormal.Chacha.Table):

| columns | value on a row |
|---|---|
| `S i l = 2i+l` | limb `l` of `sWord X i` (state before the row's quarter-round) |
| `X m b = 32+32m+b` | bit `b` of `xWord X m` |
| `C q l = 224+2q+l` | `cCell X q l` (carry out of limb `l` of addition `q`) |
| `K j l = 232+2j+l` | limb `l` of `kWord X j` (key word `j < 8`, counter `j = 8`) |
| `250 + k`, `k < 18` | `kflag X.kd k`: `I0, I1, P0..P7, F0..F3, Dr0..Dr3` |
| `M kk = 268+kk` | `mflag X kk`: on `F j`, `used[4kk+j]` |
-/

namespace ZkFormal.Chacha.Gen

open NearSpecV3 ZkFormal.Chacha

/-- One request: block `ctr` of `key`; `used[w]`: word `w` is provided (multiplicity bit). -/
structure Req where
  key : List Nat
  ctr : Nat
  used : List Bool

/-- Requests the generator supports. -/
def ReqOk (R : Req) : Prop :=
  R.key.length = 8 ∧ (∀ x ∈ R.key, x < 2 ^ 32) ∧ R.ctr < 2 ^ 26 ∧ R.used.length = 16

/-- Row descriptors.  `q R dr p` is quarter-round `8·dr + p` (double round `dr < 10`,
position `p < 8`). -/
inductive Row where
  | i0 (R : Req)
  | i1 (R : Req)
  | q (R : Req) (dr p : Nat)
  | f (R : Req) (j : Nat)
  | pad

/-- The row kind without the request data (what the flag columns depend on). -/
inductive Kd where
  | i0 | i1 | q (dr p : Nat) | f (j : Nat) | pad
  deriving DecidableEq, Repr

def Row.kd : Row → Kd
  | .i0 _ => .i0
  | .i1 _ => .i1
  | .q _ dr p => .q dr p
  | .f _ j => .f j
  | .pad => .pad

/-! ## Word-level helpers -/

/-- 16-bit limb `l` of `x`. -/
def limbN (x l : Nat) : Nat := x / 2 ^ (16 * l) % 65536

/-- Carry out of limb `l` of the limb-wise addition `x + y` (low limb first). -/
def carry (x y l : Nat) : Nat :=
  let c0 := (limbN x 0 + limbN y 0) / 65536
  if l = 0 then c0 else (limbN x 1 + limbN y 1 + c0) / 65536

/-- The input state of a request. -/
def init (R : Req) : Array Nat := initArr R.key R.ctr

/-- All intermediate words of one quarter-round on `(a, b, c, d)` (`qrf` order). -/
structure QW where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  a1 : Nat
  d1 : Nat
  c1 : Nat
  b1 : Nat
  a2 : Nat
  d2 : Nat
  c2 : Nat
  b2 : Nat

def qw (a b c d : Nat) : QW :=
  let a1 := add32 a b
  let d1 := rotl32 (d ^^^ a1) 16
  let c1 := add32 c d1
  let b1 := rotl32 (b ^^^ c1) 12
  let a2 := add32 a1 b1
  let d2 := rotl32 (d1 ^^^ a2) 8
  let c2 := add32 c1 d2
  let b2 := rotl32 (b1 ^^^ c2) 7
  ⟨a, b, c, d, a1, d1, c1, b1, a2, d2, c2, b2⟩

/-- State before quarter-round `8·dr + p` of request `R`. -/
def qState (R : Req) (dr p : Nat) : Array Nat := stBefore (init R) (8 * dr + p)

/-- The quarter-round words of row `Q dr p`. -/
def qwOf (R : Req) (dr p : Nat) : QW :=
  let s := qState R dr p
  let g := grp p
  qw s[g.1]! s[g.2.1]! s[g.2.2.1]! s[g.2.2.2]!

/-- State after the 80 quarter-rounds. -/
def fin (R : Req) : Array Nat := stBefore (init R) 80

/-- Output word `i` of the block: `add32 (fin[i]) (init[i])` (`= chachaBlock key ctr [i]`). -/
def outW (R : Req) (i : Nat) : Nat := add32 (fin R)[i]! (init R)[i]!

/-! ## Cell values, by column group -/

/-- State word of slot `i` before the row's quarter-round. -/
def sWord : Row → Nat → Nat
  | .i0 R, i => (init R)[i]!
  | .i1 R, i => (init R)[i]!
  | .q R dr p, i => (qState R dr p)[i]!
  | .f R _, i => (fin R)[i]!
  | .pad, _ => 0

/-- The six bit-decomposed words `X m`. -/
def xWord : Row → Nat → Nat
  | .i0 R, m => if m < 6 then R.key.getD m 0 else 0
  | .i1 R, m => if m < 2 then R.key.getD (6 + m) 0 else if m = 2 then R.ctr else 0
  | .q R dr p, m =>
    let w := qwOf R dr p
    match m with
    | 0 => w.b | 1 => w.d | 2 => w.a1 | 3 => w.c1 | 4 => w.a2 | 5 => w.c2 | _ => 0
  | .f R j, m => if m < 4 then outW R (4 * m + j) else 0
  | .pad, _ => 0

/-- Carry bits `C q l`. -/
def cCell : Row → Nat → Nat → Nat
  | .q R dr p, q, l =>
    let w := qwOf R dr p
    match q with
    | 0 => carry w.a w.b l | 1 => carry w.c w.d1 l | 2 => carry w.a1 w.b1 l
    | 3 => carry w.c1 w.d2 l | _ => 0
  | .f R j, kk, l => if kk < 4 then carry (fin R)[4 * kk + j]! (init R)[4 * kk + j]! l else 0
  | _, _, _ => 0

/-- Key word `j < 8` / counter `j = 8` of the row's block. -/
def kWord : Row → Nat → Nat
  | .pad, _ => 0
  | .i0 R, j | .i1 R, j | .q R _ _, j | .f R _, j =>
    if j < 8 then R.key.getD j 0 else if j = 8 then R.ctr else 0

/-- Flag / counter columns `250 + k`, `k < 18`: `I0, I1, P0..P7, F0..F3, Dr0..Dr3`. -/
def kflag : Kd → Nat → Nat
  | .i0, k => if k = 0 then 1 else 0
  | .i1, k => if k = 1 then 1 else 0
  | .q dr p, k => if k = 2 + p then 1 else if 14 ≤ k ∧ k < 18 then bt dr (k - 14) else 0
  | .f j, k => if k = 10 + j then 1 else 0
  | .pad, _ => 0

/-- Multiplicity bit `M kk`. -/
def mflag : Row → Nat → Nat
  | .f R j, kk => if R.used.getD (4 * kk + j) false then 1 else 0
  | _, _ => 0

/-- **Cell `c` of a row.** -/
def rowCell (X : Row) (c : Nat) : Nat :=
  if c < 32 then limbN (sWord X (c / 2)) (c % 2)
  else if c < 224 then bt (xWord X ((c - 32) / 32)) ((c - 32) % 32)
  else if c < 232 then cCell X ((c - 224) / 2) ((c - 224) % 2)
  else if c < 250 then limbN (kWord X ((c - 232) / 2)) ((c - 232) % 2)
  else if c < 268 then kflag X.kd (c - 250)
  else if c < 272 then (if c - 268 < 4 then mflag X (c - 268) else 0)
  else 0

/-! ## Rows -/

/-- Row `m < 86` of the block of `R`. -/
def posRow (R : Req) (m : Nat) : Row :=
  if m = 0 then .i0 R
  else if m = 1 then .i1 R
  else if m < 82 then .q R ((m - 2) / 8) ((m - 2) % 8)
  else .f R (m - 82)

def blockRows (R : Req) : List Row := (List.range 86).map (posRow R)

def honestRows (reqs : List Req) : List Row := reqs.flatMap blockRows

/-- Smallest `log` with `n ≤ 2^log`. -/
def clog2 (n : Nat) : Nat := go n 0 where
  go : Nat → Nat → Nat
    | 0, acc => acc
    | fuel + 1, acc => if n ≤ 2 ^ acc then acc else go fuel (acc + 1)

def honestLog (reqs : List Req) : Nat := max 1 (clog2 (86 * reqs.length))

def honestCell (reqs : List Req) (r c : Nat) : Nat := rowCell ((honestRows reqs).getD r .pad) c

def honestTrace (reqs : List Req) : ZkFormal.Air.Trace ZkFormal.Algebra.Fp :=
  ⟨fun _ => honestLog reqs, fun _ r c => ZkFormal.Algebra.Fp.ofNat (honestCell reqs r c)⟩

/-! ## Expected bus traffic -/

/-- Messages provided by row `F j` of request `R` (outputs `kk = 0..3`, word `4kk + j`). -/
def fMsgs (R : Req) (j : Nat) : List (List ZkFormal.Algebra.Fp) :=
  ((List.range 4).filter (fun kk => R.used.getD (4 * kk + j) false)).map fun kk =>
    Sound.chachaMsg R.key R.ctr (4 * kk + j) ((chachaBlock R.key R.ctr)[4 * kk + j]!)

/-- All messages provided on `busChacha` (multiplicity one each), in row order: per request,
per `F j` row, words `j, 4+j, 8+j, 12+j` that are used. -/
def expected (reqs : List Req) : List (List ZkFormal.Algebra.Fp) :=
  reqs.flatMap fun R => (List.range 4).flatMap (fMsgs R)

end ZkFormal.Chacha.Gen
