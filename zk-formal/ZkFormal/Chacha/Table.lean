import ZkFormal.Air.Basic
import ZkFormal.Chacha.Spec

/-!
# ZkFormal.Chacha.Table — the ChaCha20 block table `chachaV3` (np-udr-stark-v2)

## Layout (272 columns)

One block takes 86 rows: `I0, I1` (input), 80 quarter-round rows `Q` (one ChaCha20
quarter-round each; double round `dr < 10`, position `p < 8`), and 4 feed-forward rows
`F0..F3`.  Padding rows are all zero.

| columns | name | meaning |
|---|---|---|
| `[0,32)` | `S i l` | 16-bit limb `l` of state slot `i < 16` *before* this row's quarter-round |
| `[32,224)` | `X m b` | six 32-bit words as bits (`Q`: `b, d, a₁, c₁, a₂, c₂`; `F`: outputs; `I`: key/ctr range checks) |
| `[224,232)` | `C q l` | carry bit of limb `l` of addition `q` |
| `[232,250)` | `K j l` | key word `j < 8`, counter (`j = 8`), 16-bit limbs (constant over a block) |
| `250, 251` | `I0, I1` | input rows |
| `[252,260)` | `P p` | quarter-round row, position `p` in the double round |
| `[260,264)` | `F j` | feed-forward row `j` (outputs words `j, 4+j, 8+j, 12+j`) |
| `[264,268)` | `Dr b` | bits of the double-round counter `dr ≤ 9` |
| `[268,272)` | `M k` | multiplicity of output `k` of an `F` row |

The state lives in its natural slot order.  Quarter-round `p` reads/writes slots
`grp p = (a, b, c, d)`; the slot inputs are selected by `Σ_p P_p · S[slot_p]`.
`b` and `d` are bit-decomposed (`X0`, `X1`), `a₁, c₁, a₂, c₂` are committed as bits,
and the rotated xors `d₁, b₁, d₂, b₂` are degree-2/3 expressions in those bits.

## Bus

`busChacha`, *sent* by `F` rows (multiplicity bit `M k`): the 20-element message
`[K0lo, K0hi, …, K7lo, K7hi, ctr, idx, wlo, whi]` with `ctr = K8lo + 2^16·K8hi` and
`w = (chachaBlock key ctr)[idx]` (`chacha_contract`).
-/

namespace ZkFormal.Chacha.Table

open ZkFormal.Air

/-! ## Columns -/

def colS (i l : Nat) : Nat := 2 * i + l
def colX (m b : Nat) : Nat := 32 + 32 * m + b
def colC (q l : Nat) : Nat := 224 + 2 * q + l
def colK (j l : Nat) : Nat := 232 + 2 * j + l
def colI0 : Nat := 250
def colI1 : Nat := 251
def colP (p : Nat) : Nat := 252 + p
def colF (j : Nat) : Nat := 260 + j
def colDr (b : Nat) : Nat := 264 + b
def colM (k : Nat) : Nat := 268 + k
def width : Nat := 272

/-- Boolean columns: bits, carries, flags, `dr` bits, multiplicities. -/
def boolCols : List Nat := List.range' 32 200 ++ List.range' 250 22

/-- All row-kind flags. -/
def flagCols : List Nat := [colI0, colI1] ++ (List.range 8).map colP ++ (List.range 4).map colF

/-! ## Expression builders -/

namespace E
def c (x : Nat) : Expr := .col x false
def n (x : Nat) : Expr := .col x true
def k (v : Nat) : Expr := .const v
def sub (a b : Expr) : Expr := .add a (.neg b)
def sum : List Expr → Expr
  | [] => .const 0
  | e :: es => .add e (sum es)
def smul (v : Nat) (e : Expr) : Expr := .mul (.const v) e
def xor2 (x y : Expr) : Expr := sub (.add x y) (smul 2 (.mul x y))
/-- 16-bit limb `l` of the word whose bit `b` is `f b`. -/
def limb (f : Nat → Expr) (l : Nat) : Expr :=
  sum ((List.range 16).map fun b => smul (2 ^ b) (f (16 * l + b)))
/-- `Σ_{x<n} c (col x) · f x`: select by a one-hot flag group. -/
def sel (col : Nat → Nat) (n : Nat) (f : Nat → Expr) : Expr :=
  sum ((List.range n).map fun x => .mul (c (col x)) (f x))
/-- `Σ terms + cin − (res + 2^16·cout)`. -/
def addE (terms : List Expr) (cin res cout : Expr) : Expr :=
  sub (.add (sum terms) cin) (.add res (smul 65536 cout))
end E

open E

/-- Bit `b` of rotated word (`rotl32 · k`) of bit function `f`. -/
def rot (f : Nat → Expr) (k : Nat) (b : Nat) : Expr := f ((b + 32 - k) % 32)

/-- Bit columns of word `m`. -/
def xb (m : Nat) (b : Nat) : Expr := c (colX m b)

def d1 (b : Nat) : Expr := xor2 (rot (xb 1) 16 b) (rot (xb 2) 16 b)
def b1 (b : Nat) : Expr := xor2 (rot (xb 0) 12 b) (rot (xb 3) 12 b)
def d2 (b : Nat) : Expr := xor2 (rot d1 8 b) (rot (xb 4) 8 b)
def b2 (b : Nat) : Expr := xor2 (rot b1 7 b) (rot (xb 5) 7 b)

/-- Carry-in of limb `l` of addition `q`. -/
def cin (q l : Nat) : Expr := if l = 0 then k 0 else c (colC q 0)

def sC (i l : Nat) : Expr := c (colS i l)
def sN (i l : Nat) : Expr := n (colS i l)

/-- The ChaCha constant `consts[i]`, limb `l`. -/
def constLimb (i l : Nat) : Nat := (consts.getD i 0 / 2 ^ (16 * l)) % 65536

/-- Limb `l` of the input word of slot `i` (constants, key, counter, zero) on the
current row. -/
def initLimb (i l : Nat) : Expr :=
  if i < 4 then k (constLimb i l)
  else if i < 12 then c (colK (i - 4) l)
  else if i = 12 then c (colK 8 l)
  else k 0

/-! ## Quarter-round constraints (inner, for slots `grp p`) -/

/-- Inner quarter-round constraint `q < 12` for slots `(a,b,c,d)`. -/
def qrC (g : Nat × Nat × Nat × Nat) (q : Nat) : Expr :=
  let a := g.1; let bb := g.2.1; let cc := g.2.2.1; let dd := g.2.2.2
  let l := q % 2
  match q / 2 with
  | 0 => sub (limb (xb 0) l) (sC bb l)
  | 1 => sub (limb (xb 1) l) (sC dd l)
  | 2 => addE [sC a l, limb (xb 0) l] (cin 0 l) (limb (xb 2) l) (c (colC 0 l))
  | 3 => addE [sC cc l, limb d1 l] (cin 1 l) (limb (xb 3) l) (c (colC 1 l))
  | 4 => addE [limb (xb 2) l, limb b1 l] (cin 2 l) (limb (xb 4) l) (c (colC 2 l))
  | _ => addE [limb (xb 3) l, limb d2 l] (cin 3 l) (limb (xb 5) l) (c (colC 3 l))

/-- New limb `l` of slot `i` after the quarter-round on slots `g`. -/
def newS (g : Nat × Nat × Nat × Nat) (i l : Nat) : Expr :=
  if i = g.1 then limb (xb 4) l
  else if i = g.2.1 then limb b2 l
  else if i = g.2.2.1 then limb (xb 5) l
  else if i = g.2.2.2 then limb d2 l
  else sC i l

/-! ## Feed-forward constraints (inner, for output group `j`) -/

/-- Inner feed-forward constraint `q < 8` (word `4·(q/2) + j`, limb `q % 2`). -/
def ffC (j q : Nat) : Expr :=
  let kk := q / 2; let l := q % 2
  addE [sC (4 * kk + j) l, initLimb (4 * kk + j) l] (cin kk l) (limb (xb kk) l) (c (colC kk l))

/-! ## Constraint families -/

def boolC (x : Nat) : Expr := .mul (c x) (sub (c x) (k 1))
def cBool : List Expr := boolCols.map boolC

def flagSum : Expr := sum (flagCols.map c)
def sumP : Expr := sum ((List.range 8).map fun p => c (colP p))
def sumF : Expr := sum ((List.range 4).map fun j => c (colF j))
/-- `dr = 9` (given `dr ≤ 9`). -/
def lastDr : Expr := .mul (c (colDr 0)) (c (colDr 3))
def drC : Expr := sum ((List.range 4).map fun b => smul (2 ^ b) (c (colDr b)))
def drN : Expr := sum ((List.range 4).map fun b => smul (2 ^ b) (n (colDr b)))

def cKind : List Expr :=
  [.mul flagSum (sub flagSum (k 1)),
   sub (n colI1) (c colI0),
   sub (n (colP 0)) (sub (.add (c colI1) (c (colP 7))) (.mul (c (colP 7)) lastDr)),
   sub (n (colF 0)) (.mul (c (colP 7)) lastDr)] ++
  (List.range 7).map (fun p => sub (n (colP (p + 1))) (c (colP p))) ++
  (List.range 3).map (fun j => sub (n (colF (j + 1))) (c (colF j))) ++
  [.mul .isFirst (.add (c colI1) (.add sumP sumF)),
   .mul (c (colDr 3)) (c (colDr 1)),
   .mul (c (colDr 3)) (c (colDr 2)),
   .mul (n (colP 0)) (sub drN (.mul (c (colP 7)) (.add drC (k 1))))] ++
  (List.range 7).map (fun p => .mul (n (colP (p + 1))) (sub drN drC))

/-- Input rows: `I0` fixes the input state (except slot 12) and range-checks key words
`0..5`; `I1` range-checks key words `6, 7` and the counter (`< 2^30`), and puts the
counter into slot 12. -/
def cInit : List Expr :=
  ((List.range 16).filter (· ≠ 12)).flatMap (fun i => (List.range 2).map fun l =>
    .mul (c colI0) (sub (sC i l) (initLimb i l))) ++
  (List.range 6).flatMap (fun m => (List.range 2).map fun l =>
    .mul (c colI0) (sub (limb (xb m) l) (c (colK m l)))) ++
  (List.range 3).flatMap (fun m => (List.range 2).map fun l =>
    .mul (c colI1) (sub (limb (xb m) l) (c (colK (6 + m) l)))) ++
  [.mul (c colI1) (c (colX 2 30)), .mul (c colI1) (c (colX 2 31))] ++
  (List.range 2).map (fun l => .mul (c colI1) (sub (sC 12 l) (c (colK 8 l))))

/-- Rows that copy the state to the next row. -/
def gCopy : Expr := sum [c colI0, c colI1, c (colF 0), c (colF 1), c (colF 2)]

def cCopy : List Expr :=
  (List.range 16).flatMap (fun i => (List.range 2).map fun l =>
    .add (.mul gCopy (sub (sN i l) (sC i l)))
      (sel colP 8 fun p => sub (sN i l) (newS (grp p) i l))) ++
  (List.range 9).flatMap (fun j => (List.range 2).map fun l =>
    .mul (.add gCopy sumP) (sub (n (colK j l)) (c (colK j l))))

def cQR : List Expr := (List.range 12).map fun q => sel colP 8 fun p => qrC (grp p) q

def cFF : List Expr :=
  (List.range 8).map (fun q => sel colF 4 fun j => ffC j q) ++
  (List.range 4).map (fun kk => .mul (c (colM kk)) (sub (k 1) sumF))

def constraints : List Expr := cBool ++ cKind ++ cInit ++ cCopy ++ cQR ++ cFF

/-! ## Interactions -/

/-- Word index of output `kk` of the current `F` row. -/
def idxE (kk : Nat) : Expr := sel colF 4 fun j => k (4 * kk + j)

def ctrE : Expr := .add (c (colK 8 0)) (smul 65536 (c (colK 8 1)))

/-- Message of output `kk` of an `F` row. -/
def outMsg (kk : Nat) : List Expr :=
  (List.range 16).map (fun q => c (colK (q / 2) (q % 2))) ++
    [ctrE, idxE kk, limb (xb kk) 0, limb (xb kk) 1]

def interactions (busChacha : Nat) : List Interaction :=
  (List.range 4).map fun kk =>
    { bus := busChacha, mult := [c (colM kk)], msg := outMsg kk, send := true }

def maxLog : Nat := 21

def table (busChacha : Nat) : Table :=
  { width := width, constraints := constraints, interactions := interactions busChacha,
    maxLog := maxLog }

end ZkFormal.Chacha.Table
