import ZkFormal.Air.Basic
import ZkFormal.Sha.Layout

/-!
# ZkFormal.Sha.Table — the SHA-256 block table as an `Air.Table`

Constraint families (all of degree ≤ 4; `c x` is column `x` on the current
row, `n x` on the next row):

* `cBool`      — every bit/flag column is boolean;
* `cKind`      — one-hot row kind and its transitions
  (`Rj → Rj+1`, `R15 → D`, `S | D(¬last) → R0`), row 0 is `S` or padding;
* `cIV`        — an `S` row holds the SHA-256 IV;
* `cRound`     — 4 rounds per round row: `a`/`e` limb additions with carries;
* `cSched`     — message schedule for `R4..R15` (limb additions with carries);
* `cHelp`      — schedule helpers `I4/I8/I12/W3` and the chaining value `Hin`;
* `cDigest`    — `D` holds `Hin + final working variables` (mod 2^32);
* `cFrame`     — data flags, counters, block flags (`Last/P80/Seen`), padding
  bytes, length word, digest multiplicity.

Interactions: each round row `R0..R3` receives its data bytes
`(Id, pos, byte)` on `busBytes` (multiplicity `F k`); a `D` row of a last
block provides `(Id, len, digest[0..32))` on `busDigest` with multiplicity
`Dmult` (a single multiplicity bit: each message's digest is provided at
most once; a consumer needing it twice hashes twice).
-/

namespace ZkFormal.Sha.Table

open ZkFormal.Air ZkFormal.Sha.Layout

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
def not (x : Expr) : Expr := sub (k 1) x
def xor2 (x y : Expr) : Expr := sub (.add x y) (smul 2 (.mul x y))
def xor3 (x y z : Expr) : Expr := xor2 (xor2 x y) z
def ch (x y z : Expr) : Expr := .add (.mul x y) (.mul (not x) z)
def maj (x y z : Expr) : Expr :=
  sub (.add (.add (.mul x y) (.mul x z)) (.mul y z)) (smul 2 (.mul (.mul x y) z))
/-- `Σ_{b<len} 2^b · x (off + b)`. -/
def bits (x : Nat → Expr) (off len : Nat) : Expr :=
  sum ((List.range len).map fun b => smul (2 ^ b) (x (off + b)))
/-- 16-bit limb `l` of a bit-decomposed word. -/
def limb (x : Nat → Expr) (l : Nat) : Expr := bits x (16 * l) 16
/-- Bit `b` of `rotr r1 ⊕ rotr r2 ⊕ (rotr r3 | shr r3)`. -/
def sig (x : Nat → Expr) (r1 r2 r3 : Nat) (shr : Bool) (b : Nat) : Expr :=
  xor3 (x ((b + r1) % 32)) (x ((b + r2) % 32))
    (if shr then (if b + r3 < 32 then x (b + r3) else k 0) else x ((b + r3) % 32))
/-- `gate · (Σ terms + cin − (res + 2^16·cout))`. -/
def addC (gate : Expr) (terms : List Expr) (cin res cout : Expr) : Expr :=
  .mul gate (sub (.add (sum terms) cin) (.add res (smul 65536 cout)))
/-- `gate · (x − y)`. -/
def eqG (gate x y : Expr) : Expr := .mul gate (sub x y)
end E

open E

/-- Bit columns of `A`/`E` window slot `u < 8` (slots `0..3` current row,
`4..7` next row). -/
def winA (u b : Nat) : Expr := if u < 4 then c (colA u b) else n (colA (u - 4) b)
def winE (u b : Nat) : Expr := if u < 4 then c (colE u b) else n (colE (u - 4) b)

/-- Carry value `Σ_{k<3} 2^k·bit` of carry columns `cc l k` on the next row. -/
def carryN (cc : Nat → Nat → Nat) (l : Nat) : Expr := bits (fun k => n (cc l k)) 0 3

/-- `Σ_{j ∈ js} next.R j`. -/
def kindN (js : List Nat) : Expr := sum (js.map fun j => n (colR j))
def kindC (js : List Nat) : Expr := sum (js.map fun j => c (colR j))

def gRound : Expr := kindN (List.range 16)
def gSched : Expr := kindN (List.range' 4 12)
def gHelp : Expr := kindN (List.range' 1 15)
def gMsgC : Expr := kindC (List.range 4)

/-- Round constant limb for slot `i` of the next row (`Σ_j next.Rj · K_{4j+i}`). -/
def kLimb (i l : Nat) : Expr :=
  sum ((List.range 16).map fun j =>
    .mul (n (colR j)) (k ((ArenaCore.SHA256.K.getD (4 * j + i) 0 / 2 ^ (16 * l)) % 2 ^ 16)))

/-! ## Constraint families -/

def boolC (x : Nat) : Expr := .mul (c x) (sub (c x) (k 1))

def cBool : List Expr := boolCols.map boolC

def flagSum : Expr := sum (((List.range 16).map colR ++ [colD, colS]).map c)

def cKind : List Expr :=
  [.mul flagSum (sub flagSum (k 1))] ++
  (List.range 15).map (fun j => sub (n (colR (j + 1))) (c (colR j))) ++
  [sub (n colD) (c (colR 15)),
   sub (n (colR 0)) (sub (.add (c colS) (c colD)) (.mul (c colD) (c colLast))),
   .mul .isFirst (.add (kindC (List.range 16)) (c colD))]

/-- SHA-256 IV word `w` (`H0[w]`). -/
def iv (w : Nat) : Nat := ArenaCore.SHA256.H0.getD w 0

def cIV : List Expr :=
  (List.range 8).flatMap fun w => (List.range 32).map fun b =>
    eqG (c colS) (c (colSt w b)) (k ((iv w / 2 ^ b) % 2))

def roundA (i l : Nat) : Expr :=
  addC gRound
    [limb (winE i) l, limb (sig (winE (i + 3)) 6 11 25 false) l,
     limb (fun b => ch (winE (i + 3) b) (winE (i + 2) b) (winE (i + 1) b)) l,
     kLimb i l, limb (fun b => n (colW i b)) l,
     limb (sig (winA (i + 3)) 2 13 22 false) l,
     limb (fun b => maj (winA (i + 3) b) (winA (i + 2) b) (winA (i + 1) b)) l]
    (if l = 0 then k 0 else carryN (colCA i) 0)
    (limb (fun b => n (colA i b)) l) (carryN (colCA i) l)

def roundE (i l : Nat) : Expr :=
  addC gRound
    [limb (winA i) l, limb (winE i) l, limb (sig (winE (i + 3)) 6 11 25 false) l,
     limb (fun b => ch (winE (i + 3) b) (winE (i + 2) b) (winE (i + 1) b)) l,
     kLimb i l, limb (fun b => n (colW i b)) l]
    (if l = 0 then k 0 else carryN (colCE i) 0)
    (limb (fun b => n (colE i b)) l) (carryN (colCE i) l)

def cRound : List Expr :=
  (List.range 4).flatMap fun i => (List.range 2).flatMap fun l => [roundA i l, roundE i l]

/-- `W_{t-2}` bits for next-row slot `i`. -/
def w2 (i b : Nat) : Expr := if i < 2 then c (colW (i + 2) b) else n (colW (i - 2) b)
/-- `W_{t-7}` limb for next-row slot `i`. -/
def w7 (i l : Nat) : Expr := if i < 3 then c (colW3 i l) else limb (fun b => c (colW 0 b)) l
/-- `W_{t-15}` bits relative to the helper computed on the next row, slot `i`. -/
def w15 (i b : Nat) : Expr := if i < 3 then c (colW (i + 1) b) else n (colW 0 b)

def sched (i l : Nat) : Expr :=
  addC gSched [limb (sig (w2 i) 17 19 10 true) l, w7 i l, c (colI12 i l)]
    (if l = 0 then k 0 else carryN (colCW i) 0)
    (limb (fun b => n (colW i b)) l) (carryN (colCW i) l)

def cSched : List Expr :=
  (List.range 4).flatMap fun i => (List.range 2).map fun l => sched i l

def cHelp : List Expr :=
  ((List.range 4).flatMap fun i => (List.range 2).flatMap fun l =>
    [eqG gHelp (n (colI4 i l))
       (.add (limb (sig (w15 i) 7 18 3 true) l) (limb (fun b => c (colW i b)) l)),
     eqG gHelp (n (colI8 i l)) (c (colI4 i l)),
     eqG gHelp (n (colI12 i l)) (c (colI8 i l))]) ++
  ((List.range 3).flatMap fun i => (List.range 2).map fun l =>
    eqG gHelp (n (colW3 i l)) (limb (fun b => c (colW (i + 1) b)) l)) ++
  ((List.range 8).flatMap fun w => (List.range 2).flatMap fun l =>
    [eqG gHelp (n (colHin w l)) (c (colHin w l)),
     eqG (n (colR 0)) (n (colHin w l)) (limb (fun b => c (colSt w b)) l)])

def cDigest : List Expr :=
  (List.range 8).flatMap fun w => (List.range 2).map fun l =>
    addC (n colD) [c (colHin w l), limb (fun b => c (colSt w b)) l]
      (if l = 0 then k 0 else carryN (colCSt w) 0)
      (limb (fun b => n (colSt w b)) l) (carryN (colCSt w) l)

/-- Byte `q < 16` of a round row (big-endian bytes of words `W 0..3`). -/
def byteE (q : Nat) : Expr := bits (fun b => c (colW (q / 4) b)) (8 * (3 - q % 4)) 8

/-- `F (q-1) − F q` (with `F (-1) := Fprev`): byte `q` is the first non-data byte. -/
def dropE (q : Nat) : Expr := sub (if q = 0 then c colFprev else c (colF (q - 1))) (c (colF q))

/-- Sum of the data flags of the current/next row. -/
def fSumC : Expr := sum ((List.range 16).map fun q => c (colF q))
def fSumN : Expr := sum ((List.range 16).map fun q => n (colF q))

def gBlockN : Expr := .add gRound (n colD)
def gInnerN : Expr := .add gHelp (n colD)

def cFrame : List Expr :=
  -- data flags: monotone, only on R0..R3, chained across rows by Fprev
  ((List.range 15).map fun q => .mul (c (colF (q + 1))) (not (c (colF q)))) ++
  [.mul (c (colF 0)) (not (c colFprev)),
   .mul (not gMsgC) (c (colF 0)),
   .mul (c (colR 0)) (not (c colFprev))] ++
  ((List.range' 1 3).map fun j => eqG (n (colR j)) (n colFprev) (c (colF 15))) ++
  -- counters and block/message constants
  [eqG gBlockN (n colNd) (.add (.mul (not (c colS)) (c colNd)) fSumN),
   eqG gBlockN (n colId) (c colId),
   eqG gInnerN (n colSeen) (c colSeen),
   eqG gInnerN (n colP80) (c colP80),
   eqG gInnerN (n colLast) (c colLast),
   eqG (n (colR 0)) (n colSeen) (.mul (c colD) (.add (c colSeen) (c colP80))),
   sub (c colPn) (.mul (c colP80) (not (c colLast))),
   .mul (c colSeen) (c colP80)] ++
  -- block-level padding structure
  [.mul (.mul (c (colR 3)) (c colP80)) (c (colF 15)),
   .mul (.mul (c (colR 3)) (sub (not (c colSeen)) (c colP80))) (not (c (colF 15))),
   .mul (.mul (c (colR 0)) (c colSeen)) (c (colF 0)),
   .mul (.mul (c (colR 0)) (c colLast)) (sub (not (c colSeen)) (c colP80)),
   .mul (.mul (c (colR 0)) (c colSeen)) (not (c colLast)),
   .mul (.mul (c (colR 3)) (c colLast)) (c (colF 8)),
   .mul (.mul (.mul (c (colR 3)) (c colLast)) (c colP80)) (dropE 8),
   .mul (.mul (c (colR 3)) (c colPn)) (not (c (colF 7)))] ++
  -- padding bytes: 0x80 at the drop, zero elsewhere (length bytes of the last block excepted)
  ((List.range 4).flatMap fun j => (List.range 16).map fun q =>
    if 16 * j + q < 56 then
      .mul (.mul (c (colR j)) (not (c (colF q))))
        (sub (byteE q) (smul 128 (.mul (c colP80) (dropE q))))
    else
      .mul (.mul (c (colR j)) (not (c (colF q))))
        (sub (.mul (not (c colLast)) (byteE q)) (smul 128 (.mul (c colPn) (dropE q))))) ++
  -- length: last block words 14, 15 = 0, 8·len (len < 2^25)
  ((List.range 32).map fun b => .mul (.mul (c (colR 3)) (c colLast)) (c (colW 2 b))) ++
  ((List.range' 28 4).map fun b => .mul (.mul (c (colR 3)) (c colLast)) (c (colW 3 b))) ++
  [.mul (.mul (c (colR 3)) (c colLast)) (sub (bits (fun b => c (colW 3 b)) 0 28) (smul 8 (c colNd))),
  -- digest multiplicity only on the digest row of a last block
   .mul (c colDmult) (not (c colD)),
   .mul (c colDmult) (not (c colLast))]

def constraints : List Expr :=
  cBool ++ cKind ++ cIV ++ cRound ++ cSched ++ cHelp ++ cDigest ++ cFrame

/-! ## Interactions -/

/-- Message position of byte `q` of the current row: `Nd − Σ F + q`. -/
def posE (q : Nat) : Expr := .add (sub (c colNd) fSumC) (k q)

/-- Digest byte `p < 32` of the current (digest) row. -/
def digestByteE (p : Nat) : Expr := bits (fun b => c (colSt (p / 4) b)) (8 * (3 - p % 4)) 8

def interactions (busBytes busDigest : Nat) : List Interaction :=
  ((List.range 16).map fun q =>
    { bus := busBytes, mult := [c (colF q)], msg := [c colId, posE q, byteE q], send := false }) ++
  [{ bus := busDigest, mult := [c colDmult],
     msg := [c colId, c colNd] ++ (List.range 32).map digestByteE, send := true }]

/-- Largest supported height: `2^22` rows (DESIGN.md R7). -/
def maxLog : Nat := 22

def table (busBytes busDigest : Nat) : Table :=
  { width := width, constraints := constraints,
    interactions := interactions busBytes busDigest, maxLog := maxLog }

end ZkFormal.Sha.Table
