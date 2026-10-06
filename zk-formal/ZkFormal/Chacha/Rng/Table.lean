import ZkFormal.Chacha.Table

/-!
# ZkFormal.Chacha.Rng.Table — the stream / `gen_index` table `genV3` (np-udr-stark-v2)

One row per drawn word.  A `gen_index(n)` call (`NearSpecV3.genIndex 64 n`) occupies
consecutive rows: draws at stream positions `kstart, kstart+1, …`, all rejected except the
last (`acc = 1`), at most 64 draws (`att < 64`).

* Each active row *receives* word `k = 16·ctr + idx` of the stream with key `K` on
  `busChacha` (`[K limbs, ctr, idx, vlo, vhi]`, see `Chacha.Table`); the ChaCha table
  guarantees `v = vlo + 2^16·vhi = streamWord key k` (`rng_contract`).
* Lemire: `n < 2^14` as bits `N`, its leading bit one-hot `H` (`2^i ≤ n < 2^(i+1)`),
  `Z = n·2^(15-i) ∈ [2^15, 2^16)` (so `zone = 2^16·Z − 1`);
  `vlo·n = m0 + 2^16·c0`, `vhi·n + c0 = m1 + 2^16·m2` (all limbs range-checked by bits), so
  `v·n = m0 + 2^16·m1 + 2^32·m2`; accept iff `m1 < Z` (witnessed by `δ`), result `m2`.
* The accepting row *provides* `[K limbs, kstart, n, j, kend]` on `busGen`
  (`genIndex_contract`: `genIndex 64 n (rngAt key kstart) = some (j, rngAt key kend)`).

| columns | name |
|---|---|
| `[0,16)` | `K j l` key limbs |
| `16` | `ctr` (block counter of the drawn word) |
| `[17,21)` | `Idx b` (word index bits) |
| `21, 22` | `vlo, vhi` |
| `[23,37)` | `N b` (bits of `n`) |
| `[37,51)` | `H i` (leading bit of `n`) |
| `[51,67)`, `[67,81)`, `[81,97)`, `[97,111)` | bits of `m0`, `c0`, `m1`, `m2` |
| `[111,127)` | bits of `δ` |
| `127, 128, 129` | `acc, st, a` (accept, call start, active) |
| `[130,136)` | `Att b` (attempt number bits) |
| `136` | `ks` (`kstart`) |
-/

namespace ZkFormal.Chacha.Rng.Table

open ZkFormal.Air ZkFormal.Chacha.Table.E

def colK (j l : Nat) : Nat := 2 * j + l
def colCtr : Nat := 16
def colIdx (b : Nat) : Nat := 17 + b
def colVlo : Nat := 21
def colVhi : Nat := 22
def colN (b : Nat) : Nat := 23 + b
def colH (i : Nat) : Nat := 37 + i
def colM0 (b : Nat) : Nat := 51 + b
def colC0 (b : Nat) : Nat := 67 + b
def colM1 (b : Nat) : Nat := 81 + b
def colM2 (b : Nat) : Nat := 97 + b
def colDl (b : Nat) : Nat := 111 + b
def colAcc : Nat := 127
def colSt : Nat := 128
def colA : Nat := 129
def colAtt (b : Nat) : Nat := 130 + b
def colKs : Nat := 136
def width : Nat := 137

def boolCols : List Nat := List.range' 17 4 ++ List.range' 23 113

/-- `Σ_{b<len} 2^b · col b` on the current (`nx = false`) or next row. -/
def num (col : Nat → Nat) (len : Nat) (nx : Bool := false) : Expr :=
  sum ((List.range len).map fun b => smul (2 ^ b) (.col (col b) nx))

def idxE : Expr := num colIdx 4
def nE : Expr := num colN 14
def m0E : Expr := num colM0 16
def c0E : Expr := num colC0 14
def m1E : Expr := num colM1 16
def m2E : Expr := num colM2 14
def dlE : Expr := num colDl 16
def attE : Expr := num colAtt 6
def kE : Expr := .add (smul 16 (c colCtr)) idxE
def kN : Expr := .add (smul 16 (n colCtr)) (num colIdx 4 true)
/-- `Z = n·2^(15-i)` for the leading bit `i`. -/
def zE : Expr := sel colH 14 fun i => smul (2 ^ (15 - i)) nE
/-- Continue the call to the next row. -/
def gCont : Expr := .mul (c colA) (sub (k 1) (c colAcc))

def cB : List Expr := boolCols.map ZkFormal.Chacha.Table.boolC

/-- Leading bit of `n`. -/
def cH : List Expr :=
  [sub (sum ((List.range 14).map fun i => c (colH i))) (c colA)] ++
  (List.range 14).map (fun i => .mul (c (colH i)) (sub (k 1) (c (colN i)))) ++
  (List.range 14).map (fun i =>
    .mul (c (colH i)) (sum ((List.range' (i + 1) (13 - i)).map fun i' => c (colN i'))))

/-- Lemire product, acceptance, flags and call structure. -/
def cM : List Expr :=
  [sub (.mul (c colVlo) nE) (.add m0E (smul 65536 c0E)),
   sub (.add (.mul (c colVhi) nE) c0E) (.add m1E (smul 65536 m2E)),
   sub (sub dlE (.mul (c colAcc) (sub (sub zE (k 1)) m1E)))
     (.mul (sub (k 1) (c colAcc)) (sub m1E zE)),
   .mul (c colAcc) (sub (k 1) (c colA)),
   .mul (c colSt) (sub (k 1) (c colA)),
   .mul (c colSt) attE,
   .mul (c colSt) (sub (c colKs) kE),
   .mul .isFirst (sub (c colA) (c colSt)),
   sub (sub (n colA) (n colSt)) gCont,
   .mul gCont (sub (num colN 14 true) nE),
   .mul gCont (sub (n colKs) (c colKs)),
   .mul gCont (sub kN (.add kE (k 1))),
   .mul gCont (sub (num colAtt 6 true) (.add attE (k 1)))]

/-- The key is constant within a call. -/
def cK : List Expr :=
  (List.range 8).flatMap (fun j => (List.range 2).map fun l =>
    .mul gCont (sub (n (colK j l)) (c (colK j l))))

def constraints : List Expr := cB ++ cH ++ cM ++ cK

def keyMsg : List Expr := (List.range 16).map fun q => c (colK (q / 2) (q % 2))

def interactions (busChacha busGen : Nat) : List Interaction :=
  [{ bus := busChacha, mult := [c colA], send := false,
     msg := keyMsg ++ [c colCtr, idxE, c colVlo, c colVhi] },
   { bus := busGen, mult := [c colAcc], send := true,
     msg := keyMsg ++ [c colKs, nE, m2E, .add kE (k 1)] }]

def maxLog : Nat := 20

def table (busChacha busGen : Nat) : Table :=
  { width := width, constraints := constraints, interactions := interactions busChacha busGen,
    maxLog := maxLog }

end ZkFormal.Chacha.Rng.Table
