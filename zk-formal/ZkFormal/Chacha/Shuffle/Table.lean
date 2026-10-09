import ZkFormal.Chacha.Rng.Table

/-!
# ZkFormal.Chacha.Shuffle.Table — Fisher–Yates `shuffle` as a swap trace (`shufV3`)

`NearSpecV3.shuffle l r` = `for q in (1..L).rev() { swap(q, gen_index(q+1)) }`.
An instance (list of length `1 ≤ L ≤ 2^14`) occupies `L` consecutive rows, `q = L−1, …, 0`:
row `q ≥ 1` is step `q`, row `q = 0` is the final row (`fin`).

**Representation of the permutation: offline memory checking on a swap trace.**
The list lives in a memory indexed by `(inst, position)`; `inst` is the row index of the
instance's first row (so instances never share addresses).  Time stamps decrease with time:
the input is written with stamp `L`, step `q` writes with stamp `q`.
* every row `q` writes the input `l[q]` (`MINIT`, stamp `L`), reads position `q`
  (`MR1`: the value `c` with an older stamp `t1 > q`) and sends the output `(lid, q, out)`;
* step `q` receives `j = gen_index(q+1)` from `busGen` (RNG positions `kq → kn`); if `j < q`
  (`eqj = 0`) it reads position `j` (`MR2`: value `o`, stamp `t2 > q`) and writes `c` there
  (`MW2`, stamp `q`); the output of position `q` is `o` (or `c` if `j = q`);
* the final row (`q = 0`) outputs `c` (position 0's final value) and provides
  `(lid, key, kstart, L, kend)` on `busShuf`.
Positions `> q` are final after step `q`, so outputs are emitted right away.  `shuffle_contract`
shows the outputs are `NearSpecV3.shuffle`'s result (`ShuffleSpec.fyBefore_get`,
`ShuffleSpec.mem_latest`).

| col | name | col | name |
|---|---|---|---|
| 0 | `lid` | 1 | `rc` (row counter) |
| 2 | `inst` | 3 | `L` |
| 4 | `q` | 5 | `j` |
| `[6,22)` | key limbs | 22, 23, 24 | `kq, kn, ks` |
| 25 | `v0` (input `l[q]`) | 26, 27 | `c, o` |
| 28, 29 | `t1, t2` | `[30,44)`, `[44,58)`, `[58,72)` | bits of `t1−q−1`, `t2−q−1`, `q−j−1` |
| 72–76 | `a, st, fin, eqj, s2` | | |
-/

namespace ZkFormal.Chacha.Shuffle.Table

open ZkFormal.Air ZkFormal.Chacha.Table.E
open ZkFormal.Chacha.Rng.Table (num)

def colLid : Nat := 0
def colRc : Nat := 1
def colInst : Nat := 2
def colL : Nat := 3
def colQ : Nat := 4
def colJ : Nat := 5
def colK (j l : Nat) : Nat := 6 + 2 * j + l
def colKq : Nat := 22
def colKn : Nat := 23
def colKs : Nat := 24
def colV0 : Nat := 25
def colC : Nat := 26
def colO : Nat := 27
def colT1 : Nat := 28
def colT2 : Nat := 29
def colD1 (b : Nat) : Nat := 30 + b
def colD2 (b : Nat) : Nat := 44 + b
def colDj (b : Nat) : Nat := 58 + b
def colA : Nat := 72
def colSt : Nat := 73
def colFin : Nat := 74
def colEq : Nat := 75
def colS2 : Nat := 76
def width : Nat := 77

def boolCols : List Nat := List.range' 30 47

def d1E : Expr := num colD1 14
def d2E : Expr := num colD2 14
def djE : Expr := num colDj 14
/-- Steps (active, not final). -/
def gStep : Expr := sub (c colA) (c colFin)
def outE : Expr := .add (.mul (c colEq) (c colC)) (.mul (sub (k 1) (c colEq)) (c colO))

def cB : List Expr := boolCols.map ZkFormal.Chacha.Table.boolC

def cM : List Expr :=
  [.mul (c colFin) (sub (k 1) (c colA)),
   .mul (c colSt) (sub (k 1) (c colA)),
   sub (c colS2) (.mul (.mul (c colA) (sub (k 1) (c colFin))) (sub (k 1) (c colEq))),
   .mul (c colFin) (c colQ),
   .mul (c colFin) (sub (k 1) (c colEq)),
   .mul (c colEq) (sub (c colJ) (c colQ)),
   .mul (.mul (c colA) (sub (k 1) (c colEq))) (sub (sub (sub (c colQ) (c colJ)) (k 1)) djE),
   .mul (c colA) (sub (sub (sub (c colT1) (c colQ)) (k 1)) d1E),
   .mul (c colS2) (sub (sub (sub (c colT2) (c colQ)) (k 1)) d2E),
   .mul (c colSt) (sub (.add (c colQ) (k 1)) (c colL)),
   .mul (c colSt) (sub (c colKq) (c colKs)),
   .mul (c colSt) (sub (c colInst) (c colRc)),
   .mul .isFirst (c colRc),
   .mul .isTransition (sub (sub (n colRc) (c colRc)) (k 1)),
   .mul .isFirst (sub (c colA) (c colSt)),
   sub (sub (n colA) (n colSt)) gStep,
   .mul gStep (sub (.add (n colQ) (k 1)) (c colQ)),
   .mul gStep (sub (n colL) (c colL)),
   .mul gStep (sub (n colLid) (c colLid)),
   .mul gStep (sub (n colInst) (c colInst)),
   .mul gStep (sub (n colKs) (c colKs)),
   .mul gStep (sub (n colKq) (c colKn))]

def cK : List Expr :=
  (List.range 8).flatMap (fun j => (List.range 2).map fun l =>
    .mul gStep (sub (n (colK j l)) (c (colK j l))))

def constraints : List Expr := cB ++ cM ++ cK

def keyMsg : List Expr := (List.range 16).map fun q => c (colK (q / 2) (q % 2))

/-- Interactions: input, memory (init write, two reads, one write), output, `gen_index`,
the instance header. -/
def interactions (busIn busOut busMem busGen busShuf : Nat) : List Interaction :=
  [{ bus := busIn, mult := [c colA], send := false, msg := [c colLid, c colQ, c colV0] },
   { bus := busMem, mult := [c colA], send := true, msg := [c colInst, c colQ, c colL, c colV0] },
   { bus := busMem, mult := [c colA], send := false, msg := [c colInst, c colQ, c colT1, c colC] },
   { bus := busMem, mult := [c colS2], send := false, msg := [c colInst, c colJ, c colT2, c colO] },
   { bus := busMem, mult := [c colS2], send := true, msg := [c colInst, c colJ, c colQ, c colC] },
   { bus := busOut, mult := [c colA], send := true, msg := [c colLid, c colQ, outE] },
   { bus := busGen, mult := [gStep], send := false,
     msg := keyMsg ++ [c colKq, .add (c colQ) (k 1), c colJ, c colKn] },
   { bus := busShuf, mult := [c colFin], send := true,
     msg := [c colLid] ++ keyMsg ++ [c colKs, c colL, c colKq] }]

def maxLog : Nat := 20

def table (busIn busOut busMem busGen busShuf : Nat) : Table :=
  { width := width, constraints := constraints,
    interactions := interactions busIn busOut busMem busGen busShuf, maxLog := maxLog }

end ZkFormal.Chacha.Shuffle.Table
