import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.Rcpt.Ids

/-!
# ZkFormal.NearV3.Rcpt.Tables.Size — `sizeV3`: the size bounds of the constructed witness

`checkD0` requires `|witness| ≤ 8 MiB` and `|base_state| ≤ 3,000,000` (`w.size`).  The extracted
witness is constructed from the AIR's records; its size is a sum of per-table byte totals
sent on `SIZE (t, x)`:

| `t` | sender | total |
|---|---|---|
| 0 | `nodeV3` (`SUM` row) | bytes of the non-duplicate node records |
| 1 | `valV3` (`SUM` row) | bytes of the non-duplicate value records |
| 2 | `srcpV3` (last active row) | `Σ_j |RC(j)|` (the receipt lists) `+ 33 ·` number of path items |

Rows `t = 0 … NT−1` (active block from row 0) receive `SIZE (t, x_t)`; `tot` and `base` are
running sums.  Row `t = 1` checks `3,000,000 − (x_0 + x_1) ≥ 0` and row `t = NT−1` checks
`8,388,608 − OVH − Σ x_t ≥ 0`, both as 24 bits (the same bit columns); `OVH` (`u32`, public,
**requested** at `PH_WOVH`) is the natively computed rest of the witness encoding.
-/

namespace ZkFormal.NearV3.SizeV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

/-- Number of `SIZE` tags. -/
def NT : Nat := 3
/-- `u32` witness overhead (public, **requested**: after `PH_BLEN`). -/
def PH_WOVH : Nat := 198

def act : Nat := 0
def t : Nat := 1
def x : Nat := 2
def tot : Nat := 3
def base : Nat := 4
def lb : Nat := 5
def la : Nat := 6
def bt (e : Nat) : Nat := 7 + e
def width : Nat := 31

def bitsE : Expr := bits (fun e => c (bt e)) 0 24
def ovhE : Expr := sum ((List.range 4).map fun e => smul (256 ^ e) (.pub (PH_WOVH + e)))

def constraints : List Expr :=
  ([act, lb, la] ++ (List.range 24).map bt).map (fun y => bool (c y)) ++
  [ -- the active block: rows t = 0 … NT−1
    .mul .isFirst (not (c act)), .mul .isFirst (c t),
    .mul .isFirst (sub (c tot) (c x)), .mul .isFirst (sub (c base) (c x)),
    .mul .isFirst (not (n lb)),
    .mul (c lb) (sub (c t) (k 1)), .mul (c la) (sub (c t) (k (NT - 1))),
    .mul (c lb) (not (c act)), .mul (c la) (not (c act)),
    .mul (mul3 .isTransition (c act) (not (c la))) (not (n act)),
    mul3 .isTransition (c la) (n act),
    mul3 .isTransition (not (c act)) (n act),
    .mul .isLast (.mul (c act) (not (c la))),
    mul3 .isTransition (c act) (sub (n t) (.add (c t) (k 1))),
    mul3 .isTransition (n act) (sub (n tot) (.add (c tot) (n x))),
    mul3 .isTransition (n act) (sub (n base) (.add (c base) (.mul (n lb) (n x)))),
    -- the bounds
    .mul (c lb) (sub bitsE (sub (k 3000000) (c base))),
    .mul (c la) (sub bitsE (sub (sub (k 8388608) ovhE) (c tot))) ]

def interactions : List Interaction :=
  [ recv B_SIZE (c act) [c t, c x] ]

def maxLog : Nat := 2

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.SizeV3
