import ZkFormal.NearV3.Rcpt.Tables.Rcpt.Layout

/-!
# ZkFormal.NearV3.Rcpt.Tables.Rcpt.Fields — row structure of `rcptV3`

Rows: per applied source list `j` (consecutive from `0`, in applied order) 12 list-header rows
(`sCL`), then the list's receipts, one segment each; then padding.  A receipt segment runs
through v1's fields

```
PL P VL V RID T0 SL S KT PK GP TL DEP XP0 [XRI] XG XST XL0 XLH [XRH XRF XRZ]
```

(`[…]` only with a refund, `hr = 1`).  Deltas to v1 (`Near/Tables/Rcpt/Fields.lean`):

* the header block repeats per list; after a header's last row or a receipt's last row comes
  a receipt (`rf`) or the next header (`le` marks the last row of a list, `lastR` the last
  active row);
* list constants `j`, `nj`; `cj` counts the list's receipts and ends at `nj`;
* `r` is global (consecutive over all lists), `o` restarts at `12` per list (`RC(j)` offsets),
  `o2` (body positions) is global and starts at `8` (after `u32 0 ‖ u32 nref`);
* emissions: `RC` is `RC(j) = K_RC + 16·j`; the refund bytes keep v1's `RF` emissions
  (`K_RF`, positions `o2 + …`), which the public bus receives as the body `B`.
-/

namespace ZkFormal.NearV3.RcptV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

/-- `Lp + Lv + Ls + 32·kt`: variable part of a receipt's size. -/
def varE : Expr := sum [c Lp, c Lv, c Ls, smul 32 (c kt)]
/-- receipt rows (active, not list header) -/
def rowE : Expr := sub (c act) (c sCL)
/-- last row of the list header -/
def lhEnd : Expr := .mul (c sCL) (c fe)
/-- rows after which a new receipt or list header may start -/
def brkE : Expr := .add (c rl) lhEnd

/-! ## Field lengths and successions -/

/-- `(state, last index)` -/
def lastIdx : List (Nat × Expr) :=
  [ (sCL, k 11), (sPL, k 3), (sP, sub (c Lp) (k 1)), (sVL, k 3), (sV, sub (c Lv) (k 1)),
    (sRID, k 31), (sT0, k 0), (sSL, k 3), (sS, sub (c Ls) (k 1)), (sKT, k 0),
    (sPK, .add (k 31) (smul 32 (c kt))), (sGP, k 15), (sTL, k 12), (sDEP, k 15),
    (sXP0, k 3), (sXRI, k 31), (sXG, k 7), (sXST, k 4), (sXL0, k 3), (sXLH, k 31),
    (sXRH, k 15), (sXRF, k 9), (sXRZ, k 15) ]

/-- `(state, next state, condition)` inside a receipt: at the field's last row, `cond = 1`
forces the next row's state.  (The list header's successor is a receipt or a header.) -/
def succ : List (Nat × Nat × Expr) :=
  [ (sPL, sP, k 1), (sP, sVL, k 1), (sVL, sV, k 1), (sV, sRID, k 1),
    (sRID, sT0, k 1), (sT0, sSL, k 1), (sSL, sS, k 1), (sS, sKT, k 1), (sKT, sPK, k 1),
    (sPK, sGP, k 1), (sGP, sTL, k 1), (sTL, sDEP, k 1), (sDEP, sXP0, k 1),
    (sXP0, sXRI, c hr), (sXP0, sXG, not (c hr)), (sXRI, sXG, k 1), (sXG, sXST, k 1),
    (sXST, sXL0, k 1), (sXL0, sXLH, k 1), (sXLH, sXRH, c hr), (sXRH, sXRF, k 1),
    (sXRF, sXRZ, k 1) ]

/-- `|B|` from the public header (`u32`, little endian). -/
def blenE : Expr := sum ((List.range 4).map fun x => smul (256 ^ x) (.pub (PH_BLEN + x)))
/-- `n` from the public header. -/
def nPubE : Expr := sum ((List.range 4).map fun x => smul (256 ^ x) (.pub (PH_N + x)))

def boolCols : List Nat :=
  [act, rf, rl, lastR, fs, fe, kz, gKA, r1, sys, ee, kt, hr, ge, big, gDg] ++ states ++
    (List.range 66).map xb ++
    [le, gV, gS, dm, dd, gKB, fkF, gF, gAK, eqL, eqH, gBd, eL, eH]

def cStates : List Expr :=
  boolCols.map (fun x => bool (c x)) ++
  [ sub (sum (states.map c)) (c act),
    -- field bookkeeping
    mul3 (c act) (not (c fe)) (sub (n idx) (.add (c idx) (k 1))),
    mul3 (c act) (not (c fe)) (n fs) ] ++
  states.map (fun s => mul3 (c act) (not (c fe)) (sub (n s) (c s))) ++
  [ mul3 (c fe) (n act) (n idx), mul3 (c fe) (n act) (not (n fs)) ] ++
  lastIdx.map (fun (s, e) => mul3 (c fe) (c s) (sub (c idx) e)) ++
  succ.map (fun (s, s', g) => .mul (mul3 (c fe) (c s) g) (not (n s'))) ++
  [ -- first row: a list header starts; the table ends with padding
    .mul .isFirst (not (c sCL)), .mul .isFirst (not (c fs)), .mul .isFirst (c idx),
    .mul .isLast (c act),
    mul3 .isTransition (not (c act)) (n act),
    -- receipt boundaries
    sub (c rl) (.mul (c fe) (.add (c sXRZ) (.mul (c sXLH) (not (c hr))))),
    .mul (c rf) (not (c sPL)), .mul (c rf) (not (c fs)), mul3 (c sPL) (c fs) (not (c rf)),
    .mul (c rf) (c idx),
    -- after a header or a receipt: a receipt or a header (or padding)
    mul3 brkE (n act) (not (.add (n sPL) (n sCL))),
    -- last row of a list / of the active part
    sub (c le) (.mul brkE (not (n rf))),
    sub (c lastR) (.mul (c le) (not (n act))),
    -- list constants
    .mul .isFirst (c j),
    mul3 (c le) (n act) (sub (n j) (.add (c j) (k 1))),
    -- the header loads `nj` (its bytes 8, 9 are the `u32 n_j` bytes; `n_j < 2^16`)
    mul3 (c sCL) (c fs) (sub (c nj) (.add (c (reg 8)) (smul 256 (c (reg 9))))),
    mul3 (c sCL) (c fs) (c (reg 10)), mul3 (c sCL) (c fs) (c (reg 11)),
    -- receipt index: global
    .mul .isFirst (c r),
    .mul (n act) (.mul brkE (sub (n r) (.add (c r) (c rl)))),
    -- receipts of the list: `cj` from 0, `nj` at the end
    .mul (c sCL) (c cj),
    .mul (n rf) (.mul brkE (sub (n cj) (.add (c cj) (k 1)))),
    .mul (c le) (sub (c cj) (c nj)),
    -- `RC(j)` offsets: a header has length 12, the first receipt starts at 12
    .mul (c sCL) (sub (c oEnd) (k 12)),
    .mul (n rf) (.mul brkE (sub (n o) (c oEnd))),
    -- body positions: global, from 8; a header emits none
    .mul .isFirst (sub (c o2) (k 8)),
    .mul (c sCL) (sub (c o2End) (c o2)),
    .mul (n act) (.mul (.add (c sCL) (c rl)) (sub (n o2) (c o2End))),
    -- receipt sizes
    .mul rowE (sub (c oEnd) (.add (c o) (.add (k 123) varE))),
    .mul rowE (sub (c o2End)
      (.add (c o2) (.mul (c hr) (sum [k 129, smul 2 (c Ls), smul 32 (c kt)])))),
    -- refund flag only with a surplus (see Gas)
    .mul (c hr) (not (c ge)) ] ++
  [r, o2].map (fun x => mul3 (c sCL) (not (c fe)) (sub (n x) (c x))) ++
  rconsts.map (fun x => mul3 rowE (not (c rl)) (sub (n x) (c x))) ++
  lconsts.map (fun x => mul3 (c act) (not (c le)) (sub (n x) (c x)))

/-! ## Emission slots -/

def PEO : Expr := mid K_PEO (c r)
def LEAF : Expr := mid K_LEAF (c r)
def RIDm : Expr := mid K_RID (c r)
def RC : Expr := mid K_RC (c j)
def RF : Expr := k K_RF
def ix : Expr := c idx
def at' (base : List Expr) : Expr := sum (base ++ [ix])

/-- `(Id, pos, value, gate)` of one emission. -/
abbrev Em := Expr × Expr × Expr × Expr

def bE : Expr := c b

/-- The emissions of each state, slots 1–3 (missing slots are gated off).  v1's, except the
header (`RC(j)` only; the body prefix `u32 0 ‖ u32 nref` is checked natively). -/
def emits : List (Nat × List Em) :=
  [ (sCL, [(RC, ix, c (reg 0), k 1)]),
    (sPL, [(RC, at' [c o], bE, k 1)]),
    (sP, [(RC, at' [c o, k 4], bE, k 1)]),
    (sVL, [(RC, at' [c o, k 4, c Lp], bE, k 1),
           (PEO, at' [k 28, smul 32 (c hr)], bE, k 1)]),
    (sV, [(RC, at' [c o, k 8, c Lp], bE, k 1),
          (PEO, at' [k 32, smul 32 (c hr)], bE, k 1)]),
    (sRID, [(RC, at' [c o, k 8, c Lp, c Lv], bE, k 1), (LEAF, at' [k 4], bE, k 1),
            (RIDm, ix, bE, c hr)]),
    (sT0, [(RC, sum [c o, k 40, c Lp, c Lv], bE, k 1), (RF, sum [c o2, k 46, c Ls], bE, c hr)]),
    (sSL, [(RC, at' [c o, k 41, c Lp, c Lv], bE, k 1), (RF, at' [c o2, k 10], bE, c hr),
           (RF, at' [c o2, k 47, c Ls], bE, c hr)]),
    (sS, [(RC, at' [c o, k 45, c Lp, c Lv], bE, k 1), (RF, at' [c o2, k 14], bE, c hr),
          (RF, at' [c o2, k 51, c Ls], bE, c hr)]),
    (sKT, [(RC, sum [c o, k 45, c Lp, c Lv, c Ls], bE, k 1),
           (RF, sum [c o2, k 51, smul 2 (c Ls)], bE, c hr)]),
    (sPK, [(RC, at' [c o, k 46, c Lp, c Lv, c Ls], bE, k 1),
           (RF, at' [c o2, k 52, smul 2 (c Ls)], bE, c hr)]),
    (sGP, [(RC, at' [c o, k 78, varE], bE, k 1),
           (PEO, at' [k 12, smul 32 (c hr)], c burnt, k 1),
           (RF, at' [c o2, k 113, smul 2 (c Ls), smul 32 (c kt)], c ramt, c hr)]),
    (sTL, [(RC, at' [c o, k 94, varE], bE, k 1),
           (RF, at' [c o2, k 100, smul 2 (c Ls), smul 32 (c kt)], bE, c hr)]),
    (sDEP, [(RC, at' [c o, k 107, varE], bE, k 1)]),
    (sXP0, [(PEO, ix, bE, k 1)]),
    (sXRI, [(PEO, at' [k 4], bE, k 1), (RF, at' [c o2, k 14, c Ls], bE, k 1)]),
    (sXG, [(PEO, at' [k 4, smul 32 (c hr)], bE, k 1)]),
    (sXST, [(PEO, at' [k 32, smul 32 (c hr), c Lv], bE, k 1)]),
    (sXL0, [(LEAF, ix, bE, k 1)]),
    (sXLH, [(LEAF, at' [k 36], bE, k 1)]),
    (sXRH, [(RIDm, at' [k 32], bE, k 1)]),
    (sXRF, [(RF, at' [c o2], bE, k 1)]),
    (sXRZ, [(RF, at' [c o2, k 84, smul 2 (c Ls), smul 32 (c kt)], bE, k 1)]) ]

def eId (e : Nat) : Nat := [e1Id, e2Id, e3Id].getD e 0
def ePos (e : Nat) : Nat := [e1Pos, e2Pos, e3Pos].getD e 0
def eV (e : Nat) : Nat := [e1V, e2V, e3V].getD e 0
def eG (e : Nat) : Nat := [e1G, e2G, e3G].getD e 0

def cEmit : List Expr :=
  (List.range 3).map (fun e => bool (c (eG e))) ++
  (List.range 3).map (fun e => .mul (not (c act)) (c (eG e))) ++
  emits.flatMap fun (s, ems) =>
    (List.range 3).flatMap fun e =>
      match ems[e]? with
      | some (id, p, v, g) =>
        [.mul (c s) (sub (c (eId e)) id), .mul (c s) (sub (c (ePos e)) p),
         .mul (c s) (sub (c (eV e)) v), .mul (c s) (sub (c (eG e)) g)]
      | none => [.mul (c s) (c (eG e))]

end ZkFormal.NearV3.RcptV3
