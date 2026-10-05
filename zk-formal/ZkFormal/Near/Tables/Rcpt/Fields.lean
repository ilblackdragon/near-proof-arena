import ZkFormal.Near.Tables.Rcpt.Layout

/-!
# ZkFormal.Near.Tables.Rcpt.Fields — row structure of the `rcpt` table

Rows: 12 claim rows (`sCL`), then one segment per receipt in batch order, then
padding.  A receipt segment runs through the fields

```
PL P VL V RID T0 SL S KT PK GP TL DEP XP0 [XRI] XG XST XL0 XLH [XRH XRF XRZ]
```

(`[…]` only if the receipt has a refund, `hr = 1`).  This file: one-hot
states, field lengths and successions, receipt boundaries and the receipt
constants that change between receipts, and the emission slots of every field
(NEAR-AIR.md §3.3 table).
-/

namespace ZkFormal.Near.Rcpt

open ZkFormal.Air ZkFormal.Near.Dsl

/-- `Lp + Lv + Ls + 32·kt`: variable part of a receipt's size. -/
def varE : Expr := sum [c Lp, c Lv, c Ls, smul 32 (c kt)]
/-- receipt rows (active, not claim) -/
def rowE : Expr := sub (c act) (c sCL)

/-! ## Field lengths and successions -/

/-- `(state, last index)` -/
def lastIdx : List (Nat × Expr) :=
  [ (sCL, k 11), (sPL, k 3), (sP, sub (c Lp) (k 1)), (sVL, k 3), (sV, sub (c Lv) (k 1)),
    (sRID, k 31), (sT0, k 0), (sSL, k 3), (sS, sub (c Ls) (k 1)), (sKT, k 0),
    (sPK, .add (k 31) (smul 32 (c kt))), (sGP, k 15), (sTL, k 12), (sDEP, k 15),
    (sXP0, k 3), (sXRI, k 31), (sXG, k 7), (sXST, k 4), (sXL0, k 3), (sXLH, k 31),
    (sXRH, k 15), (sXRF, k 9), (sXRZ, k 15) ]

/-- `(state, next state, condition)`: at the field's last row, `cond = 1`
forces the next row's state. -/
def succ : List (Nat × Nat × Expr) :=
  [ (sCL, sPL, k 1), (sPL, sP, k 1), (sP, sVL, k 1), (sVL, sV, k 1), (sV, sRID, k 1),
    (sRID, sT0, k 1), (sT0, sSL, k 1), (sSL, sS, k 1), (sS, sKT, k 1), (sKT, sPK, k 1),
    (sPK, sGP, k 1), (sGP, sTL, k 1), (sTL, sDEP, k 1), (sDEP, sXP0, k 1),
    (sXP0, sXRI, c hr), (sXP0, sXG, not (c hr)), (sXRI, sXG, k 1), (sXG, sXST, k 1),
    (sXST, sXL0, k 1), (sXL0, sXLH, k 1), (sXLH, sXRH, c hr), (sXRH, sXRF, k 1),
    (sXRF, sXRZ, k 1) ]

def cStates : List Expr :=
  ([act, rf, rl, lastR, fs, fe, kz, gKA, r1, lo8, lo4, kt, hr, ge, big, gDg] ++ states ++
    (List.range 66).map xb).map (fun x => bool (c x)) ++
  [ sub (sum (states.map c)) (c act),
    -- field bookkeeping
    mul3 (c act) (not (c fe)) (sub (n idx) (.add (c idx) (k 1))),
    mul3 (c act) (not (c fe)) (n fs) ] ++
  states.map (fun s => mul3 (c act) (not (c fe)) (sub (n s) (c s))) ++
  [ mul3 (c fe) (not (c rl)) (n idx), mul3 (c fe) (not (c rl)) (not (n fs)) ] ++
  lastIdx.map (fun (s, e) => mul3 (c fe) (c s) (sub (c idx) e)) ++
  succ.map (fun (s, s', g) => .mul (mul3 (c fe) (c s) g) (not (n s'))) ++
  [ -- first row: claim rows start
    .mul .isFirst (not (c sCL)), .mul .isFirst (not (c fs)), .mul .isFirst (c idx),
    .mul .isLast (c act),
    mul3 .isTransition (not (c act)) (n act),
    -- receipt boundaries
    sub (c rl) (.mul (c fe) (.add (c sXRZ) (.mul (c sXLH) (not (c hr))))),
    sub (c lastR) (.mul (c rl) (not (n act))),
    .mul (c rf) (not (c sPL)), .mul (c rf) (not (c fs)), mul3 (c sPL) (c fs) (not (c rf)),
    -- a receipt's first row has `idx = 0` (after `rl` nothing else resets it)
    .mul (c rf) (c idx),
    mul3 (c rl) (n act) (not (n rf)),
    -- first receipt
    mul3 (c fe) (c sCL) (n r), mul3 (c fe) (c sCL) (sub (n o) (k 12)),
    mul3 (c fe) (c sCL) (sub (n o2) (k 4)), mul3 (c fe) (c sCL) (n rcnt),
    -- next receipt
    mul3 (c rl) (n act) (sub (n r) (.add (c r) (k 1))),
    mul3 (c rl) (n act) (sub (n o) (c oEnd)),
    mul3 (c rl) (n act) (sub (n o2) (c o2End)),
    mul3 (c rl) (n act) (sub (n rcnt) (.add (c rcnt) (c hr))),
    -- receipt sizes
    .mul rowE (sub (c oEnd) (.add (c o) (.add (k 123) varE))),
    .mul rowE (sub (c o2End)
      (.add (c o2) (.mul (c hr) (sum [k 129, smul 2 (c Ls), smul 32 (c kt)])))),
    -- refund flag only with a surplus (see Gas)
    .mul (c hr) (not (c ge)) ] ++
  rconsts.map (fun x => mul3 rowE (not (c rl)) (sub (n x) (c x)))

/-! ## Emission slots -/

def PEO : Expr := mid K_PEO (c r)
def LEAF : Expr := mid K_LEAF (c r)
def RIDm : Expr := mid K_RID (c r)
def RC : Expr := k K_RC
def RF : Expr := k K_RF
def ix : Expr := c idx
def at' (base : List Expr) : Expr := sum (base ++ [ix])

/-- `(Id, pos, value, gate)` of one emission. -/
abbrev Em := Expr × Expr × Expr × Expr

def bE : Expr := c b

/-- The emissions of each state, slots 1–3 (missing slots are gated off). -/
def emits : List (Nat × List Em) :=
  [ (sCL, [(RC, ix, c (reg 0), k 1), (RF, ix, c (reg 12), c lo4)]),
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

end ZkFormal.Near.Rcpt
