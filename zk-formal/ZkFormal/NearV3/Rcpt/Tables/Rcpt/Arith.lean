import ZkFormal.NearV3.Rcpt.Tables.Rcpt.Fields
import ZkFormal.Near.Tables.Rcpt.Arith

/-!
# ZkFormal.NearV3.Rcpt.Tables.Rcpt.Arith — registers, ids, keys, gas, balances, v3 checks

v1's `Rcpt.Arith` (`Near/Tables/Rcpt/Arith.lean`) without the claim rows, and:

* **Registers.** The list header loads `u64 own` (public) and the two bytes of `n_j`; `bgp`
  and `height` come from the prepared header (`PH_GP`, `PH_HEIGHT`).  `tok` starts at `0`
  and is compared with `H.prev_balance_burnt` (`PH_BURNT`) on the last active row.
* **System receipts** (`sys`): predecessor `= "system"` (both directions: `sys = 1 ⇒` length 6
  and the six bytes match, `sys = 0 ⇒` v1's inequality witness); no refund, burn price `0`
  (`pc = (1 − sys)·p`, so `burnt = 0`, tokens unchanged, outcome `tokens_burnt = 0`).
* **Signer = receiver** (`ee`, only with `sys`): with `ee` every signer byte receives the
  receiver byte at its position on `SREC (r, i, ·)` (and `Ls = Lv`); without `ee` a system
  receipt shows `Ls ≠ Lv` (`dz`) or one position whose bytes differ (`dd`).
* **Access-key walk** (`ee`): key `[2] ‖ signer ‖ [2] ‖ pk.encode` on `KEYNIB` (walk
  `W_AK + r`; symbols from the `T0`, `SL`, `S`, `KT`, `PK` rows, `END` on the first `GP` row);
  its `FINAL` on the `T0` row: absent, or a value record `kF` validated by `akeyV3` (`AKC`).
* **Routing (A2)**: the receiver against the own interval `q` (`[lo, hi)`), byte by byte on the
  `V` rows and at position `Lv` on the first `RID` row (where the receiver byte is `0`, the
  end marker), with chained `BND` lookups while undecided.
-/

namespace ZkFormal.NearV3.RcptV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl NearSpec

/-! ## Expression helpers (v1's, over `rcptV3`'s column names) -/

def bitsX (off len : Nat) : Expr := bits (fun j => c (xb j)) off len
def bitsXn (off len : Nat) : Expr := bits (fun j => n (xb j)) off len
def pubs (off len : Nat) : List Expr := (List.range len).map fun j => .pub (off + j)
def ks (l : List Nat) : List Expr := l.map k
def leE (l : List Expr) : Expr := sum ((l.zip (List.range l.length)).map fun (e, j) => smul (256 ^ j) e)

def G_LE : List Nat := [196, 164, 183, 246, 51, 0, 0, 0]
def S_LE : List Nat := [0, 0, 232, 137, 4, 35, 199, 138]
def SS : Expr := sum [c sP, c sV, c sS]
def hiE : Expr := sum [smul 2 (c h2), smul 3 (c h3), smul 5 (c h5), smul 6 (c h6), smul 7 (c h7)]
def loE : Expr := bits (fun j => c (lb j)) 0 4
def sepE : Expr := .add (c h2) (c h5)
def sepN : Expr := .add (n h2) (n h5)
def hexE : Expr := .add (c h3) (c hx6)
def hexN : Expr := .add (n h3) (n hx6)
def sq (e : Expr) : Expr := .mul e e
def lb' (j : Nat) : Expr := c (lb j)

def DE : Expr := bitsX 0 8
def DEn : Expr := bitsXn 0 8
def pE : Expr := .add (.mul (c ge) (c (reg 0))) (.mul (not (c ge)) (c b))
def surE : Expr := .mul (c ge) DE
def conv (cs : List Nat) (x : Expr) (dl : Nat → Expr) : Expr :=
  sum ((cs.zip (List.range cs.length)).map fun (g, j) => smul g (if j = 0 then x else dl (j - 1)))
/-- bytes `16..` of `G·x` from the last row (`x`, `dl 0..2`): must vanish -/
def ovf (x : Expr) (dl : Nat → Expr) : Expr :=
  sum [smul (164 + 183 + 246 + 51) x, smul (183 + 246 + 51) (dl 0), smul (246 + 51) (dl 1),
       smul 51 (dl 2)]


/-! ## Registers -/

/-- `(state, register contents loaded at the field's first row)` -/
def loads : List (Nat × List Expr) :=
  [ (sCL, pubs PH_OWN 8),
    (sPL, [c Lp, k 0, k 0, k 0]), (sVL, [c Lv, k 0, k 0, k 0]), (sSL, [c Ls, k 0, k 0, k 0]),
    (sT0, [k 0]), (sKT, [c kt]), (sTL, ks [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3]),
    (sXP0, [c hr, k 0, k 0, k 0]), (sXG, ks G_LE), (sXST, ks [2, 0, 0, 0, 0]),
    (sXL0, ks [2, 0, 0, 0]), (sXRH, pubs PH_HEIGHT 8 ++ ks (List.replicate 8 0)),
    (sXRF, ks [6, 0, 0, 0, 115, 121, 115, 116, 101, 109]), (sXRZ, ks (List.replicate 16 0)),
    (sP, ks [115, 121, 115, 116, 101, 109]), (sGP, pubs PH_GP 16) ]

/-- States whose byte is the register head. -/
def regStates : List Nat :=
  [sPL, sVL, sSL, sT0, sKT, sTL, sXP0, sXG, sXST, sXL0, sXRH, sXRF, sXRZ, sXRI, sXLH]

def cRegs : List Expr :=
  loads.flatMap (fun (s, l) =>
    (l.zip (List.range l.length)).map fun (e, i) => mul3 (c s) (c fs) (sub (c (reg i)) e)) ++
  [ .mul (sum (regStates.map c)) (sub (c b) (c (reg 0))) ] ++
  (List.range 31).map (fun i => mul3 (c act) (not (c fe)) (sub (n (reg i)) (c (reg (i + 1))))) ++
  -- tokens: zero at the start, rewritten in GP rows, kept otherwise
  (List.range 16).map (fun i => .mul .isFirst (c (tok i))) ++
  (List.range 15).map (fun i => .mul (c sGP) (sub (n (tok i)) (c (tok (i + 1))))) ++
  [ .mul (c sGP) (sub (n (tok 15)) (bitsX 31 8)) ] ++
  (List.range 16).map (fun i =>
    .mul (sub (sub (c act) (c sGP)) (c lastR)) (sub (n (tok i)) (c (tok i))))

/-! ## Account ids, `"system"` -/

def cChars : List Expr :=
  ([h2, h3, h5, h6, h7, z, hx6] ++ (List.range 4).map lb).map (fun x => bool (c x)) ++
  [ .mul SS (sub (c b) (.add (smul 16 hiE) loE)),
    .mul SS (sub (sum [c h2, c h3, c h5, c h6, c h7]) (k 1)),
    -- low nibble ranges per high nibble
    mul3 (c h3) (lb' 3) (lb' 2), mul3 (c h3) (lb' 3) (lb' 1),
    .mul (c z) loE, mul3 SS (not (c z)) (sub (.mul loE (c linv)) (k 1)),
    .mul (c h6) (c z),
    mul3 (c h7) (lb' 3) (lb' 2), .mul (mul3 (c h7) (lb' 3) (lb' 1)) (lb' 0),
    .mul (c h2) (not (lb' 3)), .mul (c h2) (not (lb' 2)), .mul (c h2) (sub (.add (lb' 1) (lb' 0)) (k 1)),
    .mul (c h5) (not (lb' 0)), .mul (c h5) (not (lb' 1)), .mul (c h5) (not (lb' 2)),
    .mul (c h5) (not (lb' 3)),
    -- hex letters a–f
    sub (c l210) (mul3 (lb' 2) (lb' 1) (lb' 0)),
    .mul (c hx6) (not (c h6)), .mul (c hx6) (lb' 3), .mul (c hx6) (c l210),
    mul3 (sub (c h6) (c hx6)) (not (lb' 3)) (not (c l210)),
    -- separators: not first, not last, never doubled
    .mul (mul3 SS (not (c fe)) sepE) sepN, mul3 SS (c fs) sepE, mul3 SS (c fe) sepE,
    -- lengths 2..64
    mul3 (c fe) (c sP) (sub (sub (c Lp) (k 2)) (bitsX 0 6)),
    mul3 (c fe) (c sV) (sub (sub (c Lv) (k 2)) (bitsX 0 6)),
    mul3 (c fe) (c sS) (sub (sub (c Ls) (k 2)) (bitsX 0 6)),
    mul3 (c fe) (c sP) (sub (sub (k 64) (c Lp)) (bitsX 6 6)),
    mul3 (c fe) (c sV) (sub (sub (k 64) (c Lv)) (bitsX 6 6)),
    mul3 (c fe) (c sS) (sub (sub (k 64) (c Ls)) (bitsX 6 6)),
    -- predecessor = "system" iff `sys`
    mul3 (c sP) (c fs) (sub (c acc) (sq (sub (c b) (c (reg 0))))),
    mul3 (c sP) (not (c fe)) (sub (n acc) (.add (c acc) (sq (sub (n b) (n (reg 0)))))),
    mul3 (c sP) (c fe) (sub (c p1) (.add (c acc) (sq (sub (c Lp) (k 6))))),
    mul3 (c sP) (c fe) (sub (.mul (c p1) (c isys)) (not (c sys))),
    .mul (mul3 (c sP) (c fe) (c sys)) (c p1),
    mul3 rowE (c sys) (sub (c Lp) (k 6)),
    -- named receiver
    mul3 (c sV) (c fs) (sub (c acc) hexE),
    mul3 (c sV) (not (c fe)) (sub (n acc) (.add (c acc) hexN)),
    mul3 (c sV) (c fs) (sub (c vc0) (c b)), mul3 (c sV) (c fs) (sub (c vc1) (n b)),
    mul3 (c sV) (c fs) (sub (c h01) (.add hexE hexN)),
    mul3 (c sV) (not (c fe)) (sub (n vc0) (c vc0)), mul3 (c sV) (not (c fe)) (sub (n vc1) (c vc1)),
    mul3 (c sV) (not (c fe)) (sub (n h01) (c h01)),
    mul3 (c sV) (c fe) (sub (c p1) (.add (sq (sub (c Lv) (k 64))) (sq (sub (c acc) (c Lv))))),
    mul3 (c sV) (c fe) (sub (c p2) (sum [sq (sub (c Lv) (k 42)), sq (sub (c vc0) (k 48)),
      sq (sub (c vc1) (k 120)), sq (sub (sub (c acc) (c h01)) (k 40))])),
    mul3 (c sV) (c fe) (sub (c p3) (sum [sq (sub (c Lv) (k 42)), sq (sub (c vc0) (k 48)),
      sq (sub (c vc1) (k 115)), sq (sub (sub (c acc) (c h01)) (k 40))])),
    mul3 (c sV) (c fe) (sub (.mul (c p1) (c i1)) (k 1)),
    mul3 (c sV) (c fe) (sub (.mul (c p2) (c i2)) (k 1)),
    mul3 (c sV) (c fe) (sub (.mul (c p3) (c i3)) (k 1)) ]

/-! ## Key symbols: account walk (`r`) and access-key walk (`W_AK + r`) -/

/-- Rows whose key symbols belong to the access-key walk. -/
def akRow : Expr := sum [c sT0, c sSL, c sS, c sKT, c sPK, c sGP]
/-- Walk id of the row's `KEYNIB` sends. -/
def wE : Expr := .add (c r) (smul W_AK akRow)
/-- Nibbles of a public-key byte (scratch bits `xb 0 … 7` on `PK` rows). -/
def hiPK : Expr := bitsX 0 4
def loPK : Expr := bitsX 4 4
def two (e : Expr) : Expr := smul 2 e

def cKey : List Expr :=
  [ sub (c gKA) (sum [c sV, c kz, .mul (c sRID) (c fs),
      .mul (c ee) (sum [c sT0, .mul (c sSL) (c fs), c sS, c sKT, c sPK, .mul (c sGP) (c fs)])]),
    sub (c gKB) (.add (c sV) (.mul (c ee) (sum [c sT0, .mul (c sSL) (c fs), c sS, c sKT, c sPK]))),
    -- account walk `[0] ‖ receiver`: slot A
    .mul (c sV) (sub (c tA) (.add (k 2) (two (c idx)))), .mul (c sV) (sub (c symA) hiE),
    .mul (c sV) (c lastA),
    .mul (c kz) (sub (c tA) (c idx)), .mul (c kz) (c symA), .mul (c kz) (c lastA),
    mul3 (c sRID) (c fs) (sub (c tA) (.add (k 2) (two (c Lv)))),
    mul3 (c sRID) (c fs) (sub (c symA) (k SYM_END)),
    mul3 (c sRID) (c fs) (sub (c lastA) (k 1)),
    .mul (c kz) (not (c sVL)), mul3 (c sVL) (c fs) (not (c kz)),
    mul3 (c sVL) (not (c fe)) (sub (n kz) (c fs)),
    -- account walk: slot B (low nibbles of the receiver)
    .mul (c sV) (sub (c tB) (.add (k 3) (two (c idx)))), .mul (c sV) (sub (c symB) loE),
    -- access-key walk `[2] ‖ signer ‖ [2] ‖ kt ‖ pk`, slot A
    mul3 (c ee) (c sT0) (c tA), mul3 (c ee) (c sT0) (c symA), mul3 (c ee) (c sT0) (c lastA),
    .mul (mul3 (c ee) (c sSL) (c fs)) (sub (c tA) (.add (k 2) (two (c Ls)))),
    .mul (mul3 (c ee) (c sSL) (c fs)) (c symA), .mul (mul3 (c ee) (c sSL) (c fs)) (c lastA),
    mul3 (c ee) (c sS) (sub (c tA) (.add (k 2) (two (c idx)))),
    mul3 (c ee) (c sS) (sub (c symA) hiE), mul3 (c ee) (c sS) (c lastA),
    mul3 (c ee) (c sKT) (sub (c tA) (.add (k 4) (two (c Ls)))),
    mul3 (c ee) (c sKT) (c symA), mul3 (c ee) (c sKT) (c lastA),
    mul3 (c ee) (c sPK) (sub (c tA) (sum [k 6, two (c Ls), two (c idx)])),
    mul3 (c ee) (c sPK) (sub (c symA) hiPK), mul3 (c ee) (c sPK) (c lastA),
    mul3 (c ee) (c sPK) (sub (c b) (.add (smul 16 hiPK) loPK)),
    .mul (mul3 (c ee) (c sGP) (c fs)) (sub (c tA) (sum [k 70, two (c Ls), smul 64 (c kt)])),
    .mul (mul3 (c ee) (c sGP) (c fs)) (sub (c symA) (k SYM_END)),
    .mul (mul3 (c ee) (c sGP) (c fs)) (sub (c lastA) (k 1)),
    -- access-key walk, slot B
    mul3 (c ee) (c sT0) (sub (c tB) (k 1)), mul3 (c ee) (c sT0) (sub (c symB) (k 2)),
    .mul (mul3 (c ee) (c sSL) (c fs)) (sub (c tB) (.add (k 3) (two (c Ls)))),
    .mul (mul3 (c ee) (c sSL) (c fs)) (sub (c symB) (k 2)),
    mul3 (c ee) (c sS) (sub (c tB) (.add (k 3) (two (c idx)))),
    mul3 (c ee) (c sS) (sub (c symB) loE),
    mul3 (c ee) (c sKT) (sub (c tB) (.add (k 5) (two (c Ls)))),
    mul3 (c ee) (c sKT) (sub (c symB) (c b)),
    mul3 (c ee) (c sPK) (sub (c tB) (sum [k 7, two (c Ls), two (c idx)])),
    mul3 (c ee) (c sPK) (sub (c symB) loPK),
    -- `FINAL`: the account walk on the receipt's first row (a value record, `kslot`); the
    -- access-key walk on the `T0` row (absent, or value record `kF` validated on `AKC`)
    sub (c gF) (.add (c rf) (.mul (c ee) (c sT0))),
    .mul (c rf) (c fkF), .mul (c rf) (sub (c kF) (c kslot)),
    sub (c gAK) (mul3 (c ee) (c sT0) (not (c fkF))) ]

/-! ## System receipts, signer = receiver -/

/-- Length-difference mode of `sys ∧ ¬ee` (`dz = sys·(1 − ee)·(1 − dm)`). -/
def dzE : Expr := sub (sub (c sys) (c ee)) (c dd)

def cSys : List Expr :=
  [ mul3 rowE (c ee) (not (c sys)),
    mul3 rowE (c sys) (c hr),
    mul3 rowE (c ee) (sub (c Ls) (c Lv)),
    .mul rowE (sub (c dd) (mul3 (c sys) (not (c ee)) (c dm))),
    .mul (c rf) (.mul dzE (sub (.mul (sub (c Ls) (c Lv)) (c invL)) (k 1))),
    -- `SREC` gates: all receiver / signer rows with `ee`
    .mul (c gV) (not (c sV)), mul3 (c ee) (c sV) (not (c gV)),
    .mul (c gS) (not (c sS)), mul3 (c ee) (c sS) (not (c gS)),
    mul3 (c ee) (c sS) (sub (c sx) (c b)),
    .mul (.mul (c dd) (c gS)) (sub (.mul (sub (c b) (c sx)) (c invD)) (k 1)),
    -- `dd`: exactly one signer row looks up its receiver byte
    mul3 (c sS) (c fs) (sub (c scnt) (c gS)),
    mul3 (c sS) (not (c fe)) (sub (n scnt) (.add (c scnt) (n gS))),
    .mul (mul3 (c sS) (c fe) (c dd)) (not (c scnt)) ]

/-! ## Routing (A2) -/

/-- Lookup rows: receiver bytes, and the end marker at position `Lv` (first `RID` row). -/
def rwE : Expr := .add (c sV) (.mul (c sRID) (c fs))
def orE (a b : Expr) : Expr := sub (.add a b) (.mul a b)

def cRoute : List Expr :=
  [ sub (c gBd) (.mul rwE (orE (c eqL) (c eqH))),
    mul3 (c sV) (c fs) (sub (c eqL) (k 1)),
    mul3 (c sV) (c fs) (sub (c eqH) (not (c hnB))),
    .mul (c sV) (sub (n eqL) (.mul (c eqL) (c eL))),
    .mul (c sV) (sub (n eqH) (.mul (c eqH) (c eH))),
    .mul (c sV) (sub (c vB) (c b)), mul3 (c sRID) (c fs) (c vB),
    .mul (c sV) (sub (c iB) (c idx)), mul3 (c sRID) (c fs) (sub (c iB) (c Lv)),
    -- `vB − lo + 255` and `hi − vB + 255` as 9 bits
    .mul (c gBd) (sub (bitsX 20 9) (.add (sub (c vB) (c loB)) (k 255))),
    .mul (c gBd) (sub (bitsX 29 9) (.add (sub (c hiB) (c vB)) (k 255))),
    .mul (c gBd) (sub (.mul (sub (c vB) (c loB)) (c iL)) (not (c eL))),
    mul3 (c gBd) (c eL) (sub (c vB) (c loB)),
    .mul (c gBd) (sub (.mul (sub (c hiB) (c vB)) (c iH)) (not (c eH))),
    mul3 (c gBd) (c eH) (sub (c hiB) (c vB)),
    -- while equal so far: `lo ≤ v` and `v ≤ hi`; at the end `v < hi` strictly
    .mul (mul3 (c gBd) (c eqL) (not (c (xb 28)))) (not (c eL)),
    .mul (mul3 (c gBd) (c eqH) (not (c (xb 37)))) (not (c eH)),
    .mul (mul3 (c sRID) (c fs) (c eqH)) (c eH) ]

/-! ## Gas (`GP` rows) -/

def gp : Expr := c sGP
def cGas : List Expr :=
  let d (i : Nat) : Expr := c (dl i)
  [ .mul gp (sub (sub (c b) (c (reg 0))) (sub (.add (c c1) DE) (smul 256 (c (xb 8))))),
    .mul (.mul gp (c fs)) (c c1), mul3 gp (not (c fe)) (sub (n c1) (c (xb 8))),
    mul3 gp (c fe) (sub (c (xb 8)) (not (c ge))),
    -- effective burn price: `p` (`0` for system receipts); `gq = ge·(1 − sys)`
    .mul gp (sub (c pc) (.mul (not (c sys)) pE)),
    .mul rowE (sub (c gq) (.mul (c ge) (not (c sys)))),
    -- burnt = G·pc
    .mul gp (sub (.add (c burnt) (smul 256 (bitsX 9 11))) (.add (conv (G_LE.take 5) (c pc) d) (c c2))),
    .mul (.mul gp (c fs)) (c c2), mul3 gp (not (c fe)) (sub (n c2) (bitsX 9 11)),
    mul3 gp (c fe) (bitsX 9 11), mul3 gp (c fe) (ovf (c pc) d),
    -- refund amount = G·surplus
    .mul gp (sub (.add (c ramt) (smul 256 (bitsX 20 11)))
      (.add (conv (G_LE.take 5) surE (fun i => d (4 + i))) (c c3))),
    .mul (.mul gp (c fs)) (c c3), mul3 gp (not (c fe)) (sub (n c3) (bitsX 20 11)),
    mul3 gp (c fe) (bitsX 20 11), mul3 gp (c fe) (ovf surE (fun i => d (4 + i))),
    -- running tokens
    .mul gp (sub (.add (bitsX 31 8) (smul 256 (c (xb 39)))) (sum [c (tok 0), c burnt, c c4])),
    .mul (.mul gp (c fs)) (c c4), mul3 gp (not (c fe)) (sub (n c4) (c (xb 39))),
    mul3 gp (c fe) (c (xb 39)),
    -- refund flag: (non-system) surplus bytes vanish without a refund; a refund has a
    -- nonzero surplus
    .mul (mul3 gp (not (c hr)) (c gq)) DE,
    mul3 gp (c fs) (sub (c sumD) DE),
    mul3 gp (not (c fe)) (sub (n sumD) (.add (c sumD) DEn)),
    mul3 gp (c fe) (sub (.mul (c sumD) (c invA)) (c hr)) ] ++
  -- delay lines of pc and surplus
  (List.range 8).map (fun i => mul3 gp (c fs) (d i)) ++
  [ mul3 gp (not (c fe)) (sub (n (dl 0)) (c pc)), mul3 gp (not (c fe)) (sub (n (dl 4)) surE) ] ++
  ([1, 2, 3, 5, 6, 7].map fun i => mul3 gp (not (c fe)) (sub (n (dl i)) (d (i - 1))))

/-! ## Balances (`DEP` rows): v1's -/


def dp : Expr := c sDEP
def aftE : Expr := bitsX 0 8
def cDep : List Expr :=
  let d (j : Nat) : Expr := c (dl j)
  [ .mul dp (sub (sum [c bef, c b, c c1]) (.add aftE (smul 256 (c (xb 8))))),
    .mul (.mul dp (c fs)) (c c1), mul3 dp (not (c fe)) (sub (n c1) (c (xb 8))),
    mul3 dp (c fe) (c (xb 8)),
    -- amount ≠ u128::MAX
    mul3 dp (c fs) (sub (c dsum) (sub (k 255) aftE)),
    mul3 dp (not (c fe)) (sub (n dsum) (.add (c dsum) (sub (k 255) (bitsXn 0 8)))),
    mul3 dp (c fe) (sub (.mul (c dsum) (c invB)) (k 1)),
    -- tot = aft + locked < 2^128
    .mul dp (sub (sum [aftE, c lk, c c2]) (.add (bitsX 9 8) (smul 256 (c (xb 17))))),
    .mul (.mul dp (c fs)) (c c2), mul3 dp (not (c fe)) (sub (n c2) (c (xb 17))),
    mul3 dp (c fe) (c (xb 17)),
    -- q = 10^19·storage
    .mul dp (sub (.add (conv S_LE (c st) d) (c c3)) (.add (bitsX 18 8) (smul 256 (bitsX 26 12)))),
    .mul (.mul dp (c fs)) (c c3), mul3 dp (not (c fe)) (sub (n c3) (bitsX 26 12)),
    mul3 dp (c fe) (bitsX 26 12),
    mul3 dp (not (c fe)) (sub (n (dl 0)) (c st)),
    -- tot − q with borrow; no final borrow when `big`
    .mul dp (sub (sub (bitsX 9 8) (bitsX 18 8)) (sub (.add (c c4) (bitsX 38 8)) (smul 256 (c (xb 46))))),
    .mul (.mul dp (c fs)) (c c4), mul3 dp (not (c fe)) (sub (n c4) (c (xb 46))),
    .mul (mul3 dp (c fe) (c big)) (c (xb 46)),
    -- otherwise storage ≤ 770
    .mul (c r1) (not dp), mul3 dp (c fs) (c r1), mul3 dp (not (c fe)) (sub (n r1) (c fs)),
    mul3 (not (c big)) (c r1) (sub (k 770) (sum [c (dl 0), smul 256 (c st), bitsX 47 10])),
    mul3 (not (c big)) (sub (sub dp (c fs)) (c r1)) (c st),
    -- the read is not from the future
    mul3 dp (c fs) (sub (sub (c r) (c tprev)) (bitsX 57 9)) ] ++
  (List.range 7).map (fun j => mul3 dp (c fs) (d j)) ++
  (List.range 6).map (fun j => mul3 dp (not (c fe)) (sub (n (dl (j + 1))) (d j)))


/-! ## End of the active part, digest lookups -/

def cEnd : List Expr :=
  [ .mul (c lastR) (sub (.add (c r) rowE) nPubE),
    .mul (c lastR) (sub (c o2End) blenE) ] ++
  (List.range 16).map (fun i => .mul (c lastR) (sub (c (tok i)) (.pub (PH_BURNT + i)))) ++
  [ sub (c gDg) (.mul (c fs) (.add (c sXRI) (c sXLH))),
    mul3 (c fs) (c sXRI) (sub (c dI) (mid K_RID (c r))), mul3 (c fs) (c sXRI) (sub (c dL) (k 48)),
    mul3 (c fs) (c sXLH) (sub (c dI) (mid K_PEO (c r))),
    mul3 (c fs) (c sXLH) (sub (c dL) (sum [k 37, smul 32 (c hr), c Lv])) ]

end ZkFormal.NearV3.RcptV3
