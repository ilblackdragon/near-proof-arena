import ZkFormal.Near.Tables.Dsl

/-!
# ZkFormal.Near.Tables.Node — the trie node byte stream (NEAR-AIR.md §3.1)

One row per byte of the serialization (`RawTrieNodeWithSize` borsh) of a
revealed trie node; the pre-state byte `b` and the post-state byte `pb` are
emitted together.  Nodes are contiguous segments (`nf` first row, `nl` last
row), node `0` (the first row) is the root, then one `SUM` row (revealed-size
bound), then padding (`act = 0`).

Within a node the rows run through *fields* (one-hot `sX`, `idx` = index in
the field, `fs`/`fe` = first/last row of the field):

```
leaf : TAG HPL HPF KEY* VLEN VH MEM          ext : TAG HPL HPF KEY* CH MEM
b1   : TAG BM (CH)* MEM                      b2  : TAG VLEN VH BM (CH)* MEM
```

(`KEY*` has `hplen − 1` rows; `(CH)*` is one 32-row window per present child.)
Hash windows (`VH`, `CH`) are read from the shift registers `reg` (pre) and
`preg` (post), loaded at the window's first row: by the `DIGEST` lookups of a
revealed child (`rv`, node `cid` of length `clen`) or of a touched value
(`tv`, `VPRE/VPOST(nid)`, length 72); otherwise `preg = reg` (post = pre).

Interactions: `BYTES` pre/post; `DIGEST` window pre/post and root pre/post;
`PARENT` send (revealed child window: id, depth, length, walk target) /
receive (non-root node start); `VSLOT` receive (touched node); `EDGE`
providers A and B (see `cLinks`), each chained: send `(e, 0)`, receive
`(e, m)`.  Walk targets `res` skip empty-key extensions, so walks never take
epsilon steps (a walk has at most `2 + 130 + 1` steps).
-/

namespace ZkFormal.Near.Node

open ZkFormal.Air ZkFormal.Near.Dsl

/-! ## Layout -/

def act : Nat := 0
def nf : Nat := 1
def nl : Nat := 2
def sumr : Nat := 3
def nid : Nat := 4
def pos : Nat := 5
def len : Nat := 6
def depth : Nat := 7
def b : Nat := 8
def pb : Nat := 9
def tl : Nat := 10
def te : Nat := 11
def tb1 : Nat := 12
def tb2 : Nat := 13
def sTAG : Nat := 14
def sHPL : Nat := 15
def sHPF : Nat := 16
def sKEY : Nat := 17
def sVLEN : Nat := 18
def sVH : Nat := 19
def sBM : Nat := 20
def sCH : Nat := 21
def sMEM : Nat := 22
def idx : Nat := 23
def fs : Nat := 24
def fe : Nat := 25
def hplen : Nat := 26
def odd : Nat := 27
def nokey : Nat := 28
/-- nibble bits of a key byte: `hbit i` (high nibble), `lbit i` (low nibble) -/
def hbit (i : Nat) : Nat := 29 + i
def lbit (i : Nat) : Nat := 33 + i
def bm (i : Nat) : Nat := 37 + i
def nochild : Nat := 53
def jj (i : Nat) : Nat := 54 + i
def w : Nat := 70
def lastw : Nat := 71
def reg (i : Nat) : Nat := 72 + i
def preg (i : Nat) : Nat := 104 + i
def rv : Nat := 136
def cid : Nat := 137
def clen : Nat := 138
def tv : Nat := 139
def dI : Nat := 140
def dL : Nat := 141
def gD : Nat := 142
def gP : Nat := 143
def gV : Nat := 144
def gA : Nat := 145
def aI : Nat := 146
def aS : Nat := 147
def aN : Nat := 148
def aJ : Nat := 149
def mA : Nat := 150
def mB : Nat := 151
def sz : Nat := 152
/-- walk target of the node: itself, or (empty-key extension) its child's target -/
def res : Nat := 153
/-- the window's child's walk target (sent on `PARENT`) -/
def cres : Nat := 154
/-- extension: child's walk target / child revealed / child unrevealed / single-nibble key -/
def xres : Nat := 155
def xrv : Nat := 156
def xdead : Nat := 157
def xlast0 : Nat := 158
/-- empty-key extension -/
def eext : Nat := 159
/-- edge B gate and target -/
def gB : Nat := 160
def bN : Nat := 161
def bJ : Nat := 162
def width : Nat := 163

/-- The nine field states. -/
def states : List Nat := [sTAG, sHPL, sHPF, sKEY, sVLEN, sVH, sBM, sCH, sMEM]

/-! ## Derived expressions -/

def hiE : Expr := bits (fun i => c (hbit i)) 0 4
def loE : Expr := bits (fun i => c (lbit i)) 0 4
/-- number of key nibbles `2·(hplen − 1) + odd` -/
def sE : Expr := .add (smul 2 (sub (c hplen) (k 1))) (c odd)
/-- key nibbles consumed before the high nibble of this key byte -/
def kiE : Expr := .add (smul 2 (c idx)) (c odd)
def popE : Expr := sum ((List.range 16).map fun i => c (bm i))
def isBr : Expr := .add (c tb1) (c tb2)
def tagE : Expr := .add (c tb1) (.add (smul 2 (c tb2)) (smul 3 (c te)))
def winE : Expr := .add (c sVH) (c sCH)
/-- child slot index of the window -/
def jIdxE : Expr := sum ((List.range 16).map fun i => smul i (c (jj i)))
/-- number of present children below the window's slot -/
def belowE : Expr :=
  sum ((List.range 16).map fun i => .mul (c (jj i)) (sum ((List.range i).map fun i' => c (bm i'))))
/-- windows of the node: `pop` for branches, `1` for extensions -/
def nWinE : Expr := .add (.mul isBr popE) (c te)
def chStart : Expr := .mul (c fs) (c sCH)
def vhStart : Expr := .mul (c fs) (c sVH)
/-- first row of a touched value window (`gD − gP`, degree 1) -/
def valStart : Expr := sub (c gD) (c gP)
def bmLo : Expr := bits (fun i => c (bm i)) 0 8
def bmHi : Expr := bits (fun i => c (bm i)) 8 8

/-! ## Constraints -/

/-- Boolean columns. -/
def boolCols : List Nat :=
  [act, nf, nl, sumr, tl, te, tb1, tb2] ++ states ++ [fs, fe, odd, nokey] ++
  (List.range 4).map hbit ++ (List.range 4).map lbit ++ (List.range 16).map bm ++ [nochild] ++
  (List.range 16).map jj ++ [lastw, rv, tv, gD, gP, gV, gA, xrv, xdead, xlast0, eext, gB]

def cBool : List Expr := boolCols.map fun x => bool (c x)

/-- Row kinds, first/last row. -/
def cRows : List Expr :=
  [ sub (.add (c tl) (.add (c te) isBr)) (c act),            -- one type per active row
    sub (sum (states.map c)) (c act),                         -- one field per active row
    .mul (c act) (c sumr),
    .mul (c nf) (not (c act)), .mul (c nl) (not (c act)),
    .mul .isFirst (not (c act)), .mul .isFirst (not (c nf)), .mul .isFirst (c nid),
    .mul .isFirst (c depth), .mul .isFirst (c sz),
    .mul .isLast (c act),
    -- node start
    .mul (c nf) (not (c sTAG)), .mul (c nf) (not (c fs)), .mul (c nf) (c pos), .mul (c nf) (c idx),
    -- node end
    .mul (c nl) (not (c fe)), .mul (c nl) (not (c sMEM)), mul3 (c sMEM) (c fe) (not (c nl)),
    .mul (c nl) (sub (.add (c pos) (k 1)) (c len)) ]

/-- Node-constant columns. -/
def nodeConst : List Nat :=
  [nid, len, depth, tl, te, tb1, tb2, hplen, odd, nokey, nochild, tv, res, xres, xrv, xdead, xlast0, eext] ++
    (List.range 16).map bm

/-- Transitions (current row active). -/
def cTrans : List Expr :=
  let inNode := .mul (c act) (not (c nl))
  [ .mul inNode (not (n act)), .mul inNode (n nf), .mul inNode (sub (n pos) (.add (c pos) (k 1))) ] ++
  nodeConst.map (fun x => .mul inNode (sub (n x) (c x))) ++
  [ .mul (c nl) (sub (k 1) (.add (n act) (n sumr))),
    mul3 (c nl) (n act) (not (n nf)),
    mul3 (c nl) (n act) (sub (n nid) (.add (c nid) (k 1))),
    -- SUM and padding rows are followed by padding (not on the last row)
    mul3 .isTransition (c sumr) (n act), mul3 .isTransition (c sumr) (n sumr),
    mul3 .isTransition (not (.add (c act) (c sumr))) (n act),
    mul3 .isTransition (not (.add (c act) (c sumr))) (n sumr),
    -- revealed size
    .mul .isTransition (sub (n sz) (.add (c sz) (.add (c act) (smul 72 (.mul (c nl) (c tv)))))),
    .mul (c sumr) (sub (.add (c sz) (bits (fun i => c (reg i)) 0 22)) (k 3000000)) ] ++
  (List.range 22).map fun i => .mul (c sumr) (bool (c (reg i)))

/-- Fields: succession, lengths, field constants. -/
def cFields : List Expr :=
  let inField := .mul (c act) (not (c fe))
  states.map (fun x => .mul inField (sub (n x) (c x))) ++
  [ .mul inField (sub (n idx) (.add (c idx) (k 1))), .mul inField (n fs),
    mul3 (c fe) (not (c nl)) (n idx), mul3 (c fe) (not (c nl)) (not (n fs)),
    -- lengths
    mul3 (c fe) (c sTAG) (c idx), mul3 (c fe) (c sHPL) (sub (c idx) (k 3)),
    mul3 (c fe) (c sHPF) (c idx), mul3 (c fe) (c sKEY) (sub (.add (c idx) (k 2)) (c hplen)),
    mul3 (c fe) (c sVLEN) (sub (c idx) (k 3)), mul3 (c fe) (c sVH) (sub (c idx) (k 31)),
    mul3 (c fe) (c sBM) (sub (c idx) (k 1)), mul3 (c fe) (c sCH) (sub (c idx) (k 31)),
    mul3 (c fe) (c sMEM) (sub (c idx) (k 7)),
    -- successions
    mul3 (c fe) (c sTAG) (sub (.add (c tl) (c te)) (n sHPL)),
    mul3 (c fe) (c sTAG) (sub (c tb1) (n sBM)),
    mul3 (c fe) (c sTAG) (sub (c tb2) (n sVLEN)),
    mul3 (c fe) (c sHPL) (not (n sHPF)),
    mul3 (c fe) (c sHPF) (sub (not (c nokey)) (n sKEY)),
    mul3 (c fe) (c sHPF) (sub (.mul (c nokey) (c tl)) (n sVLEN)),
    mul3 (c fe) (c sHPF) (sub (.mul (c nokey) (c te)) (n sCH)),
    mul3 (c fe) (c sKEY) (sub (c tl) (n sVLEN)),
    mul3 (c fe) (c sKEY) (sub (c te) (n sCH)),
    mul3 (c fe) (c sVLEN) (not (n sVH)),
    mul3 (c fe) (c sVH) (sub (c tl) (n sMEM)),
    mul3 (c fe) (c sVH) (sub (c tb2) (n sBM)),
    mul3 (c fe) (c sBM) (sub (c nochild) (n sMEM)),
    mul3 (c fe) (c sBM) (sub (not (c nochild)) (n sCH)),
    mul3 (c fe) (c sCH) (sub (k 1) (.add (n sCH) (n sMEM))),
    mul3 (c fe) (c sCH) (sub (c lastw) (n sMEM)),
    -- flags
    .mul (c nokey) (sub (c hplen) (k 1)),
    .mul (c nochild) popE,
    .mul (c tv) (.add (c tb1) (c te)) ] ++
  (List.range 16).map (fun i => .mul (.add (c tl) (c te)) (c (bm i)))

/-- Byte contents of the non-window fields. -/
def cBytes : List Expr :=
  [ .mul (c sTAG) (sub (c b) tagE),
    mul3 (c sHPL) (c fs) (sub (c b) (c hplen)),
    mul3 (c sHPL) (not (c fs)) (c b),
    .mul (.add (c sHPF) (c sKEY)) (sub (c b) (.add (smul 16 hiE) loE)),
    .mul (c sHPF) (sub hiE (.add (smul 2 (c tl)) (c odd))),
    mul3 (c sHPF) (not (c odd)) loE,
    .mul (mul3 (c tv) (c sVLEN) (c fs)) (sub (c b) (k 72)),
    .mul (mul3 (c tv) (c sVLEN) (not (c fs))) (c b),
    mul3 (c sBM) (c fs) (sub (c b) bmLo),
    mul3 (c sBM) (not (c fs)) (sub (c b) bmHi),
    -- post = pre outside the windows
    .mul (sub (c act) winE) (sub (c pb) (c b)) ]

/-- Windows: register reads and shifts, loads, child slot bookkeeping. -/
def windowConst : List Nat := [rv, cid, clen, cres, w, lastw] ++ (List.range 16).map jj

def cWindows : List Expr :=
  [ .mul winE (sub (c b) (c (reg 0))), .mul winE (sub (c pb) (c (preg 0))) ] ++
  (List.range 31).flatMap (fun i =>
    [ mul3 winE (not (c fe)) (sub (n (reg i)) (c (reg (i + 1)))),
      mul3 winE (not (c fe)) (sub (n (preg i)) (c (preg (i + 1)))) ]) ++
  -- unrevealed child / untouched value: post window = pre window
  (List.range 32).flatMap (fun i =>
    [ .mul (mul3 (c fs) (c sCH) (not (c rv))) (sub (c (preg i)) (c (reg i))),
      .mul (mul3 (c fs) (c sVH) (not (c tv))) (sub (c (preg i)) (c (reg i))) ]) ++
  windowConst.map (fun x => mul3 (c sCH) (not (c fe)) (sub (n x) (c x))) ++
  [ .mul (c rv) (not (c sCH)),
    -- digest lookups at the window start
    sub (c gD) (.add (c gP) (.mul vhStart (c tv))),
    .mul (c gP) (sub (c dI) (mid K_NPRE (c cid))),
    .mul (c gP) (sub (c dL) (c clen)),
    .mul valStart (sub (c dI) (mid K_VPRE (c nid))),
    .mul valStart (sub (c dL) (k 72)),
    -- window index and child slot
    .mul (mul3 (c fe) (not (c sCH)) (n sCH)) (n w),
    .mul (mul3 (c fe) (c sCH) (n sCH)) (sub (n w) (.add (c w) (k 1))),
    mul3 isBr (c sCH) (sub (sum ((List.range 16).map fun i => c (jj i))) (k 1)),
    mul3 isBr (c sCH) (sub (sum ((List.range 16).map fun i => .mul (c (jj i)) (c (bm i)))) (k 1)),
    mul3 isBr (c sCH) (sub belowE (c w)),
    .mul (c te) (.mul (c sCH) (c w)),
    mul3 (c lastw) (c sCH) (sub (.add (c w) (k 1)) nWinE) ]

/-- Walk targets (`res`), parent/slot/edge gates and edge contents.

Edges (provider A per row, B on key bytes):
* key byte `m` (`ki = 2m + odd`): A `(N,ki) –hi→ (N,ki+1)`; B `(N,ki+1) –lo→ (N,ki+2)`,
  except that the last nibble of an extension goes to `(xres, 0)` (and is absent
  if the child is unrevealed);
* odd first nibble: A `(N,0) –x0→ (N,1)` (extension with a one-nibble key: `(xres,0)`);
* branch child window (revealed): A `(N,0) –j→ (cres,0)`;
* touched value window: A `(N, tl·s) –END→ (N,0)`;
* root, first row: A `(0,0) –START→ (res,0)` (the walk's first step).
Empty-key extensions provide nothing; their `res` is their child's `res`
(or themselves, a dead end, if the child is unrevealed). -/
def cLinks : List Expr :=
  [ sub (c gP) (.mul chStart (c rv)),
    sub (c gV) (.mul (c nf) (c tv)),
    -- extension flags
    sub (c eext) (mul3 (c te) (c nokey) (not (c odd))),
    sub (c xdead) (.mul (c te) (not (c xrv))),
    sub (c xlast0) (.mul (c te) (c nokey)),
    mul3 (c te) (c sCH) (sub (c xrv) (c rv)),
    .mul (c xrv) (not (c te)),
    .mul (.mul (c te) (c sCH)) (sub (c xres) (c cres)),
    -- walk target
    .mul (sub (c act) (c eext)) (sub (c res) (c nid)),
    mul3 (c eext) (not (c xrv)) (sub (c res) (c nid)),
    mul3 (c eext) (c xrv) (sub (c res) (c xres)),
    -- gates
    sub (c gA) (.add (c sKEY) (.add (mul3 (c sHPF) (c odd) (not (.mul (c nokey) (c xdead))))
      (.add (.mul (c gP) isBr) (.add valStart .isFirst)))),
    sub (sub (c gB) (c sKEY)) (.neg (mul3 (c sKEY) (c fe) (c xdead))),
    -- key byte: high nibble (A), low nibble (B)
    .mul (c sKEY) (sub (c aI) kiE), .mul (c sKEY) (sub (c aS) hiE),
    .mul (c sKEY) (sub (c aN) (c nid)), .mul (c sKEY) (sub (c aJ) (.add kiE (k 1))),
    .mul (.mul (c sKEY) (not (.mul (c fe) (c te)))) (sub (c bN) (c nid)),
    .mul (.mul (c sKEY) (not (.mul (c fe) (c te)))) (sub (c bJ) (.add kiE (k 2))),
    mul3 (c sKEY) (c fe) (.mul (c te) (sub (c bN) (c xres))),
    mul3 (c sKEY) (c fe) (.mul (c te) (c bJ)),
    -- odd first nibble
    .mul (.mul (c sHPF) (c odd)) (c aI), .mul (.mul (c sHPF) (c odd)) (sub (c aS) loE),
    .mul (mul3 (c sHPF) (c odd) (not (c xlast0))) (sub (c aN) (c nid)),
    .mul (mul3 (c sHPF) (c odd) (not (c xlast0))) (sub (c aJ) (k 1)),
    .mul (mul3 (c sHPF) (c odd) (c xlast0)) (sub (c aN) (c xres)),
    .mul (mul3 (c sHPF) (c odd) (c xlast0)) (c aJ),
    -- branch child
    .mul (.mul (c gP) isBr) (c aI), .mul (.mul (c gP) isBr) (sub (c aS) jIdxE),
    .mul (.mul (c gP) isBr) (sub (c aN) (c cres)), .mul (.mul (c gP) isBr) (c aJ),
    -- value slot
    .mul valStart (sub (c aI) (.mul (c tl) sE)),
    .mul valStart (sub (c aS) (k SYM_END)),
    .mul valStart (sub (c aN) (c nid)),
    .mul valStart (c aJ),
    -- root: the walk's first step
    .mul .isFirst (c aI), .mul .isFirst (sub (c aS) (k SYM_START)),
    .mul .isFirst (sub (c aN) (c res)), .mul .isFirst (c aJ) ]

def constraints : List Expr := cBool ++ cRows ++ cTrans ++ cFields ++ cBytes ++ cWindows ++ cLinks

/-! ## Interactions -/

def edgeA (u : Expr) : List Expr := [c nid, c aI, c aS, c aN, c aJ, u]
def edgeB (u : Expr) : List Expr := [c nid, .add kiE (k 1), loE, c bN, c bJ, u]

def interactions : List Interaction :=
  [ send B_BYTES (c act) [mid K_NPRE (c nid), c pos, c b],
    send B_BYTES (c act) [mid K_NPOST (c nid), c pos, c pb],
    recv B_DIGEST (c gD) ([c dI, c dL] ++ (List.range 32).map fun i => c (reg i)),
    recv B_DIGEST (c gD) ([.add (c dI) (k 1), c dL] ++ (List.range 32).map fun i => c (preg i)),
    recv B_DIGEST .isFirst ([k K_NPRE, c len] ++ (List.range 32).map fun i => .pub (PV_PRE + i)),
    recv B_DIGEST .isFirst ([k K_NPOST, c len] ++ (List.range 32).map fun i => .pub (PV_POST + i)),
    send B_PARENT (c gP) [c cid, .add (c depth) (k 1), c clen, c cres],
    recv B_PARENT (sub (c nf) .isFirst) [c nid, c depth, c len, c res],
    recv B_VSLOT (c gV) [c nid],
    send B_EDGE (c gA) (edgeA (k 0)),
    recv B_EDGE (c gA) (edgeA (c mA)),
    send B_EDGE (c gB) (edgeB (k 0)),
    recv B_EDGE (c gB) (edgeB (c mB)) ]

/-- Height cap: `2^22` rows (revealed bytes `≤ 3,000,000` plus the `SUM` row). -/
def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.Near.Node
