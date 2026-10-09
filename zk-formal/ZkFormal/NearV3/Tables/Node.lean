import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.Ids
import ZkFormal.NearV3.IdsUps

/-!
# ZkFormal.NearV3.Tables.Node — `nodeV3`: tree-shaped trie records of all instances

Lane `v3-trie`.  **v1 `node` (`Near/Tables/Node.lean`) with the same column layout for
columns `0 … 162`** (so that v1's extraction and render proofs transfer by adaptation) and
these deltas (STATUS-V3-TRIE §3.2):

* **instances**: node-constant `tau`; `PARENT (cid, τ, depth+1, clen, cres)`.  Every record,
  the root included, receives `PARENT` on its first row; a root's `PARENT (rid, τ, 0, …)`
  comes from its instance head (`headV3`), which also does the root's `DIGEST` lookups,
  the `ROOT`/`MIDROOT` endpoints and the walks' `START` edge.  v1's root rules
  (`isFirst` lookups against `pub`, `depth = 0` on row 0, the `START` edge) are removed.
* **depth ≤ 399** (`depth + 112` as 9 bits on the first row: `hbit 0‥3`, `lbit 0‥3`,
  `dbit8`): bounds `fdepth` by `trieFuel` (`pathsRevealed_of_rank`).
* **value records**: a revealed value slot (`tv`) is a window onto value record `vid`
  (`valV3`) of length `vlen`: `DIGEST (VPRE(vid), vlen, reg)`, `VPARENT (vid, vlen)`; the
  `VLEN` bytes accumulate to `vlen` (`vacc`, scale `vsc`; top byte `0`); a value written in
  lockstep (`tw`, account `set`) has `DIGEST (VPOST(vid), vlen, preg)` (same length),
  otherwise `preg = reg`.  A written window receives `VSLOT (vid)` (gate `valStart·tw`; acctV3
  sends one per account write, so writes and written windows are a bijection).  v1's constant
  `72` is removed.
* **weak uniqueness**: every digest window sends `DIGS (eid, τ, i, byte)` (`eid` = the
  child's `NPRE(cid)` or the value's `VPRE(vid)`); a duplicate record (`dup`) receives
  `DUP (NPRE(nid), repE)` and copies its bytes from its predecessor over
  `ENT (eid, len, pos, byte)`; a record with a duplicate (`hd`) provides them.
* **absent terminals**: edges carry a kind (`aK`, `bK`): key nibbles `KEY`, branch children
  `DOWN`, value windows `VAL` (target `(vid, 0)`); a leaf provides an `LEND` marker at
  `(nid, s)` (provider B on its first `MEM` row; `bI`, `bS` generalise B's position and
  symbol); an extension whose child is unrevealed provides its last nibble with the dead
  target `(nid, s)`; a branch provides `BMAP (nid, bm, tb2, ·)` (chained) on its `BM` row.
* **`UPB`** (M7c, for `upsV3`): every active row is a chained provider of
  `UPB (NPOST(nid), pos, pb, len, depth, cid, u)`: `send (…, 0)`, `recv (…, mU)` with the
  row's use count `mU` (column 185); no constraint.
* **size**: the `SUM` row sends `SIZE (0, Σ bytes of non-duplicate records)` (bus 18)
  instead of v1's `≤ 3,000,000` check (the bound is on the whole normalised witness:
  size lane).

Writes in lockstep are account `set`s (same value length).  The `0x0f` upsert is applied
afterwards, by `upsV3`, on the lockstep post-trie (`set_upsert_comm`): the head sends the
lockstep post-root on `MIDROOT`.
-/

namespace ZkFormal.NearV3.NodeV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

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
/-! v3 columns -/
def tau : Nat := 163
def dbit8 : Nat := 164
def vid : Nat := 165
def vlen : Nat := 166
def tw : Nat := 167
def vacc : Nat := 168
def vsc : Nat := 169
def dup : Nat := 170
def hd : Nat := 171
def repE : Nat := 172
def mBm : Nat := 173
def aK : Nat := 174
def bK : Nat := 175
def bI : Nat := 176
def bS : Nat := 177
/-- `LEND` marker gate (leaf, first `MEM` row) -/
def gL : Nat := 178
/-- last-nibble target of an extension: `(xres, 0)` (child revealed) or `(nid, s)` (dead) -/
def xtgt : Nat := 179
def xtgJ : Nat := 180
/-- interaction gates / message columns kept at degree 1 -/
def gS : Nat := 181
def dE : Nat := 182
def gDp : Nat := 183
def gBm : Nat := 184
/-- `UPB` use count of the row's post byte (`upsV3` reads; chained provider) -/
def mU : Nat := 185
def width : Nat := 186

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
def bmE : Expr := bits (fun i => c (bm i)) 0 16
/-- `depth + 112` as nine bits (first row) -/
def depE : Expr := .add (.add hiE (smul 16 loE)) (smul 256 (c dbit8))
/-- digest windows that announce an entry to `uniqV3` -/
def gDigs : Expr := .add (.mul (c sCH) (c rv)) (.mul (c sVH) (c tv))
def eidE : Expr := .add (.mul (c sCH) (mid K_NPRE (c cid))) (.mul (c sVH) (mid K_VPRE (c vid)))
/-- post-digest lookups: revealed children, and values written in lockstep -/
def gDpost : Expr := .add (c gP) (.mul valStart (c tw))
def bmStart : Expr := .mul (c fs) (c sBM)

/-! ## Constraints -/

/-- Boolean columns. -/
def boolCols : List Nat :=
  [act, nf, nl, sumr, tl, te, tb1, tb2] ++ states ++ [fs, fe, odd, nokey] ++
  (List.range 4).map hbit ++ (List.range 4).map lbit ++ (List.range 16).map bm ++ [nochild] ++
  (List.range 16).map jj ++ [lastw, rv, tv, gD, gP, gV, gA, xrv, xdead, xlast0, eext, gB] ++
  [dbit8, tw, dup, hd, gL, gS, gDp, gBm]

def cBool : List Expr := boolCols.map fun x => bool (c x)

/-- Row kinds, first/last row. -/
def cRows : List Expr :=
  [ sub (.add (c tl) (.add (c te) isBr)) (c act),            -- one type per active row
    sub (sum (states.map c)) (c act),                         -- one field per active row
    .mul (c act) (c sumr),
    .mul (c nf) (not (c act)), .mul (c nl) (not (c act)),
    .mul .isFirst (not (c act)), .mul .isFirst (not (c nf)), .mul .isFirst (c nid),
    .mul .isFirst (c sz),
    .mul .isLast (c act),
    -- node start; depth ≤ 399
    .mul (c nf) (sub (.add (c depth) (k 112)) depE),
    .mul (c nf) (not (c sTAG)), .mul (c nf) (not (c fs)), .mul (c nf) (c pos), .mul (c nf) (c idx),
    -- node end
    .mul (c nl) (not (c fe)), .mul (c nl) (not (c sMEM)), mul3 (c sMEM) (c fe) (not (c nl)),
    .mul (c nl) (sub (.add (c pos) (k 1)) (c len)) ]

/-- Node-constant columns. -/
def nodeConst : List Nat :=
  [nid, len, depth, tl, te, tb1, tb2, hplen, odd, nokey, nochild, tv, res, xres, xrv, xdead, xlast0, eext] ++
    (List.range 16).map bm ++ [tau, vid, vlen, tw, dup, hd, repE, xtgt, xtgJ]

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
    -- bytes of non-duplicate records (sent on `SIZE` by the `SUM` row)
    .mul .isTransition (sub (n sz) (.add (c sz) (.mul (c act) (not (c dup))))) ]

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
    .mul (c tv) (.add (c tb1) (c te)),
    .mul (c tw) (not (c tv)),
    .mul (c dup) (not (c act)), .mul (c hd) (not (c act)) ] ++
  (List.range 16).map (fun i => .mul (.add (c tl) (c te)) (c (bm i)))

/-- Byte contents of the non-window fields. -/
def cBytes : List Expr :=
  [ .mul (c sTAG) (sub (c b) tagE),
    mul3 (c sHPL) (c fs) (sub (c vacc) (c b)),
    mul3 (c sHPL) (c fs) (sub (c vsc) (k 1)),
    .mul (.add (c sHPF) (c sKEY)) (sub (c b) (.add (smul 16 hiE) loE)),
    .mul (c sHPF) (sub hiE (.add (smul 2 (c tl)) (c odd))),
    mul3 (c sHPF) (not (c odd)) loE,
    -- value length: little-endian accumulator over the `VLEN` bytes; top byte 0
    mul3 (c sVLEN) (c fs) (sub (c vacc) (c b)), mul3 (c sVLEN) (c fs) (sub (c vsc) (k 1)),
    mul3 (c sVLEN) (not (c fe)) (sub (n vacc) (.add (c vacc) (.mul (n vsc) (n b)))),
    mul3 (c sVLEN) (not (c fe)) (sub (n vsc) (smul 256 (c vsc))),
    .mul (mul3 (c tv) (c sVLEN) (c fe)) (sub (c vacc) (c vlen)),
    .mul (mul3 (c tv) (c sVLEN) (c fe)) (c b),
    mul3 (c sBM) (c fs) (sub (c b) bmLo),
    mul3 (c sBM) (not (c fs)) (sub (c b) bmHi),
    -- post = pre outside the windows
    .mul (sub (c act) winE) (sub (c pb) (c b)),
    -- Full four-byte HPL accumulator, with local byte range decomposition.
    mul3 (c sHPL) (not (c fe)) (sub (n vacc) (.add (c vacc) (.mul (n vsc) (n b)))),
    mul3 (c sHPL) (not (c fe)) (sub (n vsc) (smul 256 (c vsc))),
    mul3 (c sHPL) (c fe) (sub (c vacc) (c hplen)),
    .mul (c sHPL) (sub (c b) (.add (smul 16 hiE) loE)),
    -- The trace row bound is below 2^24; exclude field-modulus aliases.
    mul3 (c sHPL) (c fe) (c b) ]

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
      .mul (mul3 (c fs) (c sVH) (not (c tw))) (sub (c (preg i)) (c (reg i))) ]) ++
  windowConst.map (fun x => mul3 (c sCH) (not (c fe)) (sub (n x) (c x))) ++
  [ .mul (c rv) (not (c sCH)),
    -- digest lookups at the window start
    sub (c gD) (.add (c gP) (.mul vhStart (c tv))),
    .mul (c gP) (sub (c dI) (mid K_NPRE (c cid))),
    .mul (c gP) (sub (c dL) (c clen)),
    .mul valStart (sub (c dI) (mid K_VPRE (c vid))),
    .mul valStart (sub (c dL) (c vlen)),
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
    -- `gV` (v1: touched-slot gate) is the duplicate gate in v3
    sub (c gV) (.mul (c nf) (c dup)),
    sub (c gL) (mul3 (c tl) (c sMEM) (c fs)),
    sub (c gS) gDigs, .mul (c gS) (sub (c dE) eidE),
    sub (c gDp) gDpost, sub (c gBm) bmStart,
    -- extension flags
    sub (c eext) (mul3 (c te) (c nokey) (not (c odd))),
    sub (c xdead) (.mul (c te) (not (c xrv))),
    sub (c xlast0) (.mul (c te) (c nokey)),
    mul3 (c te) (c sCH) (sub (c xrv) (c rv)),
    .mul (c xrv) (not (c te)),
    .mul (.mul (c te) (c sCH)) (sub (c xres) (c cres)),
    -- last-nibble target of an extension
    .mul (c xrv) (sub (c xtgt) (c xres)), .mul (c xrv) (c xtgJ),
    .mul (c xdead) (sub (c xtgt) (c nid)), .mul (c xdead) (sub (c xtgJ) sE),
    -- walk target
    .mul (sub (c act) (c eext)) (sub (c res) (c nid)),
    mul3 (c eext) (not (c xrv)) (sub (c res) (c nid)),
    mul3 (c eext) (c xrv) (sub (c res) (c xres)),
    -- gates
    sub (c gA) (.add (c sKEY) (.add (.mul (c sHPF) (c odd)) (.add (.mul (c gP) isBr) valStart))),
    sub (c gB) (.add (c sKEY) (c gL)),
    -- key byte: high nibble (A), low nibble (B)
    .mul (c sKEY) (sub (c aI) kiE), .mul (c sKEY) (sub (c aS) hiE),
    .mul (c sKEY) (sub (c aN) (c nid)), .mul (c sKEY) (sub (c aJ) (.add kiE (k 1))),
    .mul (c sKEY) (sub (c aK) (k EK_KEY)),
    .mul (c sKEY) (sub (c bI) (.add kiE (k 1))), .mul (c sKEY) (sub (c bS) loE),
    .mul (c sKEY) (sub (c bK) (k EK_KEY)),
    .mul (.mul (c sKEY) (not (.mul (c fe) (c te)))) (sub (c bN) (c nid)),
    .mul (.mul (c sKEY) (not (.mul (c fe) (c te)))) (sub (c bJ) (.add kiE (k 2))),
    mul3 (c sKEY) (c fe) (.mul (c te) (sub (c bN) (c xtgt))),
    mul3 (c sKEY) (c fe) (.mul (c te) (sub (c bJ) (c xtgJ))),
    -- leaf key end marker (`LEND`) at `(nid, s)`
    .mul (c gL) (sub (c bI) sE), .mul (c gL) (sub (c bS) (k SYM_END)),
    .mul (c gL) (sub (c bN) (c nid)), .mul (c gL) (sub (c bJ) sE), .mul (c gL) (sub (c bK) (k EK_LEND)),
    -- odd first nibble
    .mul (.mul (c sHPF) (c odd)) (c aI), .mul (.mul (c sHPF) (c odd)) (sub (c aS) loE),
    .mul (.mul (c sHPF) (c odd)) (sub (c aK) (k EK_KEY)),
    .mul (mul3 (c sHPF) (c odd) (not (c xlast0))) (sub (c aN) (c nid)),
    .mul (mul3 (c sHPF) (c odd) (not (c xlast0))) (sub (c aJ) (k 1)),
    .mul (mul3 (c sHPF) (c odd) (c xlast0)) (sub (c aN) (c xtgt)),
    .mul (mul3 (c sHPF) (c odd) (c xlast0)) (sub (c aJ) (c xtgJ)),
    -- branch child
    .mul (.mul (c gP) isBr) (c aI), .mul (.mul (c gP) isBr) (sub (c aS) jIdxE),
    .mul (.mul (c gP) isBr) (sub (c aN) (c cres)), .mul (.mul (c gP) isBr) (c aJ),
    .mul (.mul (c gP) isBr) (sub (c aK) (k EK_DOWN)),
    -- value slot
    .mul valStart (sub (c aI) (.mul (c tl) sE)),
    .mul valStart (sub (c aS) (k SYM_END)),
    .mul valStart (sub (c aN) (c vid)),
    .mul valStart (c aJ),
    .mul valStart (sub (c aK) (k EK_VAL)) ]

def constraints : List Expr := cBool ++ cRows ++ cTrans ++ cFields ++ cBytes ++ cWindows ++ cLinks

/-! ## Interactions -/

def edgeA (u : Expr) : List Expr := [c nid, c aI, c aS, c aN, c aJ, c aK, u]
def edgeB (u : Expr) : List Expr := [c nid, c bI, c bS, c bN, c bJ, c bK, u]
def bmapMsg (u : Expr) : List Expr := [c nid, bmE, c tb2, u]
def entMsg (e : Expr) : List Expr := [e, c len, c pos, c b]
/-- `UPB (NPOST(nid), pos, pb, len, depth, cid, u)`: a post byte for `upsV3`, with the row's
window child id `cid` (free off windows) -/
def upbMsg (u : Expr) : List Expr := [mid K_NPOST (c nid), c pos, c pb, c len, c depth, c cid, u]

def interactions : List Interaction :=
  [ send B_BYTES (c act) [mid K_NPRE (c nid), c pos, c b],
    send B_BYTES (c act) [mid K_NPOST (c nid), c pos, c pb],
    recv B_DIGEST (c gD) ([c dI, c dL] ++ (List.range 32).map fun i => c (reg i)),
    recv B_DIGEST (c gDp) ([.add (c dI) (k 1), c dL] ++ (List.range 32).map fun i => c (preg i)),
    send B_PARENT (c gP) [c cid, c tau, .add (c depth) (k 1), c clen, c cres],
    recv B_PARENT (c nf) [c nid, c tau, c depth, c len, c res],
    send B_VPARENT valStart [c vid, c vlen],
    send B_EDGE (c gA) (edgeA (k 0)),
    recv B_EDGE (c gA) (edgeA (c mA)),
    send B_EDGE (c gB) (edgeB (k 0)),
    recv B_EDGE (c gB) (edgeB (c mB)),
    send B_BMAP (c gBm) (bmapMsg (k 0)),
    recv B_BMAP (c gBm) (bmapMsg (c mBm)),
    send B_DIGS (c gS) [c dE, c tau, c idx, c b],
    recv B_DUP (c gV) [mid K_NPRE (c nid), c repE],
    send B_ENT (c hd) (entMsg (mid K_NPRE (c nid))),
    recv B_ENT (c dup) (entMsg (c repE)),
    send B_SIZE (c sumr) [k 0, c sz],
    send B_UPB (c act) (upbMsg (k 0)),
    recv B_UPB (c act) (upbMsg (c mU)),
    recv B_VSLOT (.mul valStart (c tw)) [c vid] ]

/-- Height cap: `2^22` rows (unfolded node bytes `≤ 3,000,000` under A7, plus the `SUM` row). -/
def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.NodeV3
