import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.Ids

/-!
# ZkFormal.NearV3.Tables.Walk — `walkV3`: key walks with absent terminals

Lane `v3-trie`, V3-D0-DESIGN §3.2.4–5 as amended (§11, STATUS-V3-TRIE §3).  v1 `walk`
(`Near/Tables/Walk.lean`) plus instances, terminal kinds and drain rows.

One segment per walk `w` of instance `τ` over the key symbols received on
`KEYNIB (w, t, sym, last)` (the key's nibbles, then `END`; from `rcpt` for account /
access-key walks, from the fixed-key tables or the public bus for `[7]`, `[10]`, `[13]`,
`[15]`, `[16]‖s`).  Row modes (one-hot):

* `mS` — **step**: consume `sym` along an edge `EDGE (N, I, sym, N2, I2, ek, u)`
  (chained: receive `u`, send `u + 1`).  The first row (`ws`) is the `START` step from
  `(H, τ)` (the head segment `H` of instance `τ` provides `(H, τ) –START→ (root target, 0)`;
  only heads provide `START` edges); it reads no key symbol.  A non-final step uses an edge of kind `DOWN` or `KEY`; the final
  step (`we`, `sym = END`) uses an edge of kind `VAL` whose target `N2` is the value
  record: **terminal VAL**.
* `mK` — **absent by key** (`ABS_KEY`): at `(N, I)` an edge `(N, I, nib, …)` of kind `KEY`
  or `LEND` (a leaf/extension key nibble, or a leaf's key end) with `nib ≠ sym` (inverse
  `inv`).  Covers `extNib`, `leafNib`, `extLen`, `leafLen` of `AbsentWitness`.
* `mB` — **absent at a branch**: `BMAP (N, bm, hv, u)` (chained) at `I = 0`; for a nibble
  `sym < 16`, bit `sym` of `bm` is `0` (`brSlot`; one-hot `sel` over the 16 bits); at
  `END`, `hv = 0` (`brVal`).
* `mD` — **drain**: after an absent terminal, consume the remaining key symbols without a
  lookup.

The last row (`we`, `last = 1`, `sym = END`) sends `FINAL (w, τ, fk, k)`: `fk = 0`, `k = N2`
(the value record) for VAL; `fk = 1`, `k = 0` for absent.  No depth counter: `nodeV3`
bounds every record's depth by 399, which bounds `fdepth` (`pathsRevealed_of_rank`).
-/

namespace ZkFormal.NearV3.WalkV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

def act : Nat := 0
def ws : Nat := 1
def we : Nat := 2
def gK : Nat := 3
def w : Nat := 4
def tau : Nat := 5
def t : Nat := 6
def sym : Nat := 7
def nN : Nat := 8
def nI : Nat := 9
def nib : Nat := 10
def nN2 : Nat := 11
def nI2 : Nat := 12
def ek : Nat := 13
def u : Nat := 14
def mS : Nat := 15
def mK : Nat := 16
def mB : Nat := 17
def mD : Nat := 18
def inv : Nat := 19
def hv : Nat := 20
def ub : Nat := 21
def fk : Nat := 22
def kk : Nat := 23
def bmb (j : Nat) : Nat := 24 + j
def sel (j : Nat) : Nat := 40 + j
def width : Nat := 56

def bmE : Expr := bits (fun j => c (bmb j)) 0 16
def selIdx : Expr := sum ((List.range 16).map fun j => smul j (c (sel j)))
def selSum : Expr := sum ((List.range 16).map fun j => c (sel j))
def selBit : Expr := sum ((List.range 16).map fun j => .mul (c (sel j)) (c (bmb j)))
/-- absent modes -/
def absE : Expr := .add (c mK) (c mB)
def modes : List Nat := [mS, mK, mB, mD]

def boolCols : List Nat :=
  [act, ws, we, gK, mS, mK, mB, mD, hv] ++ (List.range 16).map bmb ++ (List.range 16).map sel

def constraints : List Expr :=
  boolCols.map (fun x => bool (c x)) ++
  [ sub (c gK) (sub (c act) (c ws)),
    sub (sum (modes.map c)) (c act),
    .mul (c ws) (not (c act)), .mul (c we) (not (c act)),
    .mul (c ws) (c we),
    -- a walk starts with the START step from (head, τ) at symbol index 0
    .mul (c ws) (not (c mS)),
    .mul (c ws) (sub (c nI) (c tau)), .mul (c ws) (sub (c sym) (k SYM_START)),
    .mul (c ws) (c t),
    .mul .isFirst (not (c ws)),
    .mul .isLast (.mul (c act) (not (c we))),
    -- inside a walk
    mul3 (c act) (not (c we)) (not (n act)),
    mul3 (c act) (not (c we)) (n ws),
    mul3 (c act) (not (c we)) (sub (n w) (c w)),
    mul3 (c act) (not (c we)) (sub (n tau) (c tau)),
    mul3 (c act) (not (c we)) (sub (n t) (.add (c t) (c gK))),
    -- a step leads to the next lookup position; after a step comes a step or an absent terminal
    mul3 (c mS) (not (c we)) (sub (n nN) (c nN2)),
    mul3 (c mS) (not (c we)) (sub (n nI) (c nI2)),
    mul3 (c mS) (not (c we)) (n mD),
    -- after an absent terminal or a drain row: drain
    .mul (.add absE (c mD)) (.mul (not (c we)) (not (n mD))),
    -- the key's last symbol is END
    .mul (c we) (sub (c sym) (k SYM_END)),
    -- step: the edge carries the symbol; kinds DOWN/KEY (non-final) or VAL (final)
    .mul (c mS) (sub (c nib) (c sym)),
    mul3 (c mS) (not (c we)) (.mul (c ek) (sub (c ek) (k 1))),
    mul3 (c mS) (c we) (sub (c ek) (k EK_VAL)),
    -- absent by key: a KEY or LEND edge with a different symbol
    .mul (c mK) (.mul (sub (c ek) (k EK_KEY)) (sub (c ek) (k EK_LEND))),
    .mul (c mK) (sub (.mul (sub (c sym) (c nib)) (c inv)) (k 1)),
    -- absent at a branch (position 0): END ⇒ no value; nibble ⇒ bit sym of bm is 0
    .mul (c mB) (c nI),
    mul3 (c mB) (c we) (c hv),
    sub selSum (.mul (c mB) (not (c we))),
    mul3 (c mB) (not (c we)) (sub selIdx (c sym)),
    selBit,
    -- FINAL contents (last row)
    .mul (c we) (sub (c fk) (.add absE (c mD))),
    .mul (c we) (sub (c kk) (.mul (c mS) (c nN2))),
    -- after a walk: another walk or padding
    mul3 (c we) (n act) (not (n ws)),
    mul3 .isTransition (not (c act)) (n act) ]

def edge (uu : Expr) : List Expr := [c nN, c nI, c nib, c nN2, c nI2, c ek, uu]
def bmap (uu : Expr) : List Expr := [c nN, bmE, c hv, uu]

def interactions : List Interaction :=
  [ recv B_KEYNIB (c gK) [c w, c t, c sym, c we],
    recv B_EDGE (.add (c mS) (c mK)) (edge (c u)),
    send B_EDGE (.add (c mS) (c mK)) (edge (.add (c u) (k 1))),
    recv B_BMAP (c mB) (bmap (c ub)),
    send B_BMAP (c mB) (bmap (.add (c ub) (k 1))),
    send B_FINAL (c we) [c w, c tau, c fk, c kk] ]

/-- `≤ 2·4481 + 64` walks of `≤ 1 + 2·66 + 1` rows (account keys `[0] ‖ id`, access keys
`[2] ‖ id ‖ [2] ‖ pk`: `≤ 1 + 2·(1 + 64 + 1 + 33) + 1 = 200` rows). -/
def maxLog : Nat := 21

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.WalkV3
