import ZkFormal.Near.Tables.Dsl

/-!
# ZkFormal.Near.Tables.Mrk — the outcome merkle tree (NEAR-AIR.md §3.5)

nearcore `merklize` over the outcome leaves `L_r = digest(LEAF(r))`: level
`0` = leaves (size `n`), level `j` has `s_j = ⌈s_{j−1}/2⌉` nodes; node `(j,i)`
is `sha256(node(j−1,2i) ‖ node(j−1,2i+1))`, except the last node of an odd
level, which is the promoted `node(j−1,2i)`; the first level of size 1 is the
root.  Positions are published on `MPOS (level, index, Id, len)` (leaves by
`rcpt`): a node *is* an SHA message id and its length.

Rows:
* row 0 (`rt`): the root check — receives `MPOS (J, 0, Id, len)` and looks up
  `(Id, len, outcome_root)` (public);
* then levels `1, 2, …` bottom-up, nodes left to right: a hashed node is a
  64-row segment (two 32-byte windows `left ‖ right`, each loaded into `reg` by
  the `DIGEST` lookup of the child received on `MPOS`) emitting message
  `MRK(q)` (`q` counts segments) and providing `MPOS (j, i, MRK(q), 64)`; a
  promoted node is one row forwarding the child's `MPOS` entry.
-/

namespace ZkFormal.Near.Mrk

open ZkFormal.Air ZkFormal.Near.Dsl

def rt : Nat := 0
def sg : Nat := 1
def pr : Nat := 2
def pw : Nat := 3
def wn : Nat := 4
def wf : Nat := 5
def wl : Nat := 6
def sf : Nat := 7
def sl : Nat := 8
def q : Nat := 9
def j : Nat := 10
def i : Nat := 11
def sp : Nat := 12
def s : Nat := 13
def odd : Nat := 14
def lil : Nat := 15
def top : Nat := 16
def inv : Nat := 17
def cId : Nat := 18
def cLen : Nat := 19
def mj : Nat := 20
def mi : Nat := 21
def oId : Nat := 22
def oLen : Nat := 23
def gM : Nat := 24
def gO : Nat := 25
def reg (x : Nat) : Nat := 26 + x
def width : Nat := 58

/-- node rows -/
def actE : Expr := .add (c sg) (c pr)
def nActE : Expr := .add (n sg) (n pr)
/-- last row of a node -/
def endE : Expr := .add (c sl) (c pr)
/-- `n` from the public claim bytes -/
def nPubE : Expr := sum ((List.range 4).map fun x => smul (256 ^ x) (.pub (PV_N + x)))

def nodeConst : List Nat := [q, j, i, sp, s, odd, lil, top, inv]

def constraints : List Expr :=
  [rt, sg, pr, wn, wf, wl, sf, sl, odd, lil, top, gM, gO].map (fun x => bool (c x)) ++
  [ -- row kinds
    .mul (c rt) actE, .mul (c sg) (c pr),
    sub (c rt) .isFirst,
    .mul .isLast actE,
    -- the root row is followed by the first node of level 1
    .mul (c rt) (not nActE), .mul (c rt) (sub (n j) (k 1)), .mul (c rt) (n i),
    .mul (c rt) (sub (n sp) nPubE), .mul (c rt) (n q),
    .mul (c rt) (.mul (n sg) (not (n sf))),
    -- segments: two 32-row windows
    .mul (c wf) (not (c sg)), .mul (c wl) (not (c sg)), .mul (c wf) (c pw),
    .mul (c wl) (sub (c pw) (k 31)),
    sub (c sf) (.mul (c wf) (not (c wn))), sub (c sl) (.mul (c wl) (c wn)),
    .mul (c pr) (c wn),
    mul3 (c sg) (not (c wl)) (not (n sg)),
    mul3 (c sg) (not (c wl)) (n wf),
    mul3 (c sg) (not (c wl)) (sub (n pw) (.add (c pw) (k 1))),
    mul3 (c sg) (not (c wl)) (sub (n wn) (c wn)),
    mul3 (c wl) (not (c wn)) (not (n sg)),
    mul3 (c wl) (not (c wn)) (not (n wf)),
    mul3 (c wl) (not (c wn)) (not (n wn)),
    -- next node: starts with a segment's first row or is a promote row
    .mul endE (.mul (n sg) (not (n sf))),
    -- level shape
    .mul actE (sub (.add (c sp) (c odd)) (smul 2 (c s))),
    .mul actE (sub (c pr) (.mul (c odd) (c lil))),
    .mul (c lil) (sub (.add (c i) (k 1)) (c s)),
    .mul (c top) (sub (c s) (k 1)),
    .mul actE (sub (.mul (sub (c s) (k 1)) (c inv)) (not (c top))),
    -- node succession
    .mul endE (.mul (not (c lil)) (not nActE)),
    .mul endE (.mul (not (c lil)) (sub (n j) (c j))),
    .mul endE (.mul (not (c lil)) (sub (n i) (.add (c i) (k 1)))),
    .mul endE (.mul (not (c lil)) (sub (n sp) (c sp))),
    .mul endE (.mul (c lil) (.mul (not (c top)) (not nActE))),
    .mul endE (.mul (c lil) (.mul (not (c top)) (sub (n j) (.add (c j) (k 1))))),
    .mul endE (.mul (c lil) (.mul (not (c top)) (n i))),
    .mul endE (.mul (c lil) (.mul (not (c top)) (sub (n sp) (c s)))),
    .mul endE (.mul (c lil) (.mul (c top) nActE)),
    .mul endE (.mul nActE (sub (n q) (.add (c q) (c sg)))),
    mul3 .isTransition (not (.add actE (c rt))) nActE,
    -- MPOS receive (window start, promote row, root row)
    sub (c gM) (.add (c wf) (.add (c pr) (c rt))),
    .mul (.add (c wf) (c pr)) (sub (.add (c mj) (k 1)) (c j)),
    .mul (.add (c wf) (c pr)) (sub (c mi) (.add (smul 2 (c i)) (c wn))),
    .mul (c rt) (c mi),
    -- MPOS send (segment first row, promote row)
    sub (c gO) (.add (c sf) (c pr)),
    .mul (c sf) (sub (c oId) (mid K_MRK (c q))), .mul (c sf) (sub (c oLen) (k 64)),
    .mul (c pr) (sub (c oId) (c cId)), .mul (c pr) (sub (c oLen) (c cLen)) ] ++
  nodeConst.map (fun x => mul3 (c sg) (not (c sl)) (sub (n x) (c x))) ++
  (List.range 31).map (fun x => mul3 (c sg) (not (c wl)) (sub (n (reg x)) (c (reg (x + 1)))))

def interactions : List Interaction :=
  [ send B_BYTES (c sg) [mid K_MRK (c q), .add (smul 32 (c wn)) (c pw), c (reg 0)],
    recv B_DIGEST (c wf) ([c cId, c cLen] ++ (List.range 32).map fun x => c (reg x)),
    recv B_DIGEST (c rt) ([c cId, c cLen] ++ (List.range 32).map fun x => .pub (PV_OUT + x)),
    recv B_MPOS (c gM) [c mj, c mi, c cId, c cLen],
    send B_MPOS (c gO) [c j, c i, c oId, c oLen] ]

/-- `1 + 64·255 + 8` rows. -/
def maxLog : Nat := 15

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.Near.Mrk
