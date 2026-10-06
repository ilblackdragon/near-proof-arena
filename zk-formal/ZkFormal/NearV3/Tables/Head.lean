import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.Ids

/-!
# ZkFormal.NearV3.Tables.Head — `headV3`: one 32-row head per instance `τ`

Lane `v3-trie`.  A head is the virtual parent of instance `τ`'s root record `rid`: a 32-row
digest window holding the pre-root `reg` and the lockstep post-root `preg` (shift registers,
loaded by the root's `DIGEST` lookups on the first row).  It
* receives `ROOT (τ, pre)` (from the public bus for `τ = 0`, from `upsV3` of `τ − 1`) and
  sends `MIDROOT (τ, post)` (to `upsV3` of `τ`, which applies the `0x0f` upsert);
* sends `PARENT (rid, τ, 0, rlen, rres)`: the root is a record of instance `τ` at depth 0;
* provides the walks' `START` edge `(0, τ) –START→ (rres, 0)` (chained, kind `DOWN`);
* sends the root entry's digest to `uniqV3`: `DIGS (NPRE(rid), τ, i, reg[0])` on row `i`.
-/

namespace ZkFormal.NearV3.HeadV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

def act : Nat := 0
def hf : Nat := 1
def hl : Nat := 2
def tau : Nat := 3
def rid : Nat := 4
def rlen : Nat := 5
def rres : Nat := 6
def i : Nat := 7
def mE : Nat := 8
def reg (j : Nat) : Nat := 9 + j
def preg (j : Nat) : Nat := 41 + j
def width : Nat := 73

def headConst : List Nat := [tau, rid, rlen, rres]

def constraints : List Expr :=
  [act, hf, hl].map (fun x => bool (c x)) ++
  [ .mul (c hf) (not (c act)), .mul (c hl) (not (c act)),
    .mul .isFirst (not (c hf)),
    .mul .isLast (.mul (c act) (not (c hl))),
    .mul (c hf) (c i), .mul (c hl) (sub (c i) (k 31)),
    -- within a head
    mul3 (c act) (not (c hl)) (not (n act)),
    mul3 (c act) (not (c hl)) (n hf),
    mul3 (c act) (not (c hl)) (sub (n i) (.add (c i) (k 1))) ] ++
  headConst.map (fun x => mul3 (c act) (not (c hl)) (sub (n x) (c x))) ++
  (List.range 31).flatMap (fun j =>
    [ mul3 (c act) (not (c hl)) (sub (n (reg j)) (c (reg (j + 1)))),
      mul3 (c act) (not (c hl)) (sub (n (preg j)) (c (preg (j + 1)))) ]) ++
  [ -- next head or padding
    mul3 (c hl) (n act) (not (n hf)),
    mul3 .isTransition (not (c act)) (n act) ]

def regs : List Expr := (List.range 32).map fun j => c (reg j)
def pregs : List Expr := (List.range 32).map fun j => c (preg j)
def startEdge (u : Expr) : List Expr := [k 0, c tau, k SYM_START, c rres, k 0, k EK_DOWN, u]

def interactions : List Interaction :=
  [ recv B_DIGEST (c hf) ([mid K_NPRE (c rid), c rlen] ++ regs),
    recv B_DIGEST (c hf) ([mid K_NPOST (c rid), c rlen] ++ pregs),
    recv B_ROOT (c hf) ([c tau] ++ regs),
    send B_MIDROOT (c hf) ([c tau] ++ pregs),
    send B_PARENT (c hf) [c rid, c tau, k 0, c rlen, c rres],
    send B_EDGE (c hf) (startEdge (k 0)),
    recv B_EDGE (c hf) (startEdge (c mE)),
    send B_DIGS (c act) [mid K_NPRE (c rid), c tau, c i, c (reg 0)] ]

/-- `≤ 33` instances × 32 rows. -/
def maxLog : Nat := 11

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.HeadV3
