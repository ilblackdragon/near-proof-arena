import ZkFormal.Near.Tables.Dsl

/-!
# ZkFormal.Near.Tables.Acct — touched value slots (NEAR-AIR.md §3.4)

One 16-row segment per touched slot `k` (the node id of the trie node holding
the value); lane `i = 0 … 15` holds byte `i` of `amount` (pre and post), of
`locked`, byte `i` of `storage_usage` (`i < 8`, else 0) and bytes `2i, 2i+1`
of `code_hash`.  It

* emits the AccountV1 value before (`VPRE(k)`) and after (`VPOST(k)`) the
  batch, 72 bytes each (`amount ‖ locked ‖ code_hash ‖ storage_usage`);
* opens slot `k`'s memory with the write `(k, 0, i, amount_i, locked_i, storage_i)`
  and closes it with the read `(k, tlast, i, post_i, locked_i, storage_i)` on `MEM`;
* offers the slot once on `VSLOT` (so touched nodes and segments correspond);
* checks AccountV1: the pre amount is not `u128::MAX` (`Σ (255 − amount_i) ≠ 0`).
-/

namespace ZkFormal.Near.Acct

open ZkFormal.Air ZkFormal.Near.Dsl

def act : Nat := 0
def af : Nat := 1
def al : Nat := 2
def kk : Nat := 3
def i : Nat := 4
def tlast : Nat := 5
def amt : Nat := 6
def post : Nat := 7
def lk : Nat := 8
def st : Nat := 9
def ch0 : Nat := 10
def ch1 : Nat := 11
def lo8 : Nat := 12
def dsum : Nat := 13
def inv : Nat := 14
def gS : Nat := 15
def width : Nat := 16

def constraints : List Expr :=
  [act, af, al, lo8, gS].map (fun x => bool (c x)) ++
  [ .mul (c af) (not (c act)), .mul (c al) (not (c act)),
    .mul .isFirst (not (c af)),
    .mul .isLast (.mul (c act) (not (c al))),
    .mul (c af) (c i), .mul (c al) (sub (c i) (k 15)),
    -- within a segment
    mul3 (c act) (not (c al)) (not (n act)),
    mul3 (c act) (not (c al)) (n af),
    mul3 (c act) (not (c al)) (sub (n kk) (c kk)),
    mul3 (c act) (not (c al)) (sub (n tlast) (c tlast)),
    mul3 (c act) (not (c al)) (sub (n i) (.add (c i) (k 1))),
    -- after a segment: another segment or padding
    mul3 (c al) (n act) (not (n af)),
    mul3 .isTransition (not (c act)) (n act),
    -- lanes below 8
    .mul (c af) (not (c lo8)), .mul (c al) (c lo8),
    .mul (mul3 (c act) (not (c al)) (n lo8)) (not (c lo8)),
    .mul (mul3 (c act) (c lo8) (not (n lo8))) (sub (c i) (k 7)),
    .mul (not (c lo8)) (c st),
    sub (c gS) (.mul (c act) (c lo8)),
    -- AccountV1: amount ≠ u128::MAX
    .mul (c af) (sub (c dsum) (sub (k 255) (c amt))),
    mul3 (c act) (not (c al)) (sub (n dsum) (.add (c dsum) (sub (k 255) (n amt)))),
    .mul (c al) (sub (.mul (c dsum) (c inv)) (k 1)) ]

def vbytes (kind : Nat) (a : Nat) : List Interaction :=
  let id := mid kind (c kk)
  [ send B_BYTES (c act) [id, c i, c a],
    send B_BYTES (c act) [id, .add (k 16) (c i), c lk],
    send B_BYTES (c act) [id, .add (k 32) (smul 2 (c i)), c ch0],
    send B_BYTES (c act) [id, .add (k 33) (smul 2 (c i)), c ch1],
    send B_BYTES (c gS) [id, .add (k 64) (c i), c st] ]

def interactions : List Interaction :=
  vbytes K_VPRE amt ++ vbytes K_VPOST post ++
  [ send B_MEM (c act) [c kk, k 0, c i, c amt, c lk, c st],
    recv B_MEM (c act) [c kk, c tlast, c i, c post, c lk, c st],
    send B_VSLOT (c af) [c kk] ]

/-- `≤ 256` touched slots × 16 rows. -/
def maxLog : Nat := 12

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.Near.Acct
