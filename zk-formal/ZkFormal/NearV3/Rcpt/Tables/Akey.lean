import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.Rcpt.Ids

/-!
# ZkFormal.NearV3.Rcpt.Tables.Akey — `akeyV3`: present access keys of gas refunds

`applySystemReceipt` reads `AccessKey{receiver, pk}` for a gas refund (`signer = receiver`) and
requires it absent or `FullAccess` without gas-key info: the value is 9 bytes
(`nonce: u64 ‖ permission tag`) and its last byte is `1`.

One 9-row segment per access-key value record `vid` (a `valV3` record reached by an access-key
walk of `rcptV3` with terminal `VAL`).  Row `pos = 0 … 8` sends byte `pos` of the value on
`VBYTES (vid, pos, b)` (so the record has exactly these 9 bytes); the last byte is `1`.  The
segment is a chained provider of `AKC (vid, u)` (first row: sends `u = 0`, receives the final
count `U`): every access-key walk of `rcptV3` that ends at `vid` receives `u` and sends `u + 1`.
Several gas refunds may read the same key.
-/

namespace ZkFormal.NearV3.AkeyV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

def act : Nat := 0
def af : Nat := 1
def al : Nat := 2
def vid : Nat := 3
def pos : Nat := 4
def b : Nat := 5
def uu : Nat := 6
def width : Nat := 7

def constraints : List Expr :=
  [act, af, al].map (fun x => bool (c x)) ++
  [ .mul (c af) (not (c act)), .mul (c al) (not (c act)),
    .mul .isFirst (sub (c act) (c af)),
    .mul .isLast (.mul (c act) (not (c al))),
    .mul (c af) (c pos),
    .mul (c al) (sub (c pos) (k 8)),
    -- FullAccess: the permission tag (last byte) is 1
    .mul (c al) (sub (c b) (k 1)),
    -- within a segment
    mul3 (c act) (not (c al)) (not (n act)),
    mul3 (c act) (not (c al)) (n af),
    mul3 (c act) (not (c al)) (sub (n vid) (c vid)),
    mul3 (c act) (not (c al)) (sub (n pos) (.add (c pos) (k 1))),
    -- after a segment: another segment or padding
    mul3 (c al) (n act) (not (n af)),
    mul3 .isTransition (not (c act)) (n act) ]

def interactions : List Interaction :=
  [ send B_VBYTES (c act) [c vid, c pos, c b],
    send B_AKC (c af) [c vid, k 0],
    recv B_AKC (c af) [c vid, c uu] ]

/-- `≤ 4481` access keys × 9 rows (A1). -/
def maxLog : Nat := 16

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.AkeyV3
