import ZkFormal.NearV3.Rcpt.Tables.Rcpt.Arith

/-!
# ZkFormal.NearV3.Rcpt.Tables.Rcpt — `rcptV3`: the applied receipts

v1's `rcpt` (`Near/Tables/Rcpt.lean`, NEAR-AIR.md §3.3) for `NearSpecV3.applyReceipts`
(V3-D0-DESIGN §3.4): one row per emitted byte; per applied source list `j` a 12-row header
then its receipts (one segment each, v1's fields); then padding.

Interactions:
* 3 × `BYTES` send: `RC(j)` (the list `u64 own ‖ u32 n_j ‖ Σ borsh(receipt)`, consumed by
  `srcpV3`), `PEO(r)`, `LEAF(r)`, `RID(r)` (as v1), and the refund body `(K_RF, pos, byte)`,
  `pos ≥ 8`, received by the public bus (`B`, positions pinned by `|B|`);
* `DIGEST` receive (refund id and `H(PEO(r))`, as v1);
* `KEYNIB` send × 2 (slots A / B): the account walk `r` (`[0] ‖ receiver`) and, for a gas
  refund of a system receipt, the access-key walk `W_AK + r` (`[2] ‖ signer ‖ [2] ‖ pk`);
* `FINAL` receive: account walk → value record `kslot` (`VAL`); access-key walk → absent or
  `kF` (`VAL`);
* `MEM` read / write (balances of value record `kslot`, as v1);
* `RIDS` send (ids, for `sortV3`); `MPOS` send (outcome leaf `r`, for `mrkV3`);
* `RCL (j, |RC(j)|)` send (last row of list `j`, for `srcpV3`);
* `SREC` send / receive (signer = receiver test);
* `AKC` receive / send (present access key `kF`, chained through `akeyV3`);
* `BND` receive / send (routing lookups, chained through `bndV3`).
-/

namespace ZkFormal.NearV3.RcptV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

def constraints : List Expr :=
  cStates ++ cEmit ++ cRegs ++ cChars ++ cKey ++ cSys ++ cRoute ++ cGas ++ cDep ++ cEnd

def bndMsg (u : Expr) : List Expr :=
  [.add (smul BND_STRIDE (c q)) (c iB), c loB, c hiB, c hnB, u]

def interactions : List Interaction :=
  (List.range 3).map (fun e => send B_BYTES (c (eG e)) [c (eId e), c (ePos e), c (eV e)]) ++
  [ recv B_DIGEST (c gDg) ([c dI, c dL] ++ (List.range 32).map fun i => c (reg i)),
    send B_KEYNIB (c gKA) [wE, c tA, c symA, c lastA],
    send B_KEYNIB (c gKB) [wE, c tB, c symB, k 0],
    recv B_FINAL (c gF) [.add (c r) (smul W_AK (c sT0)), k 0, c fkF, c kF],
    recv B_MEM (c sDEP) [c kslot, c tprev, c idx, c bef, c lk, c st],
    send B_MEM (c sDEP) [c kslot, .add (c r) (k 1), c idx, ZkFormal.Near.Rcpt.aftE, c lk, c st],
    send B_RIDS (c sRID) [c r, c idx, c b],
    send B_MPOS (c rf) [k 0, c r, mid K_LEAF (c r), k 68],
    send B_RCL (c le) [c j, c oEnd],
    send B_SREC (c gV) [c r, c idx, c b],
    recv B_SREC (c gS) [c r, c idx, c sx],
    recv B_AKC (c gAK) [c kF, c uak],
    send B_AKC (c gAK) [c kF, .add (c uak) (k 1)],
    recv B_BND (c gBd) (bndMsg (c uB)),
    send B_BND (c gBd) (bndMsg (.add (c uB) (k 1))) ]

/-- `≤ 1984` list headers × 12 + `≤ 4481` receipts (A1) × `≤ 474` rows `< 2^22`. -/
def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.RcptV3
