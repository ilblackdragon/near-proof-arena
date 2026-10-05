import ZkFormal.Near.Tables.Rcpt.Arith

/-!
# ZkFormal.Near.Tables.Rcpt — the receipt stream (NEAR-AIR.md §3.3)

One row per emitted byte.  Claim rows, then one segment per receipt (fields in
`Rcpt.Fields`), then padding.  Each row has up to three emissions on `BYTES`
(the byte goes to the receipts commitment `RC`, the receipt's outcome `PEO`,
its outcome leaf `LEAF`, its refund-id preimage `RID`, or the refunds
commitment `RF`, at positions computed from the running offsets `o`, `o2` and
the receipt's string lengths).  Arithmetic and account-id checks:
`Rcpt.Arith`.

Interactions: 3 × `BYTES` send; `DIGEST` receive (refund id `RID(r)` and
`H(PEO(r))` windows; `RC` and `RF` against the public commitments on the
batch's last row); `KEYNIB` send ×2 (the receiver's key symbols, `END` last);
`FINAL` receive (the receiver's slot); `MEM` read/write (balances); `RIDS`
send (ids, for `sort`); `MPOS` send (leaf `r` of the outcome tree).
-/

namespace ZkFormal.Near.Rcpt

open ZkFormal.Air ZkFormal.Near.Dsl

def constraints : List Expr :=
  cStates ++ cEmit ++ cRegs ++ cChars ++ cKey ++ cGas ++ cDep ++ cClaim ++ cEnd

def interactions : List Interaction :=
  (List.range 3).map (fun e => send B_BYTES (c (eG e)) [c (eId e), c (ePos e), c (eV e)]) ++
  [ recv B_DIGEST (c gDg) ([c dI, c dL] ++ (List.range 32).map fun j => c (reg j)),
    recv B_DIGEST (c lastR) ([k K_RC, c oEnd] ++ pubs PV_RC 32),
    recv B_DIGEST (c lastR) ([k K_RF, c o2End] ++ pubs PV_RFC 32),
    send B_KEYNIB (c gKA) [c r, c tA, c symA, c lastA],
    send B_KEYNIB (c sV) [c r, .add (k 3) (smul 2 (c idx)), loE, k 0],
    recv B_FINAL (c rf) [c r, c kslot],
    recv B_MEM (c sDEP) [c kslot, c tprev, c idx, c bef, c lk, c st],
    send B_MEM (c sDEP) [c kslot, .add (c r) (k 1), c idx, aftE, c lk, c st],
    send B_RIDS (c sRID) [c r, c idx, c b],
    send B_MPOS (c rf) [k 0, c r, mid K_LEAF (c r), k 68] ]

/-- `12 + 256 · (≤ 500)` rows. -/
def maxLog : Nat := 18

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.Near.Rcpt
