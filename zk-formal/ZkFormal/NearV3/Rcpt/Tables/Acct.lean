import ZkFormal.Near.Tables.Acct
import ZkFormal.NearV3.Rcpt.Ids

/-!
# ZkFormal.NearV3.Rcpt.Tables.Acct — `acctV3`: written account values

v1 `acct` (`Near/Tables/Acct.lean`, NEAR-AIR.md §3.4) with the v3 value interface: one 16-row
segment per touched account value record `kk = vid` (a `valV3` record, reached by the
receivers' account walks), lane `i = 0 … 15` holding byte `i` of `amount` (pre and post), of
`locked`, byte `i` of `storage_usage` (`i < 8`) and bytes `2i, 2i+1` of `code_hash`.  It

* sends the pre value to its value record on `VBYTES (vid, pos, b)` (72 bytes; v1 hashed them as
  `VPRE(k)` itself, in v3 `valV3` hashes the record's bytes);
* emits the post value as `BYTES (VPOST(vid), pos, b)` (72 bytes; `hpl`: the post value has the
  record's length, 72, because the pre value has exactly 72 `VBYTES` messages);
* opens and closes the value's memory on `MEM` (as v1);
* sends `VSLOT (vid)` once (v1 bus 3): consumed by the written value window (`tw`) of `nodeV3`,
  so that every written account value is a lockstep write and conversely (`hperm`; requested
  from lane v3-trie);
* checks AccountV1: the pre amount is not `u128::MAX`.

Only the interactions and `maxLog` differ from v1; the constraints are v1's verbatim.
-/

namespace ZkFormal.NearV3.AcctV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

export ZkFormal.Near.Acct (act af al kk i tlast amt post lk st ch0 ch1 lo8 dsum inv gS width
  constraints)

/-- The pre value on `VBYTES` (positions as v1's `VPRE` emission). -/
def vpre : List Interaction :=
  [ send B_VBYTES (c act) [c kk, c i, c amt],
    send B_VBYTES (c act) [c kk, .add (k 16) (c i), c lk],
    send B_VBYTES (c act) [c kk, .add (k 32) (smul 2 (c i)), c ch0],
    send B_VBYTES (c act) [c kk, .add (k 33) (smul 2 (c i)), c ch1],
    send B_VBYTES (c gS) [c kk, .add (k 64) (c i), c st] ]

def interactions : List Interaction :=
  vpre ++ ZkFormal.Near.Acct.vbytes K_VPOST post ++
  [ send B_MEM (c act) [c kk, k 0, c i, c amt, c lk, c st],
    recv B_MEM (c act) [c kk, c tlast, c i, c post, c lk, c st],
    send B_VSLOT (c af) [c kk] ]

/-- `≤ 4481` touched accounts × 16 rows (A1). -/
def maxLog : Nat := 17

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.AcctV3
