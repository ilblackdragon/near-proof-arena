import ZkFormal.Near.Ids

/-!
# ZkFormal.NearV3.Ids — buses of the v3 trie tables (`nodeV3`, `walkV3`, `uniqV3`)

V3-D0-DESIGN §3.7 numbers v1's ten buses `0 … 9` and the v3 buses `10 … 18`; lane
`v3-trie` adds `19 … 23`.  SHA message kinds are v1's (`K_NPRE`, `K_NPOST`, `K_VPRE`,
`K_VPOST`); in v3 a value message `VPRE(vid)` / `VPOST(vid)` is indexed by the *value
record* id `vid` (a segment of `nodeV3`), not by the touched leaf.

| # | bus | message | producers → consumers |
|---|---|---|---|
| 10 | `ROOT` | `(τ, d[32])` | public `(0, pre)` / instance heads → heads / public `(K+1, post)` |
| 11 | `BMAP` | `(N, bm, hasVal, u)` | `nodeV3` branch (chained provider) ↔ `walkV3` absent terminals |
| 17 | `DIGS` | `(eid, τ, i, byte)` | `nodeV3` digest windows → `uniqV3` |
| 19 | `DUP` | `(eid, eid_prev)` | `uniqV3` (equal consecutive keys) → `nodeV3` duplicate entry |
| 20 | `ENT` | `(eid, len, pos, byte)` | `nodeV3` entry with a duplicate → `nodeV3` duplicate (byte copy) |
| 21 | `VBYTES` | `(vid, pos, byte)` | value parsers (`acct`, `akey`, `sched`, `qvals`, public) → `nodeV3` value record |
| 22 | `VPARENT` | `(vid, len)` | `nodeV3` value window → value record (permutation, tree-shaped) |
| 23 | `MEMD` | reserved (`upsV3`) | |
| 18 | `SIZE` | `(table, total)` | `nodeV3`/`valV3` → `size` |
| 24 | `MIDROOT` | `(τ, d[32])` | `headV3` (lockstep post-root) → `upsV3` |
-/

namespace ZkFormal.NearV3

def B_ROOT : Nat := 10
def B_BMAP : Nat := 11
def B_DIGS : Nat := 17
def B_DUP : Nat := 19
def B_ENT : Nat := 20
def B_VBYTES : Nat := 21
def B_VPARENT : Nat := 22
def B_MEMD : Nat := 23
def B_SIZE : Nat := 18
/-- `(τ, d[32])`: lockstep post-root of instance `τ` (head → `upsV3`, which applies the
`0x0f` upsert and sends `ROOT (τ+1, ·)`). -/
def B_MIDROOT : Nat := 24

/-- Edge kinds carried by `EDGE` in v3 (`walkV3` decides what a step may conclude). -/
def EK_DOWN : Nat := 0   -- branch child / START: descent only
def EK_KEY : Nat := 1    -- a key nibble of a leaf or extension (descent, or `ABS_KEY` witness)
def EK_VAL : Nat := 2    -- `END` into a revealed value (terminal `VAL`)
def EK_LEND : Nat := 3   -- `END` marker of a leaf whose value is not revealed (`ABS_KEY` only)

/-- `walkV3` terminal kinds (`FINAL (w, kind, k)`). -/
def FK_VAL : Nat := 0
def FK_ABS : Nat := 1

end ZkFormal.NearV3
