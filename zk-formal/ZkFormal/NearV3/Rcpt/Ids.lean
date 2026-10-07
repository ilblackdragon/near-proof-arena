import ZkFormal.NearV3.Ids

/-!
# ZkFormal.NearV3.Rcpt.Ids — buses, kinds, walk ids and public offsets of the receipt side

Lane `v3-rcpt` (`docs/zk-formal/STATUS-V3-RCPT.md`).  Tables: `rcptV3`, `acctV3`, `akeyV3`,
`bndV3`, `srcpV3`, `sizeV3`, `qvV3`, `mrkV3`, `sortV3`.

## Buses (new numbers only; v1 `0 … 9` and the trie lane's `10, 11, 17 … 25` are reused)

| # | bus | message | producers → consumers |
|---|---|---|---|
| 0 | `BYTES` | `(Id, pos, byte)` | as v1; **the refund body**: `rcptV3` sends `(K_RF, pos, byte)` for `pos ≥ 8` and the public bus receives `(K_RF, pos, B[pos])` (no SHA hashing of the body) |
| 3 | `VSLOT` | `(vid)` | `acctV3` (one per written account value) → `nodeV3` lockstep-written value windows (`tw`), **requested** from lane v3-trie |
| 5 | `KEYNIB` | `(w, t, sym, last)` | `rcptV3` (account walks `w = r`, access-key walks `w = W_AK + r`), `qvV3` (`w = W_QV + τ + 64·slot`) → `walkV3` |
| 6 | `FINAL` | `(w, τ, fk, k)` | `walkV3` → `rcptV3`, `qvV3` |
| 7 | `MEM` | `(vid, t, i, amt_i, locked_i, stor_i)` | `acctV3` ↔ `rcptV3` (v1 offline memory, slot = value record id) |
| 14 | `SRC` | `(j, dup, root[32])` | public (applied-order source lists) → `srcpV3` |
| 15 | `BND` | `(x, lo, hi, hn, u)` | `bndV3` (chained provider: sends `u = 0`, receives the final count) ↔ `rcptV3` routing lookups (receive `u`, send `u + 1`) |
| 16 | `SREC` | `(r, i, byte)` | `rcptV3` receiver rows → `rcptV3` signer rows (signer = receiver test) |
| 21 | `VBYTES` | `(vid, pos, byte)` | `acctV3`, `akeyV3`, `qvV3` → `valV3` |
| 26 | `RCL` | `(j, len)` | `rcptV3` (length of `RC(j)`) → `srcpV3` |
| 27 | `AKC` | `(vid, u)` | `akeyV3` (chained: sends `0`, receives the final count) ↔ `rcptV3` present access keys |
| 28 | `BNDP` | `(x, lo, hi, hn)` | public (own-shard routing intervals) → `bndV3` |
| 29 | `QSH` | `(τ, e, s_0 … s_7)` | `qvV3` `[13]` entries → `qvV3` `[16] ‖ u64 s` walks |
| 18 | `SIZE` | `(table, total)` | tables → `sizeV3` |

## SHA kinds (registry V3-D0-DESIGN §12)

`K_RC = 1` (`RC(j)`, idx `j`), `K_RF = 2` (body, **public, not hashed**), `K_PEO = 3`, `K_LEAF = 4`,
`K_RID = 5` (idx `r`), `K_MRK = 6`, `K_VPOST = 10` (idx `vid`), `K_SRC = 13` (idx: running
message counter of `srcpV3`).  `K_VAK = 14` is **not used**: access-key values are `valV3`
records (hashed as `VPRE(vid)`), so `akeyV3` only sends `VBYTES`.

## Public data (requirements on the prepared statement)

Static header fields are read with `.pub i` (`Prep.encode` = `borshBytes prepTag ‖ PrepHdr.encode
‖ …`, offsets below; `PH_BLEN` is **requested**: `u32 |B|` appended to the header).  The
variable-length data arrive as public messages on `SRC`, `BNDP` and `BYTES` (`(K_RF, pos, b)`);
each needs a record index or a position, so the assembly needs *indexed* public segments
(message = constant prefix ‖ `start + j` ‖ record) — requested from the bus lane.
-/

namespace ZkFormal.NearV3

/-! ## Buses -/

def B_SRC : Nat := 14
def B_BND : Nat := 15
def B_SREC : Nat := 16
def B_RCL : Nat := 26
def B_AKC : Nat := 27
def B_BNDP : Nat := 28
def B_QSH : Nat := 29

/-! ## SHA kinds -/

def K_SRC : Nat := 13

/-! ## Walk ids -/

/-- Access-key walk of receipt `r`: `W_AK + r` (`r < n ≤ 4481 < W_AK`). -/
def W_AK : Nat := 8192
/-- Fixed-key walks: `W_QV + τ + 64·slot` (`τ < 64`). -/
def W_QV : Nat := 16384

/-! ## Public header (offsets into `Prep.encode`) -/

/-- `u32 n` (number of applied receipts). -/
def PH_N : Nat := 30
/-- `u64` own shard id. -/
def PH_OWN : Nat := 34
/-- `u64` height of `B2`. -/
def PH_HEIGHT : Nat := 50
/-- `u128` gas price of the main application. -/
def PH_GP : Nat := 58
/-- `[32]` outcome root `H.prev_outcome_root`. -/
def PH_OUT : Nat := 146
/-- `u128` balance burnt `H.prev_balance_burnt`. -/
def PH_BURNT : Nat := 178
/-- `u32 |B|` (**requested**: appended to `PrepHdr.encode`). -/
def PH_BLEN : Nat := 194

/-! ## Routing records -/

/-- Positions per interval record block: boundary bytes `0 … 63` and the end marker `64`. -/
def BND_STRIDE : Nat := 65

end ZkFormal.NearV3
