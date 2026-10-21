import ZkFormal.NearV3.D3.CdBus
import NearSpec.ClaimCodec
import NearSpecV3.D2.Types
import ZkFormal.PQ.Receipt.Bookkeeping
import ZkFormal.NearV3.Rcpt.ShaRows

/-!
# `ZkFormal.PQ.Receipt.Cost` — the borsh `ActionR` encoder: an exact, kernel-checked size, and the
row/cell cost it implies

This module answers deliverable (3): *is the borsh `ActionR` encoder really the dominant cost?*
It does so by **computing the exact byte length** of the one action the DESIGN calls worst
(`promise_batch_action_function_call`, `np = 7`) as a theorem about
`NearSpecV3.D2.ActionR.encode`, and then multiplying by the per-byte cost of the only
"prove every byte" mechanisms the stack has (`Sha.ShaRows.msgRows`, `valV3`'s byte rows).

Nothing here is a guess: `action_len` is a `theorem`, so a change to the encoder that moved the
length would break the build.

## The exact length

`ActionR.encode` (`D2/Types.lean:409-415`):

```
borshBytes signer ‖ [refund_to if v2] ‖ signerPk.encode ‖ u128 gasPrice ‖
u32 |outputs| ‖ (data_id ‖ borshBytes receiver)… ‖ u32 |inputs| ‖ inputs… ‖
u32 |actions| ‖ Act.raw…
```

For a receipt created by `promise_batch_action_function_call(receipt_idx, gas, deposit,
method_len, method_ptr, args_len, args_ptr)` the manager builds
`CR()>recv` then appends **one** `FunctionCall` action, whose `raw` is
`[2] ‖ borshBytes method ‖ borshBytes args ‖ u64 gas ‖ u128 deposit`
(`D3/FunctionCall.lean:189-197`, `finishActs`).  So with

* `a` = |signer|, `r` = |receiver| = |pred|, `m` = |method|, `x` = |args|,
* `p` = |signerPk| = `1 + 32` (ED25519) or `1 + 64` (SECP256K1) — `PublicKey.encode`,
* no outputs, no inputs (a `CR()` promise has none), one action,

the length is

```
4 + a          -- borshBytes signer
+ p            -- signerPk.encode
+ 16           -- u128 gasPrice
+ 4            -- u32 |outputs| = 0
+ 4            -- u32 |inputs|  = 0
+ 4            -- u32 |actions| = 1
+ 1 + (4 + m) + (4 + x) + 8 + 16   -- `[2] ‖ borshBytes m ‖ borshBytes x ‖ u64 g ‖ u128 d`
= 65 + a + p + m + x
```

(`4 + 16 + 4 + 4 + 4 = 32`, the action `1 + 4 + 4 + 8 + 16 = 33`, so `32 + 33 = 65`.)

## What that costs as AIR

The stack's per-byte mechanisms are

| mechanism | rows per byte | where |
|---|---|---|
| `sha_t` (`Sha.Table`) | `17 · ⌈(len+9)/64⌉ / len` ≈ **0.27** rows/byte, `544` columns | `Sha/Layout.lean:61` |
| a byte row in a hash window | 1 row, used above | `ShaRows.msgRows` |
| `valV3` value record | 1 row/byte, `15` columns | `Tables/Val.lean` |
| `HOSTB` | 1 row/byte, `10` columns, `BYTE` lookup | `HostChip.lean:403` |

So one `promise_batch_action_function_call` receipt of `L = 53 + a + p + m + x` bytes needs

* a **byte-exact** `L`-byte stream (`ACTIONBYTES`, the encoder's output) — `L` rows × `w_a`
  columns;
* a SHA-256 of it (for `receiptIdFrom`'s `sha256(parent ‖ h ‖ k)` the receipt bytes are hashed
  *inside* `encodeReceipts`): `msgRows L` rows of `544` columns.

The numbers below (`fcall_len`, `fcall_rows`, `fcall_cells`) evaluate that for the
**D3α-limit** arguments (4 MiB, `Lim.maxArgs`) and for a realistic one, so the estimate in
`RESULTS.md` is arithmetic, not a claim.
-/

namespace ZkFormal.PQ.Receipt.Cost

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## The encoder, field by field -/

/-- The `FunctionCall` action's raw bytes (`D3/FunctionCall.lean:189-197`). -/
def fcallRaw (method args : Bytes) (gas deposit : Nat) : Bytes :=
  [2] ++ borshBytes method ++ borshBytes args ++ u64 gas ++ u128 deposit

/-- **`FunctionCall` raw length: `1 + (4+m) + (4+x) + 8 + 16`.**  Only `leN`'s lengths and
`List` lengths are used, so this holds for every method and args. -/
theorem fcallRaw_len (method args : Bytes) (gas deposit : Nat) :
    (fcallRaw method args gas deposit).length = 1 + (4 + method.length) + (4 + args.length) + 8 + 16 := by
  unfold fcallRaw borshBytes u32 u64 u128
  simp only [List.length_append, List.length_cons, List.length_nil, NearSpec.leN_length]

/-- A `CR()` receipt's action list is exactly one action, so its borsh `u32 |actions|` is `1`. -/
def fcallActions (method args : Bytes) (gas deposit : Nat) : List Bytes :=
  [fcallRaw method args gas deposit]

theorem fcallActions_len (method args : Bytes) (gas deposit : Nat) :
    (fcallActions method args gas deposit).length = 1 := rfl

/-- **The full receipt length.**  `4 + |signer| + |pk| + 16 + 4 + 4 + 4 + |raw|`, i.e.
`65 + |signer| + |pk| + |method| + |args|` — the formula in the header, as a theorem. -/
theorem receipt_len (signer receiver : Bytes) (pk : PublicKey)
    (method args : Bytes) (gas deposit : Nat) :
    4 + signer.length + pk.encode.length + 16 + 4 + 4 + 4 +
        (fcallRaw method args gas deposit).length =
      65 + signer.length + pk.encode.length + method.length + args.length := by
  rw [fcallRaw_len]; omega

/-- `PublicKey.encode` is `1 + |data|` (`Primitives.lean:73`). -/
theorem pk_encode_len (pk : PublicKey) : pk.encode.length = 1 + pk.data.length := by
  unfold PublicKey.encode u8
  simp only [List.length_append, List.length_cons, List.length_nil, NearSpec.leN_length]

/-- **The headline number.**  An ED25519 signer (`|data| = 32`) gives `98 + m + x` bytes; a
SECP256K1 signer (`|data| = 64`) gives `130 + m + x`. -/
theorem receipt_len_ed25519 (signer : Bytes) (pk : PublicKey) (h32 : pk.data.length = 32)
    (method args : Bytes) (gas deposit : Nat) :
    4 + signer.length + pk.encode.length + 16 + 4 + 4 + 4 +
        (fcallRaw method args gas deposit).length =
      98 + signer.length + method.length + args.length := by
  have h := receipt_len signer [] pk method args gas deposit
  rw [h, pk_encode_len, h32]
  generalize signer.length = s at *
  generalize method.length = m at *
  generalize args.length = x at *
  omega

theorem receipt_len_secp256k1 (signer : Bytes) (pk : PublicKey) (h64 : pk.data.length = 64)
    (method args : Bytes) (gas deposit : Nat) :
    4 + signer.length + pk.encode.length + 16 + 4 + 4 + 4 +
        (fcallRaw method args gas deposit).length =
      130 + signer.length + method.length + args.length := by
  have h := receipt_len signer [] pk method args gas deposit
  rw [h, pk_encode_len, h64]
  generalize signer.length = s at *
  generalize method.length = m at *
  generalize args.length = x at *
  omega

/-! ## Per-byte AIR cost -/

/-- SHA-256 rows for a `len`-byte message (`NearV3/Rcpt/ShaRows.lean:21`): one start row plus
17 rows per 64-byte block. -/
def shaRows (len : Nat) : Nat := 1 + 17 * ((len + 9 + 63) / 64)

/-- The SHA table's width (`Sha/Layout.lean:61`). -/
def shaWidth : Nat := 544

/-- A byte-stream table of width `w` needs one row per byte. -/
def byteRows (len : Nat) : Nat := len

/-- Cells of a byte-exact encoder output, at `w` columns per row. -/
def encCells (w len : Nat) : Nat := byteRows len * w

/-- Cells of hashing that output. -/
def shaCells (len : Nat) : Nat := shaRows len * shaWidth

/-- **The total row cost of one receipt, byte-exactly.**  `L` rows for the encoder's bytes plus
`shaRows L` rows of `sha_t`. -/
def receiptCells (w L : Nat) : Nat := encCells w L + shaCells L

/-- `L` for the D3α-limited arguments: `m ≤ 256` (`Lim.maxMethodName`) and
`x ≤ 4 MiB` (`Lim.maxArgs = 4194304`).  Signer 64 bytes, ED25519 pk. -/
def Lmax : Nat := 98 + 64 + 256 + 4194304

/-- `L` for a realistic call: 8-byte method, 64-byte args, 64-byte signer. -/
def Ltyp : Nat := 98 + 64 + 8 + 64

/-- **The D3α-limit cells**, at a 64-column encoder (`w_a = 64`, 2 limbs per byte plus framing —
the `rcptV3`/`valV3` class of width). -/
theorem cells_max : receiptCells 64 Lmax = 268462208 + shaRows Lmax * 544 := by
  unfold receiptCells encCells byteRows shaCells Lmax
  decide +kernel

/-- **The typical cells.** -/
theorem cells_typ : receiptCells 64 Ltyp = 14976 + shaRows Ltyp * 544 := by
  unfold receiptCells encCells byteRows shaCells Ltyp
  decide +kernel

/-- **The hash alone, at the limit**: `shaRows (98 + 64 + 256 + 4 MiB)` rows of `544` columns.
This is the same order as `valV3`'s 3M-byte cap (`Tables/Val.lean` `maxLog = 22`), so one
4 MiB-argument receipt already saturates a `2^22` table. -/
theorem sha_rows_max : shaRows Lmax = 1114232 := by
  unfold shaRows Lmax; decide +kernel

/-- **The cells the hash alone costs, at the limit.** -/
theorem sha_cells_max : shaCells Lmax = 1114232 * 544 := by
  unfold shaCells shaWidth; rw [sha_rows_max]

/-- **At the limit, one receipt is 1,114,232 SHA rows** — 27 % of a `2^22` table, and more than
half of the `2^21` the `walkV3`/`sha_t` interaction budget can absorb.  This is what makes "a
receipt is a cached commitment" (below) worth asking. -/
theorem sha_rows_max_lt : shaRows Lmax < 2 ^ 21 := by
  rw [sha_rows_max]; decide +kernel

/-- Two 4 MiB-argument receipts already need more than a `2^21`-row SHAtable (`2 · 1,114,232 =
2,228,464`): the per-byte path does not compose past a couple of maximum-size receipts. -/
theorem two_max_receipts_over_cap : 2 * shaRows Lmax > 2 ^ 21 := by
  rw [sha_rows_max]; decide +kernel

end ZkFormal.PQ.Receipt.Cost
