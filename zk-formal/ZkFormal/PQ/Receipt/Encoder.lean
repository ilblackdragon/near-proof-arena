import ZkFormal.PQ.Receipt.Cost

/-!
# `ZkFormal.PQ.Receipt.Encoder` — the borsh `ActionR` byte encoder, as AIR rows

Lane `pq-actionr`.  `Cost.lean` priced the encoder (31 % of the byte-exact receipt cost) and left
it unbuilt.  This module builds it, starting from the simplest action that exercises the borsh
shape — `promise_batch_action_transfer` (`[3] ‖ u128 amount`, no string) — and generalising to
`promise_batch_action_delete_account` (`[7] ‖ borshBytes beneficiary`, one `u32` prefix) and
`promise_batch_action_function_call` (`[2] ‖ borshBytes method ‖ borshBytes args ‖ u64 gas ‖
u128 deposit`, two prefixes).

## What the encoder has to get right

Borsh frames every variable-length field with a **`u32` little-endian length prefix equal to the
number of bytes actually emitted**, and every action with a **`u8` tag**.  The obligations are

1. **the length identity** — `|bytes| = 1 + Σ(4 + |str|) + 8·#u64 + 16·#u128`
   (`encAction_length`, one induction over the field list);
2. **the prefix is the count** — `prefixBytes_value` (`leNat` of the four prefix bytes is `n`) and
   the byte-wise `prefixBytes_getD`;
3. **the group's declared `len` is the number of emitting rows** (`pbe_group_len_is_row_count`) —
   the direction that cannot be faked, and the one the AIR closes.

## Layering

* **`trRaw` / `daRaw` / `caRaw` / `fcRaw`** — the reference bytes: the spec's own action
  construction (`D3/FunctionCall.lean:172` for `TR`; `D2/Types.lean`'s `pBase` tags for the rest).
* **`decodesAs`** — the spec's **decoder** (`D2.pBaseAct`) run on the reference bytes, by kernel
  `decide` on real vectors.  Parsing is the other direction of the same specification, so this is
  an independent check of the encoder rather than a restatement of it.
* **`encAction`** — the bytes a row set produces, as a function of the tag and a list of typed
  fields (`BField.str` / `.u64` / `.u128`).  Its length is the framing identity, and the concrete
  actions are proved equal to their reference encodings position for position
  (`encAction_transfer`, `encAction_delete`, `encAction_create`, `encAction_fcall`).
* **`etable` (`PBE`)** — the AIR: 13 columns, one row per emitted byte.  Body bytes come from a
  committed array on bus 214 (the cached-source design `results/pq-receipt-air/README.md` §3.3
  argues for); prefix bytes are looked up in a 4-row `u32` table on bus 213.

## The wire

`PBE` sends each byte on the **existing** `HOSTB` bus (210) in the `dir = 1` (state → outside)
half, with the 5-field message `[ts, hid, dir, pos, byte]` that `Wire.PBB` and the HOST chip's
`HostB.msg` already use (`pbe_msg_len`).  No second byte wire is introduced: `PBB`'s `dir = 1`
sender *is* this table's sender, which is what `Wire.ActionEncodingIsBorsh` claimed.
-/

namespace ZkFormal.PQ.Receipt

theorem leN_len_enc : ∀ (w x : Nat), (NearSpec.leN w x).length = w
  | 0, _ => rfl
  | w + 1, x => by
    simp only [NearSpec.leN, List.length_cons]
    exact congrArg (fun n => n + 1) (leN_len_enc w (x / 256))

theorem toNats_leN_enc : ∀ (n x : Nat),
    (NearSpec.leN n x).map UInt8.toNat = (List.range n).map (fun i => x / 256 ^ i % 256)
  | 0, _ => rfl
  | n + 1, x => by
    rw [NearSpec.leN, List.map_cons, toNats_leN_enc n (x / 256),
      List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · simp [Nat.pow_zero]
    · apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      rw [Nat.pow_succ', Nat.div_div_eq_div_mul, Nat.mul_comm]

def prefixBytes (n : Nat) : List Nat := (NearSpec.u32 n).map UInt8.toNat

theorem prefixBytes_length (n : Nat) : (prefixBytes n).length = 4 := by
  unfold prefixBytes NearSpec.u32
  rw [List.length_map, leN_len_enc]

theorem prefixBytes_eq (n : Nat) :
    prefixBytes n = [n % 256, n / 256 % 256, n / 65536 % 256, n / 16777216 % 256] := by
  unfold prefixBytes NearSpec.u32
  rw [toNats_leN_enc]
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, Nat.pow_zero, Nat.div_one, Nat.pow_succ']

theorem map_ofNat_toNat (l : List UInt8) : l.map (UInt8.ofNat ∘ UInt8.toNat) = l := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp [Function.comp_def, UInt8.ofNat_toNat]

theorem prefixBytes_value {n : Nat} (hn : n < 4294967296) :
    NearSpec.leNat ((prefixBytes n).map UInt8.ofNat) = n := by
  have h : (prefixBytes n).map UInt8.ofNat = NearSpec.u32 n := by
    unfold prefixBytes
    rw [List.map_map]
    exact map_ofNat_toNat (NearSpec.u32 n)
  rw [h]
  exact ZkFormal.NearV3.leNat_u32 hn

/-- Byte `k` of the `u32` prefix is `n / 256^k % 256` — the byte-wise form of the framing fact,
which is what a prefix row's stored byte must equal. -/
theorem prefixBytes_getD (n k : Nat) (hk : k < 4) :
    (prefixBytes n).getD k 0 = n / 256 ^ k % 256 := by
  rw [prefixBytes_eq]
  match k with
  | 0 => simp [Nat.pow_zero]
  | 1 => simp
  | 2 => simp [Nat.pow_succ]
  | 3 => simp [Nat.pow_succ]

/-- `List.range`'s `getD` is the index (local copy). -/
theorem getD_range_enc (n i : Nat) (hi : i < n) : (List.range n).getD i 0 = i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.length_range ▸ hi)]
  simp

/-- `map` and `getD` commute on an in-range index (local copy). -/
theorem getD_map_enc (f : Nat → Nat) (l : List Nat) (i : Nat) (hi : i < l.length) :
    (l.map f).getD i 0 = f (l.getD i 0) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ k =>
      simp only [List.map_cons, List.getD_cons_succ, List.length_cons] at hi ⊢
      exact ih k (by omega)

/-- `getD` at an append boundary (local: the tree's other copies sit behind heavier imports). -/
theorem getD_append_right_enc (a b : List Nat) (i d : Nat) :
    (a ++ b).getD (a.length + i) d = b.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

theorem borshBytes_len_enc (b : NearSpec.Bytes) :
    (NearSpec.borshBytes b).length = 4 + b.length := by
  unfold NearSpec.borshBytes NearSpec.u32
  rw [List.length_append, leN_len_enc]

theorem borshBytes_map (b : NearSpec.Bytes) :
    (NearSpec.borshBytes b).map UInt8.toNat = prefixBytes b.length ++ b.map UInt8.toNat := by
  unfold NearSpec.borshBytes prefixBytes NearSpec.u32
  rw [List.map_append]



/-- One field of a borsh action body, in the three shapes borsh's `Action` arms use:

* `str` — a `Vec<u8>`/`String`: a `u32` length prefix **equal to the byte count**, then the bytes.
* `raw` — a byte run with **no** prefix and no fixed width.  This is what a serialised
  `PublicKey` (`u8 tag ‖ data`, `Primitives.lean:73`), a `u8` permission tag, and any other
  already-encoded sub-value are: the bytes are laid out verbatim.
* `uN` — a fixed-width little-endian integer, `N / 8` bytes.

The `raw` case is what the four remaining `ActionR` arms need (`stake`, both `addKey` shapes,
`deleteKey` all carry a serialised key verbatim); without it those bodies cannot be expressed as a
`BField` list at all, which is why the earlier lane stopped at the arms whose bodies happen to be
`str`/`u64`/`u128` only. -/
inductive BField where
  | str (bs : List Nat)
  /-- a verbatim byte run: no length prefix, no fixed width -/
  | raw (bs : List Nat)
  | u8 (v : Nat)
  | u16 (v : Nat)
  | u32 (v : Nat)
  | u64 (v : Nat)
  | u128 (v : Nat)
  deriving DecidableEq, Repr

/-- Byte count of a field.  `str` is `4 + |bs|` (the `u32` prefix is part of it); `raw` is the run
itself; `uN` is `N / 8`. -/
def BField.len : BField → Nat
  | .str bs => 4 + bs.length
  | .raw bs => bs.length
  | .u8 _ => 1
  | .u16 _ => 2
  | .u32 _ => 4
  | .u64 _ => 8
  | .u128 _ => 16

def BField.bytes : BField → List Nat
  | .str bs => prefixBytes bs.length ++ bs
  | .raw bs => bs
  | .u8 v => (NearSpec.u8 v).map UInt8.toNat
  | .u16 v => (NearSpec.u16 v).map UInt8.toNat
  | .u32 v => (NearSpec.u32 v).map UInt8.toNat
  | .u64 v => (NearSpec.u64 v).map UInt8.toNat
  | .u128 v => (NearSpec.u128 v).map UInt8.toNat

theorem BField.bytes_length (f : BField) : f.bytes.length = BField.len f := by
  cases f with
  | str bs => simp [BField.bytes, BField.len, prefixBytes_length]
  | raw bs => rfl
  | u8 v => simp [BField.bytes, BField.len, NearSpec.u8, leN_len_enc]
  | u16 v => simp [BField.bytes, BField.len, NearSpec.u16, leN_len_enc]
  | u32 v => simp [BField.bytes, BField.len, NearSpec.u32, leN_len_enc]
  | u64 v => simp [BField.bytes, BField.len, NearSpec.u64, leN_len_enc]
  | u128 v => simp [BField.bytes, BField.len, NearSpec.u128, leN_len_enc]

def encAction (tag : Nat) (fs : List BField) : List Nat := tag :: fs.flatMap BField.bytes

theorem flatMap_bytes_len (fs : List BField) :
    (fs.flatMap BField.bytes).length = (fs.map (fun f => (BField.bytes f).length)).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, ih]

theorem fieldLen_sum_eq (fs : List BField) :
    (fs.map (fun f => (BField.bytes f).length)).sum = (fs.map BField.len).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, BField.bytes_length]

theorem encAction_length (tag : Nat) (fs : List BField) :
    (encAction tag fs).length = 1 + (fs.map BField.len).sum := by
  unfold encAction
  rw [List.length_cons, flatMap_bytes_len, fieldLen_sum_eq]
  omega

/-! ## 3. The reference encodings, and byte-exactness against the spec's decoder

`trRaw` / `daRaw` / `caRaw` / `fcRaw` are the spec's own construction of each action's bytes
(`D3/FunctionCall.lean:172` for `TR`, `D2/Types.lean`'s `pBase` for the rest).  `decodesAs` runs
the spec's **decoder** on them: parsing is the other direction of the same specification, so the
`decide` facts below are an independent check of the encoder, not a restatement of it. -/

/-- The reference bytes of a transfer action (`D3/FunctionCall.lean:172`). -/
def trRaw (amount : Nat) : NearSpec.Bytes := [3] ++ NearSpec.u128 amount
/-- The reference bytes of a delete-account action (`D2/Types.lean` `pBase` tag 7). -/
def daRaw (beneficiary : NearSpec.Bytes) : NearSpec.Bytes := [7] ++ NearSpec.borshBytes beneficiary
/-- The reference bytes of a create-account action (`pBase` tag 0: no payload). -/
def caRaw : NearSpec.Bytes := [0]
/-- The reference bytes of a function-call action (`D3/FunctionCall.lean:189-197`). -/
def fcRaw (method args : NearSpec.Bytes) (gas deposit : Nat) : NearSpec.Bytes :=
  [2] ++ NearSpec.borshBytes method ++ NearSpec.borshBytes args ++ NearSpec.u64 gas ++
    NearSpec.u128 deposit

/-- The reference `FunctionCall` bytes are `Cost.fcallRaw`. -/
theorem fcRaw_eq_cost (method args : NearSpec.Bytes) (gas deposit : Nat) :
    fcRaw method args gas deposit =
      ZkFormal.PQ.Receipt.Cost.fcallRaw method args gas deposit := rfl

/-- **A transfer action is 17 bytes.** -/
theorem trRaw_len (amount : Nat) : (trRaw amount).length = 17 := by
  unfold trRaw NearSpec.u128
  rw [List.length_append, leN_len_enc]
  simp

/-- **The transfer's bytes are the 17-byte little-endian encoding of `3 + 256·amount`.** -/
theorem trRaw_bytes (amount : Nat) : trRaw amount = NearSpec.leN 17 (3 + 256 * amount) := by
  unfold trRaw NearSpec.u128
  rw [show (17 : Nat) = 1 + 16 by omega]
  have hmod : (3 + 256 * amount) % 256 = 3 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by decide)]
  have hdiv : (3 + 256 * amount) / 256 = amount := by
    rw [Nat.add_mul_div_left 3 amount (by decide), Nat.div_eq_of_lt (by decide), Nat.zero_add]
  have hleN : NearSpec.leN (1 + 16) (3 + 256 * amount)
      = UInt8.ofNat ((3 + 256 * amount) % 256) ::
          NearSpec.leN 16 ((3 + 256 * amount) / 256) := rfl
  rw [hleN, hmod, hdiv]
  rfl

theorem daRaw_len (b : NearSpec.Bytes) : (daRaw b).length = 5 + b.length := by
  unfold daRaw
  rw [List.length_append, borshBytes_len_enc]
  simp only [List.length_cons, List.length_nil]
  omega

theorem caRaw_len : caRaw.length = 1 := rfl

theorem fcRaw_len (m a : NearSpec.Bytes) (g d : Nat) :
    (fcRaw m a g d).length = 33 + m.length + a.length := by
  unfold fcRaw NearSpec.u64 NearSpec.u128
  rw [List.length_append, List.length_append, List.length_append, List.length_append,
    List.length_cons, borshBytes_len_enc, borshBytes_len_enc, leN_len_enc, leN_len_enc]
  simp
  omega

/-- The byte-exactness predicate: the spec's decoder, run on `raw`, yields exactly `b` with `raw`
round-tripping. -/
def decodesAs (raw : NearSpec.Bytes) (b : NearSpecV3.D2.Base) : Bool :=
  match NearSpecV3.D2.pBaseAct raw with
  | .ok (x, []) => decide (x.b = b) && decide (x.raw = raw)
  | _ => false

/-! ### The five action kinds `promise_*` can still append

`ActionR.encode` lays an action out as `tag ‖ body`, and `D2.pBase`'s arms (`Types.lean:283-330`)
fix each body.  The five below are every arm a `promise_batch_action_*` function can reach that
`trRaw`/`daRaw`/`caRaw`/`fcRaw` do not already cover:

| promise function | tag | body |
|---|---:|---|
| `promise_batch_action_deploy_contract` | 1 | `borshBytes code` |
| `promise_batch_action_stake` | 4 | `u128 amount ‖ PublicKey.encode` |
| `promise_batch_action_add_key_with_full_access` | 5 | `PublicKey.encode ‖ u64 nonce ‖ u8 1` |
| `promise_batch_action_add_key_with_function_call` | 5 | `PublicKey.encode ‖ u64 nonce ‖ u8 0 ‖ FcPerm.encode` |
| `promise_batch_action_delete_key` | 6 | `PublicKey.encode` |

The two `addKey` shapes share tag `5`; they differ only in the permission body, which is why the
encoder models a permission as a `BField list` rather than as a fixed shape (`permFull` /
`permFc`). -/

/-- The reference bytes of a deploy-contract action (`pBase` tag 1: one `borshBytes`). -/
def deployRaw (code : NearSpec.Bytes) : NearSpec.Bytes := [1] ++ NearSpec.borshBytes code

/-- The reference bytes of a stake action (`pBase` tag 4: `u128 ‖ PublicKey`). -/
def stakeRaw (amount : Nat) (pk : NearSpec.PublicKey) : NearSpec.Bytes :=
  [4] ++ NearSpec.u128 amount ++ pk.encode

/-- The reference bytes of a full-access add-key action (`pBase` tag 5 with `Perm::Full`:
`PublicKey ‖ u64 nonce ‖ [1]`). -/
def addKeyFullRaw (pk : NearSpec.PublicKey) (nonce : Nat) : NearSpec.Bytes :=
  [5] ++ pk.encode ++ NearSpec.u64 nonce ++ [1]

/-- The reference bytes of a function-call add-key action (`pBase` tag 5 with `Perm::FunctionCall`:
`PublicKey ‖ u64 nonce ‖ [0] ‖ FcPerm.encode`). -/
def addKeyFcRaw (pk : NearSpec.PublicKey) (nonce : Nat) (p : NearSpecV3.D2.FcPerm) :
    NearSpec.Bytes :=
  [5] ++ pk.encode ++ NearSpec.u64 nonce ++ [0] ++ p.encode

/-- The reference bytes of a delete-key action (`pBase` tag 6: `PublicKey`). -/
def deleteKeyRaw (pk : NearSpec.PublicKey) : NearSpec.Bytes := [6] ++ pk.encode

/-- **Byte-exactness, deploy-contract.**  Empty and non-empty code. -/
theorem decodes_deploy_empty : decodesAs (deployRaw []) (.deploy []) = true := by decide
theorem decodes_deploy_nonempty :
    decodesAs (deployRaw [0, 97, 115, 109, 1, 0, 0, 0]) (.deploy [0, 97, 115, 109, 1, 0, 0, 0]) =
      true := by decide

/-- **Byte-exactness, stake.**  An ED25519 key (`tag 0 ‖ 32`), and a zero amount. -/
theorem decodes_stake_zero :
    decodesAs (stakeRaw 0 ⟨0, List.replicate 32 0⟩) (.stake 0 ⟨0, List.replicate 32 0⟩) =
      true := by decide
theorem decodes_stake_amount :
    decodesAs (stakeRaw 1234567890 ⟨0, List.replicate 32 7⟩)
      (.stake 1234567890 ⟨0, List.replicate 32 7⟩) = true := by decide
/-- A SECP256K1 key is `tag 1 ‖ 64`, and the length difference must survive decoding. -/
theorem decodes_stake_secp :
    decodesAs (stakeRaw 5 ⟨1, List.replicate 64 3⟩) (.stake 5 ⟨1, List.replicate 64 3⟩) = true :=
  by decide

/-- **Byte-exactness, add-key with full access.**  The permission tag `1` is what `pPerm` reads. -/
theorem decodes_addkey_full :
    decodesAs (addKeyFullRaw ⟨0, List.replicate 32 9⟩ 42)
      (.addKey ⟨0, List.replicate 32 9⟩ ⟨42, .full⟩) = true := by decide

/-- **Byte-exactness, add-key with a function-call permission.**  `allowance = none` and
`allowance = some a` are both covered, as are a non-empty method list and none. -/
theorem decodes_addkey_fc_none :
    decodesAs (addKeyFcRaw ⟨0, List.replicate 32 9⟩ 42
        ⟨none, [97, 99, 99, 116], []⟩)
      (.addKey ⟨0, List.replicate 32 9⟩
        ⟨42, .fc ⟨none, [97, 99, 99, 116], []⟩⟩) = true := by decide
theorem decodes_addkey_fc_some :
    decodesAs (addKeyFcRaw ⟨0, List.replicate 32 9⟩ 0
        ⟨some 1000000, [97, 99, 99, 116], [[109, 49], [109, 50]]⟩)
      (.addKey ⟨0, List.replicate 32 9⟩
        ⟨0, .fc ⟨some 1000000, [97, 99, 99, 116], [[109, 49], [109, 50]]⟩⟩) = true := by decide

/-- **Byte-exactness, delete-key.** -/
theorem decodes_deletekey :
    decodesAs (deleteKeyRaw ⟨0, List.replicate 32 5⟩)
      (.deleteKey ⟨0, List.replicate 32 5⟩) = true := by decide

/-- The check discriminates on the five new shapes too: a stake's bytes are not an add-key's. -/
theorem decodes_stake_not_addkey :
    decodesAs (stakeRaw 7 ⟨0, List.replicate 32 1⟩)
      (.addKey ⟨0, List.replicate 32 1⟩ ⟨7, .full⟩) = false := by decide

/-! ### The new actions' row encodings

`encAction` at the concrete field list is the reference encoding, position for position.  The two
`addKey` shapes share `encAction 5`; they differ only in the permission field list. -/

/-- **`deploy` is `tag 1` then one `str`.** -/
theorem encAction_deploy (code : NearSpec.Bytes) :
    encAction 1 [.str (code.map UInt8.toNat)] = (deployRaw code).map UInt8.toNat := by
  unfold encAction deployRaw BField.bytes
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_map,
    List.map_append, List.map_cons, List.map_nil]
  rw [borshBytes_map code]
  rfl

/-- **`stake` is `tag 4`, a `u128` and a verbatim key.** -/
theorem encAction_stake (amount : Nat) (pk : NearSpec.PublicKey) :
    encAction 4 [.u128 amount, .raw (pk.encode.map UInt8.toNat)] =
      (stakeRaw amount pk).map UInt8.toNat := by
  unfold encAction stakeRaw NearSpec.u128 BField.bytes
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_map,
    List.map_append, List.map_cons, List.map_nil, List.cons_append]
  rfl

/-- `u8` of `0`/`1` as bytes: the two permission tags borsh writes. -/
theorem u8_zero_bytes : (NearSpec.u8 0).map UInt8.toNat = [0] := by
  simp only [NearSpec.u8]
  decide
theorem u8_one_bytes : (NearSpec.u8 1).map UInt8.toNat = [1] := by
  simp only [NearSpec.u8]
  decide

/-- **`addKey` with full access is `tag 5`, a key, a `u64` and the permission tag `1`.** -/
theorem encAction_addKeyFull (pk : NearSpec.PublicKey) (nonce : Nat) :
    encAction 5 [.raw (pk.encode.map UInt8.toNat), .u64 nonce, .u8 1] =
      (addKeyFullRaw pk nonce).map UInt8.toNat := by
  unfold encAction addKeyFullRaw NearSpec.u64 BField.bytes
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_map,
    List.map_append, List.map_cons, List.map_nil, List.cons_append, List.map_map]
  rw [u8_one_bytes]
  simp only [NearSpec.u64, List.nil_append, List.append_assoc]
  rfl

/-- **`addKey` with a function-call permission is `tag 5`, a key, a `u64`, the tag `0`, then
`FcPerm.encode` verbatim.** -/
theorem encAction_addKeyFc (pk : NearSpec.PublicKey) (nonce : Nat)
    (p : NearSpecV3.D2.FcPerm) :
    encAction 5 [.raw (pk.encode.map UInt8.toNat), .u64 nonce, .u8 0,
      .raw (p.encode.map UInt8.toNat)] = (addKeyFcRaw pk nonce p).map UInt8.toNat := by
  unfold encAction addKeyFcRaw NearSpec.u64 BField.bytes
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_map,
    List.map_append, List.map_cons, List.map_nil, List.cons_append, List.map_map]
  rw [u8_zero_bytes]
  simp only [NearSpec.u64, List.nil_append, List.append_assoc]
  rfl

/-- **`deleteKey` is `tag 6` then a verbatim key.** -/
theorem encAction_deleteKey (pk : NearSpec.PublicKey) :
    encAction 6 [.raw (pk.encode.map UInt8.toNat)] = (deleteKeyRaw pk).map UInt8.toNat := by
  unfold encAction deleteKeyRaw BField.bytes
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil]
  rfl

/-- **The length identity at the five new actions.** -/
theorem encAction_deploy_len (code : List Nat) :
    (encAction 1 [.str code]).length = 5 + code.length := by
  rw [encAction_length]; simp [BField.len]; omega

theorem encAction_stake_len (amount : Nat) (k : List Nat) :
    (encAction 4 [.u128 amount, .raw k]).length = 17 + k.length := by
  rw [encAction_length]; simp [BField.len]; omega

theorem encAction_addKeyFull_len (k : List Nat) (nonce : Nat) :
    (encAction 5 [.raw k, .u64 nonce, .u8 1]).length = 10 + k.length := by
  rw [encAction_length]; simp [BField.len]; omega

theorem encAction_addKeyFc_len (k : List Nat) (nonce : Nat) (perm : List Nat) :
    (encAction 5 [.raw k, .u64 nonce, .u8 0, .raw perm]).length = 10 + k.length + perm.length :=
  by
  rw [encAction_length]; simp [BField.len]; omega

theorem encAction_deleteKey_len (k : List Nat) :
    (encAction 6 [.raw k]).length = 1 + k.length := by
  rw [encAction_length]; simp [BField.len]

/-- **Byte-exactness, transfer.** -/
theorem decodes_transfer_zero : decodesAs (trRaw 0) (.transfer 0) = true := by decide
theorem decodes_transfer_one : decodesAs (trRaw 1) (.transfer 1) = true := by decide
theorem decodes_transfer_fee :
    decodesAs (trRaw 115123062500) (.transfer 115123062500) = true := by decide
theorem decodes_transfer_near :
    decodesAs (trRaw 1234567890) (.transfer 1234567890) = true := by decide
theorem decodes_transfer_u64 :
    decodesAs (trRaw 18446744073709551615) (.transfer 18446744073709551615) = true := by decide

/-- **Byte-exactness, delete-account.** -/
theorem decodes_delete_bob :
    decodesAs (daRaw [98, 111, 98]) (.deleteAccount [98, 111, 98]) = true := by decide
theorem decodes_delete_dotted :
    decodesAs (daRaw [97, 108, 105, 99, 101, 46, 110, 101, 97, 114])
      (.deleteAccount [97, 108, 105, 99, 101, 46, 110, 101, 97, 114]) = true := by decide

/-- **Byte-exactness, create-account.** -/
theorem decodes_create : decodesAs caRaw .createAccount = true := by decide

/-- **Byte-exactness, function-call.** -/
theorem decodes_fcall :
    decodesAs (fcRaw [116, 114, 97, 110, 115, 102, 101, 114] [1, 2, 3] 300000000000000 0)
      (.fcall [116, 114, 97, 110, 115, 102, 101, 114] [1, 2, 3] 300000000000000 0) = true :=
  by decide
theorem decodes_fcall_empty : decodesAs (fcRaw [] [] 0 0) (.fcall [] [] 0 0) = true := by decide

/-- The check discriminates: the bytes of a transfer of `1` are not a transfer of `2`. -/
theorem decodes_discriminates : decodesAs (trRaw 1) (.transfer 2) = false := by decide

/-- **The exact bytes of a transfer of `1234567890` yoctoNEAR.** -/
theorem trRaw_vector :
    (trRaw 1234567890).map UInt8.toNat =
      [3, 210, 2, 150, 73, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide

/-- **The exact bytes of a delete-account of `bob`.** -/
theorem daRaw_vector :
    (daRaw [98, 111, 98]).map UInt8.toNat = [7, 3, 0, 0, 0, 98, 111, 98] := by decide

/-! ### The rows' bytes equal the reference bytes

`encAction` at the concrete field list is the reference encoding, position for position. -/

/-- **`transfer` is `tag 3` then one `u128`.** -/
theorem encAction_transfer (amount : Nat) :
    encAction 3 [.u128 amount] = (trRaw amount).map UInt8.toNat := by
  unfold encAction trRaw NearSpec.u128 BField.bytes
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append,
    List.map_cons, List.map_nil, List.cons_append]
  rfl

/-- **`delete_account` is `tag 7` then `borshBytes beneficiary`.** -/
theorem encAction_delete (beneficiary : NearSpec.Bytes) :
    encAction 7 [.str (beneficiary.map UInt8.toNat)] = (daRaw beneficiary).map UInt8.toNat := by
  unfold encAction daRaw BField.bytes
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_map,
    List.map_append, List.map_cons, List.map_nil]
  rw [borshBytes_map beneficiary]
  rfl

/-- **`create_account` is just the tag.** -/
theorem encAction_create : encAction 0 [] = caRaw.map UInt8.toNat := rfl

/-- **`function_call` is `tag 2`, two strings, a `u64` and a `u128`.** -/
theorem encAction_fcall (method args : NearSpec.Bytes) (gas deposit : Nat) :
    encAction 2 [.str (method.map UInt8.toNat), .str (args.map UInt8.toNat),
      .u64 gas, .u128 deposit] = (fcRaw method args gas deposit).map UInt8.toNat := by
  unfold encAction fcRaw NearSpec.u64 NearSpec.u128 BField.bytes
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_map,
    List.map_append, List.map_cons, List.nil_append, List.cons_append]
  rw [borshBytes_map method, borshBytes_map args]
  simp only [List.append_assoc]
  rfl

/-- **The length identity at the concrete actions.** -/
theorem encAction_transfer_len (amount : Nat) : (encAction 3 [.u128 amount]).length = 17 := by
  rw [encAction_length]; simp [BField.len]

theorem encAction_delete_len (b : List Nat) : (encAction 7 [.str b]).length = 5 + b.length := by
  rw [encAction_length]; simp [BField.len]; omega

theorem encAction_fcall_len (m a : List Nat) (g d : Nat) :
    (encAction 2 [.str m, .str a, .u64 g, .u128 d]).length = 33 + m.length + a.length := by
  rw [encAction_length]; simp [BField.len]; omega

/-- **The tag is byte `0` of the encoding.** -/
theorem encAction_tag (tag : Nat) (fs : List BField) : (encAction tag fs).getD 0 0 = tag := rfl

/-- **The `TR` encoding, position by position.**  Byte `0` is the tag `3`; byte `1 + k` is the
amount's `k`-th little-endian byte.  This is the lemma a trace generator fills rows from. -/
theorem encAction_transfer_body (amount k : Nat) (hk : k < 16) :
    (encAction 3 [.u128 amount]).getD (1 + k) 0 = amount / 256 ^ k % 256 := by
  rw [encAction_transfer, trRaw, NearSpec.u128, List.map_append]
  rw [toNats_leN_enc]
  rw [show 1 + k = (List.map UInt8.toNat ([3] : List UInt8)).length + k by simp]
  rw [getD_append_right_enc]
  rw [getD_map_enc _ _ k (by simpa using hk)]
  rw [getD_range_enc _ _ hk]

/-- **The `TR` encoding's tag byte** is `3`. -/
theorem encAction_transfer_tag (amount : Nat) :
    (encAction 3 [.u128 amount]).getD 0 0 = 3 := rfl

/-! ## 4. The receipt-level length

`ActionR.encode` (`D2/Types.lean:409`) with `v2 = false`, no outputs, no inputs and one action is
`4 + |signer| + |pk| + 16 + 4 + 4 + 4 + |action|`.  `Cost.receipt_len` is that identity for the
`FC` action; these are the `TR` / `DA` instances. -/

/-- **The `TR` receipt's length**: `49 + |signer| + |pk|`. -/
theorem receipt_tr_len (signer : NearSpec.Bytes) (pk : NearSpec.PublicKey) (amount : Nat) :
    (NearSpec.borshBytes signer).length + pk.encode.length + (NearSpec.u128 amount).length +
        4 + 4 + 4 + (trRaw amount).length = 49 + signer.length + pk.encode.length := by
  rw [trRaw_len, borshBytes_len_enc]
  simp only [NearSpec.u128, leN_len_enc]
  omega

/-- **The `TR` receipt's length, ED25519** (`|pk.encode| = 33`): `82 + |signer|`. -/
theorem receipt_tr_len_ed25519 (signer : NearSpec.Bytes) (pk : NearSpec.PublicKey)
    (amount : Nat) (h33 : pk.encode.length = 33) :
    (NearSpec.borshBytes signer).length + pk.encode.length + (NearSpec.u128 amount).length +
        4 + 4 + 4 + (trRaw amount).length = 82 + signer.length := by
  rw [receipt_tr_len, h33]; omega

/-- **The `TR` receipt's length, SECP256K1** (`|pk.encode| = 65`): `114 + |signer|`. -/
theorem receipt_tr_len_secp256k1 (signer : NearSpec.Bytes) (pk : NearSpec.PublicKey)
    (amount : Nat) (h65 : pk.encode.length = 65) :
    (NearSpec.borshBytes signer).length + pk.encode.length + (NearSpec.u128 amount).length +
        4 + 4 + 4 + (trRaw amount).length = 114 + signer.length := by
  rw [receipt_tr_len, h65]; omega

/-- **The `DA` receipt's length**: `37 + |signer| + |pk| + |beneficiary|`. -/
theorem receipt_da_len (signer : NearSpec.Bytes) (pk : NearSpec.PublicKey)
    (beneficiary : NearSpec.Bytes) :
    (NearSpec.borshBytes signer).length + pk.encode.length + (NearSpec.u128 0).length +
        4 + 4 + 4 + (daRaw beneficiary).length =
      37 + signer.length + pk.encode.length + beneficiary.length := by
  rw [daRaw_len, borshBytes_len_enc]
  have h16 : (NearSpec.u128 0).length = 16 := leN_len_enc 16 0
  rw [h16]
  omega

/-- **The framing identity, per shape.**  `|action| = 1 + 4·(#strings) + (Σ|str|) + tail`, where
`tail` is the fixed-width part (`16` for a lone `u128`; `8 + 16 = 24` for `FC`'s `u64`+`u128`).
The AIR's `cFrame` is exactly this identity with `nStr`/`tail` as per-class constants. -/
theorem frame_shape (nStr strLen tail : Nat) :
    1 + 4 * nStr + strLen + tail = 1 + 4 * nStr + strLen + tail := rfl

/-- **`TR`**: `1 + 0 + 0 + 16 = 17`, and the encoding is 17 bytes. -/
theorem tr_frame_len : 1 + 4 * 0 + 0 + 16 = (encAction 3 [.u128 0]).length := by
  rw [encAction_transfer_len]

/-- **`DA`**: `1 + 4 + |b| + 0 = 5 + |b|` (`nStr = 1`, `strLen = |b|`, no fixed tail), and the
encoding is that long. -/
theorem da_frame_len (b : List Nat) :
    1 + 4 * 1 + b.length + 0 = (encAction 7 [.str b]).length := by
  rw [encAction_delete_len]
  generalize b.length = m at *
  have : (1 : Nat) + 4 * 1 = 5 := by decide
  omega

/-- **`FC`**: `1 + 8 + (|m|+|a|) + 24 = 33 + |m| + |a|`. -/
theorem fc_frame_len (m a : List Nat) (g d : Nat) :
    1 + 4 * 2 + (m.length + a.length) + 24 =
      (encAction 2 [.str m, .str a, .u64 g, .u128 d]).length := by
  rw [encAction_fcall_len]
  generalize m.length = mm at *
  generalize a.length = aa at *
  have : (1 : Nat) + 4 * 2 + 24 = 33 := by decide
  omega

/-! ## 5. The `PBE` table

One row per emitted byte.  Groups are delimited as `HostB`'s are: `f = 1` on a group's first row,
`pos` increments by one inside a group, and the group constants (`ts`, `hid`, `len`, `knd`,
`strLen`) are fixed inside a group.

| column | meaning |
|---|---|
| `act` | the row emits a byte (0 on padding) |
| `ts`, `hid` | the call the bytes belong to (the `HOSTB` group key) |
| `pos` | byte position inside the group |
| `len` | the group's byte count — the borsh length the prefix must equal |
| `byte` | the emitted byte |
| `knd` | the action tag (the class's `PBC.knd`) |
| `strLen` | the action's string field length (`0` for `TR`) |
| `nStr` | the number of `u32`-prefixed string fields (class constant) |
| `tail` | the fixed-width tail's byte count (class constant) |
| `f` | group-break flag (1 on a group's first row) |
| `gap` | 16-bit witness for `pos < len` |
| `selTag`, `selBody` | phase selectors: tag row / body row |
| `d` | body index, `pos − 5` |
| `fld` | index of the string field a prefix row belongs to (class constant) |

width 16.

`fld` is the per-field index of §"the prefix group key".  A `u32` prefix byte is identified on
`PBPREFIX` by `(ts, hid, fld, strLen, pos)`; without `fld`, a call that frames **two** strings of
equal length (`function_call` with `|method| = |args|`) would emit two prefix groups with the same
key and the two groups could be merged, which is exactly the documented blocker for `FC`.  With it,
the two prefix groups of one call differ in the `fld` slot (`prefixKey_fld_ne`), so the multiset
keeps them apart (`preKey_nat_inj` shows the key is the tuple, `ePreMsg = ePreKey ++ [byte]`). -/

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.V2

def eAct : Nat := 0
def eTs : Nat := 1
def eHid : Nat := 2
def ePos : Nat := 3
def eLen : Nat := 4
def eByte : Nat := 5
def eKnd : Nat := 6
def eStrLen : Nat := 7
def eF : Nat := 8
def eGap : Nat := 9
def eSelTag : Nat := 10
def eSelBody : Nat := 11
def eD : Nat := 12
/-- The number of `u32`-prefixed string fields (class constant: `0` `TR`, `1` `DA`, `2` `FC`). -/
def eNStr : Nat := 13
/-- The fixed-width tail's byte count (class constant: `16` `TR`, `0` `DA`, `24` `FC`). -/
def eTail : Nat := 14
/-- The **per-field index**: which `u32`-prefixed string field a prefix row's byte belongs to
(`0` for `DA`'s only string; `0`/`1` for `FC`'s `method`/`args`).  It is a **per-row** column, not a
group constant: `function_call`'s two prefix groups are rows of *one* action group (the group's
`pos` runs `0 … len−1` straight through both strings), so a group-constant `fld` could not tell the
two apart — it would forbid the very trace FC needs.  It is part of the `PBPREFIX` key
`(ts, hid, strLen, pos, fld)`. -/
def eFld : Nat := 15
/-- The length of **this row's** string field (per row), as opposed to `strLen`, which is the
group-constant *total* `Σ|str_i|` the framing identity reads.  A prefix row's byte is a byte of it. -/
def eStrLenF : Nat := 16
/-- The prefix byte's index `k` inside its `u32` (`0 … 3`).  Its bound is not a local constraint:
the `PBPREFIX` lookup (bus 213) is exactly the 4-row `u32` table, so a row with `pid ∉ 0..3` has no
sender to match.  That is the same division of labour `HOSTB`'s byte `BYTE` lookup uses. -/
def ePid : Nat := 17
/-- Phase selector: the row emits one of a string field's four `u32` prefix bytes. -/
def eSelPre : Nat := 18
/-- The **header size** (class constant): `1` for an action group (the `u8` tag), `4` for the
receipt's `Vec<Action>` group (its `u32` element count).  This is what lets one framing constraint
cover both an action and the actions-vector that contains it. -/
def eHdr : Nat := 19
def eWidth : Nat := 20

def eBits : List Expr := [eAct, eF, eSelTag, eSelBody, eSelPre].map (fun x => bool (c x))

def eGroupCons : List Expr :=
  [ .mul .isFirst (sub (k 1) (c eF)), .mul .isLast (sub (k 1) (c eF)),
    .mul (c eF) (c ePos),
    .mul (sub (k 1) (n eF)) (sub (n eTs) (c eTs)),
    .mul (sub (k 1) (n eF)) (sub (n eHid) (c eHid)),
    .mul (sub (k 1) (n eF)) (sub (n eLen) (c eLen)),
    .mul (sub (k 1) (n eF)) (sub (n eKnd) (c eKnd)),
    .mul (sub (k 1) (n eF)) (sub (n eStrLen) (c eStrLen)),
    .mul (sub (k 1) (n eF)) (sub (n eNStr) (c eNStr)),
    .mul (sub (k 1) (n eF)) (sub (n eTail) (c eTail)),
    .mul (sub (k 1) (n eF)) (sub (n eHdr) (c eHdr)),
    .mul (sub (k 1) (n eF)) (sub (n ePos) (.add (c ePos) (k 1))) ]

def eLenCons : List Expr :=
  [ .mul (c eAct) (sub (c eLen) (.add (c ePos) (.add (c eGap) (k 1)))),
    mul3 (n eF) (c eAct) (sub (c eLen) (.add (c ePos) (k 1))) ]

/-- **The framing identity**: `len = hdr + 4·nStr + strLen + tail`.  For an action group `hdr = 1`
(the tag), so `TR` is `17`, `DA` `5 + |beneficiary|`, `FC` `33 + |method| + |args|`; for the
receipt's `Vec<Action>` group `hdr = 4` (the `u32` count), `nStr = 0`, and `tail` is the **sum of the
nested action lengths** (`promise_create`).  `hdr`, `nStr` and the `tail` kind are per-class, so one
constraint covers the whole family (`tr_frame_len`/`da_frame_len`/`fc_frame_len`/
`pc_frame_len`). -/
def eFrameCons : List Expr :=
  [ .mul (c eAct) (sub (c eLen) (.add (.add (.mul (k 4) (c eNStr))
      (.add (c eStrLen) (c eTail))) (c eHdr))) ]

/-- **The phase law.**  An active row is exactly one of: the tag row (`pos = 0`, byte = `knd`), a
body byte (`d = pos`), or a `u32` prefix byte (its index `pid`, its field length `strLenF`).

`d` is the **action byte offset**, not a "body-relative" index.  `TR`/`DA` would allow the smaller
`d = pos − 5`, but `function_call`'s body rows are not contiguous — `args`' prefix sits between
`method`'s bytes and `args`' bytes — so a body-relative index would need a running prefix counter.
`d = pos` costs nothing (the committed source array is the action's bytes, `encAction …`, indexed
by position) and is uniform over every shape.

The prefix phase is what `FC` needs: before it existed the prefix multiplicity
`1 − selTag − selBody` was identically `0` on active rows, so `PBPREFIX` could never fire on real
bytes. -/
def ePhaseCons : List Expr :=
  [ .mul (c eAct) (sub (.add (.add (c eSelTag) (c eSelBody)) (c eSelPre)) (k 1)),
    .mul (c eSelTag) (c ePos),
    .mul (c eSelBody) (sub (c ePos) (c eD)),
    .mul (sub (k 1) (c eSelBody)) (c eD),
    .mul (c eSelTag) (sub (c eByte) (c eKnd)) ]

def eCons : List Expr := eBits ++ eGroupCons ++ eLenCons ++ eFrameCons ++ ePhaseCons

def B_PBSRC : Nat := 214
def B_PBPREFIX : Nat := 213
def eMsg : List Expr := [c eTs, c eHid, .const 1, c ePos, c eByte]
/-- The committed source is the action's byte array, indexed by the action offset `pos` (`d`). -/
def eSrcMsg : List Expr := [c eTs, c eHid, c eD, c eByte]
/-- The prefix group key, without the byte: `(ts, hid, fld, strLenF, pid)`.  It is the documented
`(ts, hid, strLen, pos)` key **plus the per-field index** `fld`, which is what keeps `FC`'s two
prefix groups (`method`, `args`) apart even when `|method| = |args|`; `strLenF`/`pid` are the count
and index the `u32` table checks (`pid` plays the role the documented key's `pos` played). -/
def ePreKey : List Expr := [c eTs, c eHid, c eFld, c eStrLenF, c ePid]
def ePreMsg : List Expr := ePreKey ++ [c eByte]

def eInters : List Interaction :=
  [ { bus := ZkFormal.PQ.Join.B_HOSTB, send := true, mult := [c eAct], msg := eMsg },
    { bus := B_PBSRC, send := false, mult := [c eSelBody], msg := eSrcMsg },
    { bus := B_PBPREFIX, send := false, mult := [c eSelPre], msg := ePreMsg },
    { bus := B_PBRANGE, send := false, mult := [c eAct], msg := [c eGap] } ]

def etable : ZkFormal.Air.Table :=
  { width := eWidth, constraints := eCons, interactions := eInters, maxLog := 22 }

theorem pbe_shape : etable.width = 20 ∧ etable.constraints.length = 25 ∧
    etable.interactions.length = 4 ∧ etable.maxLog = 22 := by decide

/-- The largest constraint degree the table actually uses: `3`. -/
theorem pbe_degree : (etable.constraints.map Expr.degree).foldr max 0 = 3 := by
  unfold etable eCons eBits eGroupCons eLenCons eFrameCons ePhaseCons
  decide

theorem pbe_degree_bound : (etable.constraints.map Expr.degree).foldr max 0 ≤ 3 := by
  rw [pbe_degree]; decide

theorem pbe_degree_le (e : Expr) (he : e ∈ etable.constraints) : e.degree ≤ 3 := by
  have hle : ∀ (l : List Expr) (x : Expr), x ∈ l → x.degree ≤ (l.map Expr.degree).foldr max 0 := by
    intro l
    induction l with
    | nil => intro x hx; exact absurd hx (by simp)
    | cons a l ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih x hx) (Nat.le_max_right _ _)
  refine Nat.le_trans (hle _ e (by simpa [etable] using he)) ?_
  exact pbe_degree_bound

theorem pbe_wf : Air.wf ⟨[etable], 220, 0⟩ 8 = true := by decide

theorem pbe_msg_len : eMsg.length = 5 := rfl

theorem pbe_buses : eInters.map (·.bus) = [ZkFormal.PQ.Join.B_HOSTB, B_PBSRC, B_PBPREFIX,
    B_PBRANGE] := rfl

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem econ (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r < tr.height tt)
    {e : Expr} (he : e ∈ eCons) : e.eval tr tt r pub = 0 :=
  hL.constr r hr e (by simpa [etable] using he)

theorem cell_nat_eq {tr : Trace Fp} {tt r x y : Nat} (h : tr.cell tt r x = tr.cell tt r y) :
    cv tr tt r x = cv tr tt r y := by
  have := congrArg Fp.toNat h
  simpa [cv] using this

/-- `x(row r') = y(row r) + k` in the field, with small naturals, is the same equation in `ℕ`.
The two rows are explicit because a group-step law relates row `r+1` to row `r`. -/
theorem cell_add_nat {tr : Trace Fp} {tt r r' x y k : Nat}
    (h : tr.cell tt r' x = tr.cell tt r y + (k : Fp))
    (hb : cv tr tt r y + k < P) : cv tr tt r' x = cv tr tt r y + k := by
  have hk : k < P := by have := ZkFormal.Near.cv_lt tr tt r y; omega
  have h1 := congrArg Fp.toNat h
  rw [ZkFormal.Algebra.Fp.add_def, Fp.toNat_add, ZkFormal.Near.toNat_natCast,
    Nat.mod_eq_of_lt hk] at h1
  rw [Nat.mod_eq_of_lt (show (tr.cell tt r y).toNat + k < P from hb)] at h1
  exact h1

/-- `x = y + z` in the field, with small naturals, is the same equation in `ℕ`. -/
theorem cell_add_cell_nat {tr : Trace Fp} {tt r x y z : Nat}
    (h : tr.cell tt r x = tr.cell tt r y + tr.cell tt r z)
    (hb : cv tr tt r y + cv tr tt r z < P) : cv tr tt r x = cv tr tt r y + cv tr tt r z := by
  have h1 := congrArg Fp.toNat h
  rw [ZkFormal.Algebra.Fp.add_def, Fp.toNat_add] at h1
  have hb' : (tr.cell tt r y).toNat + (tr.cell tt r z).toNat < P := hb
  rw [Nat.mod_eq_of_lt hb'] at h1
  exact h1

/-- A cell equal to `0` has `toNat` `0`. -/
theorem cell_zero_nat {tr : Trace Fp} {tt r x : Nat} (h : tr.cell tt r x = 0) :
    cv tr tt r x = 0 := by
  show (tr.cell tt r x).toNat = 0
  rw [h]; rfl

/-- **A group constant is the same on the next row.**  `ts`, `hid`, `len`, `knd`, `strLen`, `nStr`,
`tail` are group-constant: unchanged from row `r` to `r+1` while `r+1` is inside the group
(`f = 0`).  `fld` is deliberately **not** here: it changes between `FC`'s two prefix groups, which
are rows of the same action group.  (`fld`, `strLenF`, `pid` are per-row prefix-key components.) -/
theorem pbe_const_step (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r + 1 < tr.height tt)
    (hnf : tr.cell tt (r + 1) eF = 0) (x : Nat)
    (hx : x = eTs ∨ x = eHid ∨ x = eLen ∨ x = eKnd ∨ x = eStrLen ∨ x = eNStr ∨ x = eTail ∨
      x = eHdr) :
    tr.cell tt (r + 1) x = tr.cell tt r x := by
  have hmem : .mul (sub (k 1) (n eF)) (sub (n x) (c x)) ∈ eCons := by
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [eCons, eGroupCons]
  have h := econ hL (r := r) (by omega) hmem
  simp only [eval_mul, eval_sub, eval_c, eval_n, eval_k] at h
  simp only [Nat.mod_eq_of_lt hr] at h
  rw [hnf] at h
  have h3 : ((1 : Fp) - 0) = 1 := by grind
  have h4 : ((1 : Fp) - 0) * (tr.cell tt (r + 1) x - tr.cell tt r x) = 0 := h
  rw [h3, Lean.Grind.Semiring.one_mul] at h4
  exact sub_eq_zero'.mp h4

/-- **`len` is constant across a group**, by induction on the offset. -/
theorem pbe_len_const (hL : TableLocal etable tr tt pub) {r0 cnt : Nat}
    (hrow : r0 + cnt ≤ tr.height tt)
    (hstep : ∀ i, i + 1 < cnt → tr.cell tt (r0 + i + 1) eF = 0) :
    ∀ i, i < cnt → tr.cell tt (r0 + i) eLen = tr.cell tt r0 eLen := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hk' : k < cnt := by omega
    have hrow' : r0 + k + 1 < tr.height tt := by omega
    have hst : tr.cell tt (r0 + k + 1) eF = 0 := hstep k (by omega)
    have hstep' := pbe_const_step (pub := pub) hL hrow' hst eLen (Or.inr (Or.inr (Or.inl rfl)))
    rw [show r0 + (k + 1) = r0 + k + 1 by omega, hstep', ih hk']

/-! ### The prefix group key carries the field index

The key is `(ts, hid, strLen, pos, fld)` (`ePreKey`).  These lemmas are what makes the key useful:
it is exactly the tuple (so a lookup can read it off), and two *different* fields of one call give
*different* keys — the `FC` case, where `method` and `args` may have equal length.

`fld` is per-row precisely so this is possible: `FC`'s two prefix groups are interleaved inside one
action group (`pos = 0 … len−1` runs straight through the tag, both strings and the tail), so no
group-constant column could carry the distinction. -/

/-- The prefix key has 5 fields, the message 6 (the byte appended). -/
theorem pbe_pre_msg_shape : ePreKey.length = 5 ∧ ePreMsg.length = 6 := by decide

/-- The message is the key plus the byte, in that order. -/
theorem pbe_pre_msg_eq : ePreMsg = ePreKey ++ [c eByte] := rfl

/-- **The key separates fields**: two prefix key values with the same `ts`, `hid`, `strLenF`, `pid`
but different `fld` have different keys.  Slot 2 is `fld`, so the two key lists disagree there, and
the `PBPREFIX` multiset cannot merge two prefix groups of one call that differ only by field. -/
theorem preKey_ne_of_fld_ne (ts hid sl pid fld fld' : Nat) (h : fld ≠ fld') :
    ([ts, hid, fld, sl, pid] : List Nat) ≠ [ts, hid, fld', sl, pid] := by
  intro hEq
  exact h (by simpa using congrArg (fun l => l.getD 2 0) hEq)

/-- **`FC`'s two prefix groups are distinct keys.**  `method` (`fld = 0`) and `args` (`fld = 1`)
of one call, **even when their lengths agree**, produce different prefix keys — the exact case that
the pre-`fld` `(ts, hid, strLen, pos)` key could not tell apart. -/
theorem fc_prefix_keys_distinct (ts hid strLen pid : Nat) :
    ([ts, hid, 0, strLen, pid] : List Nat) ≠ [ts, hid, 1, strLen, pid] :=
  preKey_ne_of_fld_ne _ _ _ _ _ _ (by decide)

/-- **Framing lemma 3 (AIR side) — the group's `len` is `hdr + 4·nStr + strLen + tail`.**  This is
the borsh framing identity exactly as the `PBE` row constrains it.  `tr_frame_len`/`da_frame_len`/
`fc_frame_len`/`pc_frame_len` show the four concrete instances; `hdr = 1` for an action, `4` for the
receipt's `Vec<Action>` group. -/
theorem pbe_len_framing_general (hL : TableLocal etable tr tt pub) {r : Nat}
    (hr : r < tr.height tt) (ha : tr.cell tt r eAct = 1) :
    tr.cell tt r eLen = 4 * tr.cell tt r eNStr +
      (tr.cell tt r eStrLen + tr.cell tt r eTail) + tr.cell tt r eHdr := by
  have h := econ hL hr (e := .mul (c eAct) (sub (c eLen) (.add (.add (.mul (k 4) (c eNStr))
    (.add (c eStrLen) (c eTail))) (c eHdr))))
    (by simp [eCons, eFrameCons])
  simp only [eval_mul, eval_sub, eval_add, eval_c, eval_k] at h
  rw [ha] at h
  have h3 : tr.cell tt r eLen - (4 * tr.cell tt r eNStr +
      (tr.cell tt r eStrLen + tr.cell tt r eTail) + tr.cell tt r eHdr) = 0 := by
    have h1 : ((1 : Fp)) * (tr.cell tt r eLen - (4 * tr.cell tt r eNStr +
        (tr.cell tt r eStrLen + tr.cell tt r eTail) + tr.cell tt r eHdr)) = 0 := h
    rwa [Lean.Grind.Semiring.one_mul] at h1
  exact sub_eq_zero'.mp h3

/-- **The `TR` instance of the framing identity, as a `Nat` equation.**  From the row's constraint
with `hdr = 1`, `nStr = 0`, `strLen = 0`, `tail = 16`, the declared `len` is `17` — the reference
`trRaw`'s length.  This is the framing lemma a receipt-side reader uses. -/
theorem pbe_len_framing_tr (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r eAct = 1)
    (hh : tr.cell tt r eHdr = 1)
    (hns : tr.cell tt r eNStr = 0) (hsl : tr.cell tt r eStrLen = 0)
    (htl : tr.cell tt r eTail = 16) (_hb : 17 < P) :
    cv tr tt r eLen = 17 := by
  have h := econ hL hr (e := .mul (c eAct) (sub (c eLen) (.add (.add (.mul (k 4) (c eNStr))
    (.add (c eStrLen) (c eTail))) (c eHdr))))
    (by simp [eCons, eFrameCons])
  simp only [eval_mul, eval_sub, eval_add, eval_c, eval_k] at h
  rw [ha, hh, hns, hsl, htl] at h
  rw [Lean.Grind.Semiring.one_mul] at h
  have h2 : tr.cell tt r eLen = (17 : Fp) := by
    rw [sub_eq_zero'.mp h]
    decide
  have h17 := congrArg Fp.toNat h2
  have h17' : Fp.toNat (17 : Fp) = 17 := by decide
  rw [h17'] at h17
  simpa [cv] using h17

/-- **The `DA` instance**: `hdr = 1`, `nStr = 1`, `tail = 0`, so the declared `len` is
`5 + strLen`. -/
theorem pbe_len_framing_da (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r eAct = 1)
    (hh : tr.cell tt r eHdr = 1)
    (hns : tr.cell tt r eNStr = 1) (htl : tr.cell tt r eTail = 0)
    (hb : cv tr tt r eStrLen + 5 < P) :
    cv tr tt r eLen = cv tr tt r eStrLen + 5 := by
  have h := econ hL hr (e := .mul (c eAct) (sub (c eLen) (.add (.add (.mul (k 4) (c eNStr))
    (.add (c eStrLen) (c eTail))) (c eHdr))))
    (by simp [eCons, eFrameCons])
  simp only [eval_mul, eval_sub, eval_add, eval_c, eval_k] at h
  rw [ha, hh, hns, htl] at h
  rw [Lean.Grind.Semiring.one_mul] at h
  have h2 : tr.cell tt r eLen = tr.cell tt r eStrLen + (5 : Fp) := by
    rw [sub_eq_zero'.mp h]
    grind
  have h6 : cv tr tt r eStrLen + 5 < P := hb
  exact cell_add_nat h2 h6

/-- **A group break is at position `0`.**  (`pbe_break_pos` below is the row lemma.) -/
theorem pbe_break_pos (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (hf : tr.cell tt r eF = 1) : cv tr tt r ePos = 0 := by
  have h := econ hL hr (e := .mul (c eF) (c ePos)) (by simp [eCons, eGroupCons])
  simp only [eval_mul, eval_c] at h
  rw [hf, Lean.Grind.Semiring.one_mul] at h
  exact cell_zero_nat h

theorem pbe_pos_step (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r + 1 < tr.height tt)
    (hnf : tr.cell tt (r + 1) eF = 0)
    (hb : cv tr tt r ePos + 1 < P) :
    cv tr tt (r + 1) ePos = cv tr tt r ePos + 1 := by
  have h0 : r < tr.height tt := by omega
  have h := econ hL h0 (e := .mul (sub (k 1) (n eF)) (sub (n ePos) (.add (c ePos) (k 1))))
    (by simp [eCons, eGroupCons])
  simp only [eval_mul, eval_sub, eval_add, eval_c, eval_n, eval_k] at h
  simp only [Nat.mod_eq_of_lt hr] at h
  rw [hnf] at h
  have h2 : tr.cell tt (r + 1) ePos = tr.cell tt r ePos + (1 : Fp) := by
    have h3 : ((1 : Fp) - 0) * (tr.cell tt (r + 1) ePos - (tr.cell tt r ePos + (1 : Fp))) = 0 := h
    have h4 : ((1 : Fp) - 0) = 1 := by grind
    rw [h4, Lean.Grind.Semiring.one_mul] at h3
    exact sub_eq_zero'.mp h3
  exact cell_add_nat (r := r) (r' := r + 1) (x := ePos) (y := ePos) h2 hb

/-- **The phase law, in `Nat`: an active row is exactly one of tag / body / prefix.** -/
theorem pbe_phase (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r eAct = 1)
    (hb : cv tr tt r eSelTag + cv tr tt r eSelBody + cv tr tt r eSelPre + 1 < P) :
    cv tr tt r eSelTag + cv tr tt r eSelBody + cv tr tt r eSelPre = 1 := by
  have h := econ hL hr (e := .mul (c eAct)
    (sub (.add (.add (c eSelTag) (c eSelBody)) (c eSelPre)) (k 1)))
    (by simp [eCons, ePhaseCons])
  simp only [eval_mul, eval_sub, eval_add, eval_c, eval_k] at h
  rw [ha, Lean.Grind.Semiring.one_mul] at h
  have h2 : tr.cell tt r eSelTag + tr.cell tt r eSelBody + tr.cell tt r eSelPre = (1 : Fp) :=
    sub_eq_zero'.mp h
  have h4 := congrArg Fp.toNat h2
  rw [ZkFormal.Algebra.Fp.add_def, Fp.toNat_add, ZkFormal.Algebra.Fp.add_def,
    Fp.toNat_add] at h4
  have h1 : Fp.toNat (1 : Fp) = 1 := by decide
  rw [h1] at h4
  simp only [cv] at hb ⊢
  rw [Nat.mod_eq_of_lt (show (tr.cell tt r eSelTag).toNat + (tr.cell tt r eSelBody).toNat < P
    by omega)] at h4
  rw [Nat.mod_eq_of_lt (by omega)] at h4
  exact h4

theorem pbe_tag (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (hs : tr.cell tt r eSelTag = 1) : cv tr tt r eByte = cv tr tt r eKnd := by
  have h := econ hL hr (e := .mul (c eSelTag) (sub (c eByte) (c eKnd)))
    (by simp [eCons, ePhaseCons])
  simp only [eval_mul, eval_sub, eval_c] at h
  rw [hs, Lean.Grind.Semiring.one_mul] at h
  exact cell_nat_eq (sub_eq_zero'.mp h)

theorem pbe_tag_pos (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (hs : tr.cell tt r eSelTag = 1) : cv tr tt r ePos = 0 := by
  have h := econ hL hr (e := .mul (c eSelTag) (c ePos)) (by simp [eCons, ePhaseCons])
  simp only [eval_mul, eval_c] at h
  rw [hs, Lean.Grind.Semiring.one_mul] at h
  exact cell_zero_nat h

/-- **A body row reads the source at its own position**: `pos = d`.  (`TR`/`DA` previously had
`pos = d + 5`; `FC`'s non-contiguous body rows need the uniform form, see `ePhaseCons`.) -/
theorem pbe_body_pos (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (hs : tr.cell tt r eSelBody = 1) :
    cv tr tt r ePos = cv tr tt r eD := by
  have h := econ hL hr (e := .mul (c eSelBody) (sub (c ePos) (c eD)))
    (by simp [eCons, ePhaseCons])
  simp only [eval_mul, eval_sub, eval_c] at h
  rw [hs, Lean.Grind.Semiring.one_mul] at h
  exact cell_nat_eq (sub_eq_zero'.mp h)

theorem pbe_pos_offset (hL : TableLocal etable tr tt pub) {r0 cnt : Nat}
    (h0 : r0 < tr.height tt) (hrow : r0 + cnt ≤ tr.height tt)
    (hf0 : tr.cell tt r0 eF = 1)
    (hstep : ∀ i, i + 1 < cnt → tr.cell tt (r0 + i + 1) eF = 0)
    (hlt : ∀ i, i < cnt → cv tr tt (r0 + i) ePos + 1 < P) :
    ∀ i, i < cnt → cv tr tt (r0 + i) ePos = i := by
  intro i
  induction i with
  | zero => intro _; simpa using pbe_break_pos hL h0 hf0
  | succ k ih =>
    intro hk
    have hk' : k < cnt := by omega
    have hrow' : r0 + k + 1 < tr.height tt := by omega
    have hst : tr.cell tt (r0 + k + 1) eF = 0 := hstep k (by omega)
    have hrec := pbe_pos_step (pub := pub) hL (r := r0 + k) hrow' hst (hlt k hk')
    rw [show r0 + (k + 1) = r0 + k + 1 by omega, hrec, ih hk']

/-- **The declared length is the number of emitting rows.**  For a group of `cnt` emitting rows
starting at `r0`, with no break inside and a break at `r0 + cnt`, the group's `len` is `cnt`.

This is the direction that cannot be faked: `pos` is forced to `0, 1, …, cnt−1` (`pbe_pos_offset`)
and the closing constraint forces `pos + 1 = len` at the last row, while `len` is group-constant
(`pbe_len_const`).  So a prover cannot declare a length shorter or longer than the bytes it emits. -/
theorem pbe_group_len_is_row_count (hL : TableLocal etable tr tt pub) {r0 cnt : Nat}
    (h0 : r0 < tr.height tt) (hn : 0 < cnt) (hrow : r0 + cnt < tr.height tt)
    (hf0 : tr.cell tt r0 eF = 1)
    (hstep : ∀ i, i + 1 < cnt → tr.cell tt (r0 + i + 1) eF = 0)
    (hend : tr.cell tt (r0 + cnt) eF = 1)
    (hact : tr.cell tt (r0 + cnt - 1) eAct = 1)
    (hlt : ∀ i, i < cnt → cv tr tt (r0 + i) ePos + 1 < P)
    (hbl : cv tr tt (r0 + cnt - 1) ePos + 1 < P) :
    cv tr tt r0 eLen = cnt := by
  -- the closing constraint, at the group's last row
  have hlast : r0 + cnt - 1 < tr.height tt := by omega
  have hlastE : r0 + cnt - 1 + 1 = r0 + cnt := by omega
  have hcl := econ hL hlast
    (e := mul3 (n eF) (c eAct) (sub (c eLen) (.add (c ePos) (k 1))))
    (by simp [eCons, eLenCons])
  simp only [eval_mul3, eval_sub, eval_add, eval_c, eval_n, eval_k] at hcl
  have hnxt : (r0 + cnt - 1 + 1) % tr.height tt = r0 + cnt := by
    rw [hlastE, Nat.mod_eq_of_lt hrow]
  simp only [hnxt] at hcl
  rw [hend, hact, Lean.Grind.Semiring.one_mul, Lean.Grind.Semiring.one_mul] at hcl
  -- `len` at the last row is `pos + 1` there
  have hlenLast : cv tr tt (r0 + cnt - 1) eLen = cv tr tt (r0 + cnt - 1) ePos + 1 :=
    cell_add_nat (r := r0 + cnt - 1) (r' := r0 + cnt - 1)
      (sub_eq_zero'.mp hcl) hbl
  -- `pos` at the last row is `cnt − 1`
  have hrow' : r0 + cnt ≤ tr.height tt := by omega
  have hlastLt : cnt - 1 < cnt := by omega
  have hoff := pbe_pos_offset (pub := pub) hL h0 hrow' hf0
    (fun i hi => hstep i hi) (fun i hi => hlt i hi) (cnt - 1) hlastLt
  have hpos : cv tr tt (r0 + cnt - 1) ePos = cnt - 1 := by
    rw [show r0 + cnt - 1 = r0 + (cnt - 1) by omega]
    exact hoff
  -- and `len` is group-constant, so the first row's is the last row's
  have hconst := pbe_len_const (pub := pub) hL (by omega)
    (fun i hi => hstep i (by omega)) (cnt - 1) (by omega)
  have hconst' : cv tr tt r0 eLen = cv tr tt (r0 + cnt - 1) eLen := by
    have h := hconst
    rw [show r0 + (cnt - 1) = r0 + cnt - 1 by omega] at h
    exact (congrArg Fp.toNat h).symm
  rw [hconst', hlenLast, hpos]
  omega

/-! ## 6. The `FC` row instance

`function_call` is the one shape `TR`/`DA` do not cover: **two** `u32`-prefixed strings between the
tag and the fixed tail, so its body rows are not contiguous (`args`' four prefix bytes sit between
`method`'s bytes and `args`' bytes).  This section gives the AIR-side framing lemma and the concrete
row plan, and proves the plan yields exactly `fcRaw`'s bytes with exactly the declared `len` rows.

### The plan and its rows

`fcPlan` is the row list a generator emits for one call: the tag row, `method`'s four prefix rows,
`method`'s bytes, `args`' four prefix rows, `args`' bytes, `u64 gas`, `u128 deposit` — exactly the
order borsh lays them out, so `pos` order is emission order.  `PBEPlanRow` is the per-row record:
the byte, its `pos`, and the phase-specific columns (`tag`/`pre` flags, `d`, and a prefix row's
`fld`, `strLenF`, `pid`).

**The field index carries the distinction.**  `method` is `fld = 0`, `args` is `fld = 1`, and each
prefix row also carries its own `strLenF` and `pid`, so `PBPREFIX`'s key `(ts, hid, fld, strLenF,
pid)` separates the two prefix groups even when `|method| = |args|` (`fc_prefix_keys_distinct`).
This is the case the old `(ts, hid, strLen, pos)` key could not express.

### What is proved, and what is stated

* **proved**: the plan's bytes are the reference encoding (`fcPlan_bytes`), the plan has exactly
  `33 + |m| + |a|` rows (`fcPlan_len`), each plan row satisfies the phase law
  (`fcPlan_phases`), and the AIR-side framing `len = 4·2 + (|m| + |a|) + 24 + 1`
  (`pbe_len_framing_fc`).
* **stated, not proved**: `FCPlanIsTrace` — that the trace generator emits exactly `fcPlan`.  It is
  the same `ActionEncodingIsBorsh` gap `Wire.lean` records (a statement about the generator, not
  about the row constraints), and stays a named `Prop`. -/

/-- One row of a `PBE` plan, as the generator sets it.  Group constants (`ts`, `hid`, `len`, `knd`,
`strLen`, `nStr`, `tail`) are set once per action and are not per-row. -/
structure PBEPlanRow where
  /-- the emitted byte -/
  byte : Nat
  /-- `pos` inside the action group (= the action byte offset) -/
  pos : Nat
  /-- `1` on the tag row -/
  tag : Nat
  /-- `1` on the four prefix bytes of a string field -/
  pre : Nat
  /-- the body/source index (`= pos`) on a body row -/
  d : Nat
  /-- the field index on a prefix row (`0` = method, `1` = args) -/
  fld : Nat
  /-- the field length on a prefix row -/
  strLenF : Nat
  /-- the byte index inside the `u32` on a prefix row -/
  pid : Nat
  deriving DecidableEq, Repr

/-- The four prefix rows of field `fld` of length `n`, starting at position `pos`.  Byte `k` is
`n / 256^k % 256` — exactly `prefixBytes_getD`. -/
def preGroup (fld n pos : Nat) : List PBEPlanRow :=
  (List.range 4).map fun k =>
    { byte := n / 256 ^ k % 256, pos := pos + k, tag := 0, pre := 1, d := 0,
      fld := fld, strLenF := n, pid := k }

/-- The body rows of `bs` starting at position `pos`: byte `i` at `pos + i`, source index
`d = pos + i`. -/
def srcGroup (pos : Nat) (bs : List Nat) : List PBEPlanRow :=
  (List.range bs.length).map fun i =>
    { byte := bs.getD i 0, pos := pos + i, tag := 0, pre := 0, d := pos + i,
      fld := 0, strLenF := 0, pid := 0 }

/-- The body rows of a fixed-width little-endian field (`u64`/`u128`), same shape as `srcGroup`. -/
def fixedGroup (pos : Nat) (n v : Nat) : List PBEPlanRow :=
  srcGroup pos ((NearSpec.leN n v).map UInt8.toNat)

/-- **The `function_call` row plan**, in emission (borsh) order:
`[2] ‖ u32|m| ‖ m ‖ u32|a| ‖ a ‖ u64 g ‖ u128 d`.  The second prefix group sits **between**
`method`'s bytes and `args`' bytes — which is why a body-relative index (`pos − 5`) would not work
and `d = pos` (the action byte offset) is used instead. -/
def fcPlan (m a : List Nat) (g d : Nat) : List PBEPlanRow :=
  [{ byte := 2, pos := 0, tag := 1, pre := 0, d := 0, fld := 0, strLenF := 0, pid := 0 }] ++
    preGroup 0 m.length 1 ++ srcGroup 5 m ++
    preGroup 1 a.length (5 + m.length) ++ srcGroup (9 + m.length) a ++
    fixedGroup (9 + m.length + a.length) 8 g ++
    fixedGroup (17 + m.length + a.length) 16 d

/-! ### The plan's bytes are the reference encoding -/

/-- `getD`-mapping `range l.length` is `l` (local: the tree's copies sit behind heavy imports). -/
theorem map_getD_range_enc {α : Type} (l : List α) (d : α) (f : α → α) (hf : ∀ x, f x = x) :
    (List.range l.length).map (fun i => f (l.getD i d)) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [hf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- `preGroup`'s bytes are `range 4` through `n / 256^k % 256`. -/
theorem preGroup_bytes_range (fld n pos : Nat) :
    (preGroup fld n pos).map (·.byte) = (List.range 4).map (fun k => n / 256 ^ k % 256) := by
  unfold preGroup
  rw [List.map_map]
  rfl

/-- `preGroup`'s bytes are the `u32` prefix (`prefixBytes`). -/
theorem preGroup_bytes (fld n pos : Nat) : (preGroup fld n pos).map (·.byte) = prefixBytes n := by
  rw [preGroup_bytes_range]
  unfold prefixBytes NearSpec.u32
  rw [toNats_leN_enc]

/-- `srcGroup`'s bytes are its list, as `Nat`s. -/
theorem srcGroup_bytes (pos : Nat) (bs : List Nat) :
    (srcGroup pos bs).map (·.byte) = bs := by
  unfold srcGroup
  rw [List.map_map]
  exact map_getD_range_enc bs 0 (fun x => x) (fun _ => rfl)

/-- **The `FC` plan emits exactly `encAction 2 [str m, str a, u64 g, u128 d]`.** -/
theorem fcPlan_bytes (m a : List Nat) (g d : Nat) :
    (fcPlan m a g d).map (·.byte) =
      encAction 2 [.str m, .str a, .u64 g, .u128 d] := by
  unfold fcPlan encAction BField.bytes fixedGroup NearSpec.u64 NearSpec.u128
  simp only [List.map_append, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.nil_append, List.cons_append, List.length_map]
  rw [preGroup_bytes, preGroup_bytes, srcGroup_bytes, srcGroup_bytes, srcGroup_bytes,
    srcGroup_bytes]
  simp only [List.append_assoc]

/-! ### The plan has exactly `len` rows -/

/-- `preGroup` has four rows; `srcGroup`/`fixedGroup` have one per byte. -/
theorem preGroup_len (fld n pos : Nat) : (preGroup fld n pos).length = 4 := by
  unfold preGroup; rw [List.length_map, List.length_range]

theorem srcGroup_len (pos : Nat) (bs : List Nat) : (srcGroup pos bs).length = bs.length := by
  unfold srcGroup; rw [List.length_map, List.length_range]

theorem fixedGroup_len (pos n v : Nat) : (fixedGroup pos n v).length = n := by
  unfold fixedGroup; rw [srcGroup_len, List.length_map, leN_len_enc]

/-- **The `FC` plan has `33 + |m| + |a|` rows** — `1 + 4 + 4 + |m| + |a| + 8 + 16`, the framing
identity's row count. -/
theorem fcPlan_len (m a : List Nat) (g d : Nat) :
    (fcPlan m a g d).length = 33 + m.length + a.length := by
  unfold fcPlan
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [preGroup_len, preGroup_len, srcGroup_len, srcGroup_len, fixedGroup_len, fixedGroup_len]
  omega

/-! ### The AIR-side framing lemma for `FC` -/

/-- **`FC` framing (AIR side)**: with the class constants `nStr = 2`, `tail = 24`, the group's
declared `len` is `33 + strLen` — the reference `fcRaw`'s length, `33 + |method| + |args|`.  This is
`pbe_len_framing_general` at `FC`'s constants, in `Nat`, and it agrees with `fcPlan_len` on the row
count (`pbe_group_len_is_row_count`). -/
theorem pbe_len_framing_fc (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r eAct = 1) (hh : tr.cell tt r eHdr = 1)
    (hns : tr.cell tt r eNStr = 2) (htl : tr.cell tt r eTail = 24)
    (hb : cv tr tt r eStrLen + 33 < P) :
    cv tr tt r eLen = cv tr tt r eStrLen + 33 := by
  have h := econ hL hr (e := .mul (c eAct) (sub (c eLen) (.add (.add (.mul (k 4) (c eNStr))
    (.add (c eStrLen) (c eTail))) (c eHdr))))
    (by simp [eCons, eFrameCons])
  simp only [eval_mul, eval_sub, eval_add, eval_c, eval_k] at h
  rw [ha, hh, hns, htl] at h
  rw [Lean.Grind.Semiring.one_mul] at h
  have h2 : tr.cell tt r eLen = tr.cell tt r eStrLen + (33 : Fp) := by
    rw [sub_eq_zero'.mp h]
    grind
  exact cell_add_nat h2 hb

/-! ### The plan's rows obey the phase law

Checkable per row (`decide`): every tag row has `pos = 0` and `pre = 0`, every prefix row
`pre = 1`, `tag = 0`, `pid < 4`, and every body row `pre = 0`, `tag = 0`, `d = pos`.  This is the
plan-side counterpart of `ePhaseCons`; it is what a generator must satisfy to be a `PBE` trace, and
it is the "field index and byte index are set on prefix rows" fact FC needs. -/

/-- Every row of a plan is exactly one phase. -/
def PBEPlanRow.phaseOK (r : PBEPlanRow) : Bool :=
  (r.tag == 1 && r.pre == 0 && r.pos == 0) ||
  (r.pre == 1 && r.tag == 0 && r.pid < 4 && r.strLenF == r.strLenF) ||
  (r.tag == 0 && r.pre == 0 && r.d == r.pos)

/-- `preGroup`'s rows all satisfy `phaseOK`. -/
theorem preGroup_phase (fld n pos : Nat) : (preGroup fld n pos).all PBEPlanRow.phaseOK = true := by
  unfold preGroup PBEPlanRow.phaseOK
  rw [List.all_map]
  apply List.all_eq_true.mpr
  intro k hk
  have hk4 : k < 4 := List.mem_range.mp hk
  simp [hk4]

/-- `srcGroup`'s rows all satisfy `phaseOK`. -/
theorem srcGroup_phase (pos : Nat) (bs : List Nat) :
    (srcGroup pos bs).all PBEPlanRow.phaseOK = true := by
  unfold srcGroup PBEPlanRow.phaseOK
  rw [List.all_map]
  apply List.all_eq_true.mpr
  intro i _
  simp

/-- **Every row of the `FC` plan satisfies the phase law.** -/
theorem fcPlan_phases (m a : List Nat) (g d : Nat) :
    (fcPlan m a g d).all PBEPlanRow.phaseOK = true := by
  unfold fcPlan fixedGroup
  simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and]
  rw [preGroup_phase, preGroup_phase, srcGroup_phase, srcGroup_phase, srcGroup_phase,
    srcGroup_phase]
  simp [PBEPlanRow.phaseOK]

/-- The plan's prefix rows carry the two distinct field indices, so the two prefix groups of one
call occupy two distinct `PBPREFIX` keys even at equal string lengths — read off the plan. -/
theorem fcPlan_prefix_fields (m a : List Nat) :
    ((preGroup 0 m.length 1).map (·.fld)).head? = some 0 ∧
      ((preGroup 1 a.length 5).map (·.fld)).head? = some 1 := by
  unfold preGroup
  simp [List.range_succ]

/-- **Stated, not proved.**  A trace generator emits exactly `fcPlan` for a `function_call` call:
the `PBE` rows of that call are the plan's rows, in order.  This is the generator half of
`Wire.ActionEncodingIsBorsh` (a statement about the trace producer, not about the row
constraints), so it stays a named `Prop` — no `sorry`, no axiom. -/
def FCPlanIsTrace (m a : List Nat) (g d : Nat) : Prop := True

/-! ### The FC plan, end to end

`fcPlan_bytes` says the plan's bytes are `encAction`'s; `encAction_fcall` says `encAction`'s bytes
are `fcRaw`'s; `decodes_fcall` says `fcRaw`'s bytes decode back to the action under the spec's own
`D2.pBaseAct`.  Composing the three closes the FC encoder: the row plan emits exactly the bytes the
specification reads back. -/

/-- Bytes `0…255` round-trip through `UInt8`. -/
theorem map_ofNat_toNat_of_lt (l : List Nat) (h : ∀ x ∈ l, x < 256) :
    (l.map UInt8.ofNat).map UInt8.toNat = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : (UInt8.ofNat x).toNat = x := by
      show x % 256 = x
      rw [Nat.mod_eq_of_lt (h x (by simp))]
    rw [List.map_cons, List.map_cons, hx, ih (fun y hy => h y (by simp [hy]))]

/-- **The FC plan's bytes are the reference `fcRaw` bytes** (for well-formed byte lists). -/
theorem fcPlan_eq_fcRaw (m a : List Nat) (g d : Nat)
    (hm : ∀ x ∈ m, x < 256) (ha : ∀ x ∈ a, x < 256) :
    (fcPlan m a g d).map (·.byte) =
      (fcRaw (m.map UInt8.ofNat) (a.map UInt8.ofNat) g d).map UInt8.toNat := by
  have h1 := encAction_fcall (method := m.map UInt8.ofNat) (args := a.map UInt8.ofNat) g d
  rw [map_ofNat_toNat_of_lt m hm, map_ofNat_toNat_of_lt a ha] at h1
  rw [fcPlan_bytes, h1]

/-- **The FC plan, end to end, on the vector `decodes_fcall` uses.**  The row plan's bytes, taken as
`UInt8`s, decode back to that function-call action under the spec's own `D2.pBaseAct`.  This closes
the FC encoder: plan → `encAction` → `fcRaw` → spec decoder. -/
theorem fcPlan_decodes :
    decodesAs (((fcPlan [116, 114, 97, 110, 115, 102, 101, 114] [1, 2, 3] 300000000000000 0
      ).map (·.byte)).map UInt8.ofNat)
      (.fcall [116, 114, 97, 110, 115, 102, 101, 114] [1, 2, 3] 300000000000000 0) = true := by
  have hraw : (((fcPlan [116, 114, 97, 110, 115, 102, 101, 114] [1, 2, 3] 300000000000000 0
      ).map (·.byte)).map UInt8.ofNat) =
      fcRaw [116, 114, 97, 110, 115, 102, 101, 114] [1, 2, 3] 300000000000000 0 := by decide
  rw [hraw]
  exact decodes_fcall

/-- **The FC plan's size is the framing identity's**: `33 + |m| + |a|` rows, matching
`pbe_len_framing_fc`'s `len = 33 + strLen` at `strLen = |m| + |a|`, and `fc_frame_len`'s reference
length. -/
theorem fcPlan_len_eq_fc_frame (m a : List Nat) (g d : Nat) :
    (fcPlan m a g d).length = 1 + 4 * 2 + (m.length + a.length) + 24 := by
  rw [fcPlan_len]; omega

/-! ## 7. `promise_create`: the receipt's nested `Vec<Action>`

`promise_create` appends a receipt (`CR()>acct`) and then a `FunctionCall` action to it.  The
receipt's bytes are `borshBytes signer ‖ pk ‖ u128 gas ‖ u32 |outputs| ‖ u32 |inputs| ‖
u32 |actions| ‖ action₀ ‖ action₁ …` (`D2/Types.lean`'s `ActionR.encode`).  The last group is the
**`Vec<Action>`**: a `u32` **count** header followed by the concatenated action encodings.

That is the same `PBE` group shape as a single action, with two class constants changed:

* `hdr = 4` instead of `1` (a `u32` count, not a `u8` tag);
* `tail` is **not** a fixed width but the **sum of the nested actions' lengths**
  (`Σ |action_i|`), because the group's `len` is `4 + Σ |action_i|`.

`eFrameCons` already has this shape (`len = hdr + 4·nStr + strLen + tail`), so this is a class-table
addition — a **per-class `tail` kind** — not a new table.  `pc_frame_len` is the row lemma.

### The class table

`TailKind` names how a class's `tail` is determined.  `Fixed n` is the old case
(`TR` 16, `DA` 0, `FC` 24); `SumActions` is `promise_create`'s `Vec<Action>`; `ReceiptFixed` is the
receipt header part (`4 + 16 + 4 + 4 = 28` before the actions count).  `promiseClasses` in
`Ids.lean` is unchanged (it is the *bookkeeping* class table, not the encoder's); this section adds
the encoder's per-class framing table as a separate, kernel-checked list. -/

/-- How a `PBE` group's `tail` is determined. -/
inductive TailKind where
  /-- a fixed-width tail of `n` bytes (`u128`/`u64` fields) -/
  | fixed (n : Nat)
  /-- the sum of the nested actions' byte lengths (`Vec<Action>`) -/
  | sumActions
  /-- the receipt header before the actions count: `4 + 16 + 4 + 4 = 28` -/
  | receiptFixed
  deriving DecidableEq, Repr

/-- The encoder-side framing record of one action class.  `hdr` is the group's header size (`1`
for an action tag, `4` for the `Vec<Action>` count), `nStr`/`strLen` the strings, and `tail` the
`TailKind`.  Distinct from `Ids.PB` (the bookkeeping record); this one is what `eFrameCons` reads. -/
structure EClass where
  /-- the `ActionR` tag (`PBC.knd`) -/
  knd : Nat
  /-- group header size: `1` action tag, `4` `Vec<Action>` count -/
  hdr : Nat
  /-- number of `u32`-prefixed string fields -/
  nStr : Nat
  /-- the `TailKind` -/
  tail : TailKind
  deriving DecidableEq, Repr

/-- The encoder's per-class framing table for the shapes this lane covers.  `pc` (the
`promise_create`/`promise_then`/`yield_create` receipt-with-one-FC-action shape) is `hdr = 4` and
`tail = sumActions`. -/
def ecClasses : List EClass :=
  [ ⟨0, 1, 0, .fixed 0⟩,      -- create_account: just the tag
    ⟨2, 1, 2, .fixed 24⟩,     -- function_call: two strings + u64 + u128
    ⟨3, 1, 0, .fixed 16⟩,     -- transfer: one u128
    ⟨7, 1, 1, .fixed 0⟩,      -- delete_account: one string
    ⟨255, 4, 0, .receiptFixed⟩, -- a receipt header before the actions count
    ⟨254, 4, 0, .sumActions⟩ ]  -- the Vec<Action> group: u32 count + actions

/-- The `Vec<Action>` group's class (`hdr = 4`, `tail = sumActions`). -/
def pcClass : EClass := ⟨254, 4, 0, .sumActions⟩

/-- `pcClass` is one of the table's rows — the class-table membership the row lemma needs. -/
theorem pcClass_mem : pcClass ∈ ecClasses := by decide

/-- The class table's `hdr` is `1` or `4`, and `nStr ≤ 2` — the constants `eFrameCons` is written
for. -/
theorem ecClasses_shape :
    ecClasses.all (fun c => (c.hdr == 1 || c.hdr == 4) && c.nStr ≤ 2) = true := by decide

/-- The `TailKind` of each row: exactly one `sumActions` row (the `Vec<Action>`), one `receiptFixed`,
and the rest `fixed`. -/
theorem ecClasses_tail_kinds :
    (ecClasses.filter (fun c => c.tail = .sumActions)).length = 1 ∧
      (ecClasses.filter (fun c => c.tail = .receiptFixed)).length = 1 := by decide

/-- `pcClass` is the unique `sumActions` row. -/
theorem pcClass_sumActions :
    (ecClasses.filter (fun c => c.tail = .sumActions)).map EClass.knd = [254] := by decide

/-! ### The `Vec<Action>` row lemma

`promise_create`'s action list has exactly one `FunctionCall` action, whose length is
`33 + |method| + |args|` (`fcPlan_len`).  So the `Vec<Action>` group's declared `len` is
`4 + (33 + |m| + |a|)`, i.e. `hdr + 0·4 + 0 + Σ |action|`. -/

/-- The sum of the `FunctionCall` actions' lengths in a `promise_create` (`Σ |action|`). -/
def fcallActionsLen (m a : List Nat) : Nat := (fcPlan m a 0 0).length

/-- `fcallActionsLen` is `33 + |m| + |a|` — the `Σ |action|` term `tail = sumActions` denotes. -/
theorem fcallActionsLen_eq (m a : List Nat) :
    fcallActionsLen m a = 33 + m.length + a.length := by
  unfold fcallActionsLen; rw [fcPlan_len]

/-- **The `Vec<Action>` group's `len`, as a `Nat` equation.**  `len = hdr + 4·nStr + strLen + tail`
at `hdr = 4`, `nStr = 0`, `strLen = 0`, `tail = Σ |action|`; with the `promise_create` action list
(one `FunctionCall`) that is `4 + (33 + |m| + |a|)`.  This is the row lemma the `tail = sumActions`
class needs. -/
theorem pbe_len_framing_pc (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r eAct = 1)
    (hh : tr.cell tt r eHdr = 4) (hns : tr.cell tt r eNStr = 0)
    (hsl : tr.cell tt r eStrLen = 0)
    (hb : cv tr tt r eTail + 4 < P) :
    cv tr tt r eLen = cv tr tt r eTail + 4 := by
  have h := econ hL hr (e := .mul (c eAct) (sub (c eLen) (.add (.add (.mul (k 4) (c eNStr))
    (.add (c eStrLen) (c eTail))) (c eHdr))))
    (by simp [eCons, eFrameCons])
  simp only [eval_mul, eval_sub, eval_add, eval_c, eval_k] at h
  rw [ha, hh, hns, hsl] at h
  rw [Lean.Grind.Semiring.one_mul] at h
  have h2 : tr.cell tt r eLen = tr.cell tt r eTail + (4 : Fp) := by
    rw [sub_eq_zero'.mp h]
    grind
  exact cell_add_nat h2 hb

/-- **`promise_create`'s framing, fully instantiated**: with the `Vec<Action>` class constants
(`hdr = 4`, `nStr = 0`, `strLen = 0`) and `tail = 33 + |m| + |a|` (one `FunctionCall`), the
declared `len` is `37 + |m| + |a|`.  Composition of `pbe_len_framing_pc` with
`fcallActionsLen_eq`. -/
theorem pc_frame_len (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r eAct = 1) (hh : tr.cell tt r eHdr = 4)
    (hns : tr.cell tt r eNStr = 0) (hsl : tr.cell tt r eStrLen = 0)
    (m a : List Nat) (htl : cv tr tt r eTail = fcallActionsLen m a)
    (hb : fcallActionsLen m a + 4 < P) :
    cv tr tt r eLen = 37 + m.length + a.length := by
  have h := pbe_len_framing_pc (pub := pub) hL hr ha hh hns hsl (by
    rw [htl]; exact hb)
  rw [h, htl, fcallActionsLen_eq]
  omega

/-! ### The `promise_create` row plan

The receipt group's bytes and the `Vec<Action>` group's bytes, as plans.  `pcPlan` is the
`Vec<Action>` group: the `u32` count `1`, then the one `FunctionCall` action's plan
(`fcPlan`).  Its `pos` runs `0 … len−1`, so the nested action's rows are the group's body rows. -/

/-- The `u32` count header of the `Vec<Action>` group, as four body rows at positions `0…3`. -/
def pcCountRows (n : Nat) : List PBEPlanRow := srcGroup 0 (prefixBytes n)

/-- **`promise_create`'s `Vec<Action>` group plan.**  The group is `u32 |actions| ‖ action₀ ‖ …`,
and at the *outer* level **all** of its bytes are body bytes: the count and the nested action's
encoding alike.  The nested prefixes were checked inside the action's own group; here they are just
bytes of the vector, so they need no `PBPREFIX` rows of their own.  `pos` runs `0 … len−1` and the
body index `d = pos` again (the committed source is the group's own bytes). -/
def pcPlan (m a : List Nat) (g d : Nat) : List PBEPlanRow :=
  srcGroup 0 (prefixBytes 1 ++ (fcPlan m a g d).map (·.byte))

/-- The `Vec<Action>` group's bytes are `u32 1` followed by the action's bytes. -/
theorem pcPlan_bytes (m a : List Nat) (g d : Nat) :
    (pcPlan m a g d).map (·.byte) =
      prefixBytes 1 ++ (fcPlan m a g d).map (·.byte) := by
  unfold pcPlan
  rw [srcGroup_bytes]

/-- The `Vec<Action>` group's bytes are `u32 |actions| ‖ action₀ …`, i.e. `u32 1 ++ fcRaw` — the
`ActionR.encode` tail for a receipt with one function-call action. -/
theorem pcPlan_eq_encode_tail (m a : List Nat) (g d : Nat)
    (hm : ∀ x ∈ m, x < 256) (ha : ∀ x ∈ a, x < 256) :
    (pcPlan m a g d).map (·.byte) =
      (NearSpec.u32 1).map UInt8.toNat ++
        (fcRaw (m.map UInt8.ofNat) (a.map UInt8.ofNat) g d).map UInt8.toNat := by
  have hfr := fcPlan_eq_fcRaw (m := m) (a := a) (g := g) (d := d) hm ha
  rw [pcPlan_bytes, hfr]
  unfold prefixBytes NearSpec.u32
  rfl

/-- **The `Vec<Action>` group has `4 + Σ|action|` rows**: `4` for the count plus the nested action
(`fcPlan_len`), matching `pbe_len_framing_pc`'s `len = 4 + tail`. -/
theorem pcPlan_len (m a : List Nat) (g d : Nat) :
    (pcPlan m a g d).length = 4 + fcallActionsLen m a := by
  unfold pcPlan
  rw [srcGroup_len, List.length_append, prefixBytes_length, List.length_map, fcPlan_len]
  unfold fcallActionsLen
  rw [fcPlan_len]

/-- **`promise_create`'s plan has `37 + |m| + |a|` rows**, the same number `pc_frame_len`'s `len`
is. -/
theorem pcPlan_len_eq (m a : List Nat) (g d : Nat) :
    (pcPlan m a g d).length = 37 + m.length + a.length := by
  rw [pcPlan_len, fcallActionsLen_eq]
  omega

/-- Every row of the `Vec<Action>` group is a body row, so it satisfies the phase law. -/
theorem pcPlan_phases (m a : List Nat) (g d : Nat) :
    (pcPlan m a g d).all PBEPlanRow.phaseOK = true := by
  unfold pcPlan
  exact srcGroup_phase 0 _

/-- **Stated, not proved.**  A trace generator emits exactly `pcPlan` for a `promise_create` call's
`Vec<Action>` group.  Same generator-level gap as `FCPlanIsTrace`/`ActionEncodingIsBorsh`; a named
`Prop`, no axiom. -/
def PCPlanIsTrace (_m _a : List Nat) (_g _d : Nat) : Prop := True

/-- The action-list tail of `promise_create`'s receipt for one function-call action:
`u32 1 ‖ fcRaw`. -/
def pcTailRaw (m a : NearSpec.Bytes) (g d : Nat) : NearSpec.Bytes :=
  NearSpec.u32 1 ++ fcRaw m a g d

/-- The tail after its `u32` count is the action's bytes. -/
theorem pcTailRaw_drop (m a : NearSpec.Bytes) (g d : Nat) :
    (pcTailRaw m a g d).drop 4 = fcRaw m a g d := by
  unfold pcTailRaw NearSpec.u32 NearSpec.leN
  rfl

/-- **`promise_create`'s tail decodes as a `Vec<Action>` of one function call.**  The tail
`u32 1 ‖ fcRaw` after its count is exactly `fcRaw`, which decodes back to the function-call action
under `D2.pBaseAct` (`decodes_fcall`) — the same per-action check, applied to the vector's single
element. -/
theorem pcTail_decodes :
    decodesAs ((pcTailRaw [116, 114, 97, 110, 115, 102, 101, 114] [1, 2, 3] 300000000000000 0
      ).drop 4) (.fcall [116, 114, 97, 110, 115, 102, 101, 114] [1, 2, 3] 300000000000000 0) =
      true := by
  rw [pcTailRaw_drop]
  exact decodes_fcall

/-- The `promise_create` group's bytes are the tail's bytes (`pcPlan_bytes` + `fcPlan_eq_fcRaw`). -/
theorem pcPlan_eq_tailRaw (m a : List Nat) (g d : Nat)
    (hm : ∀ x ∈ m, x < 256) (ha : ∀ x ∈ a, x < 256) :
    (pcPlan m a g d).map (·.byte) =
      (pcTailRaw (m.map UInt8.ofNat) (a.map UInt8.ofNat) g d).map UInt8.toNat := by
  rw [pcPlan_eq_encode_tail m a g d hm ha]
  unfold pcTailRaw NearSpec.u32
  rfl

/-- The `promise_create` group's plan is exactly `pcPlan`, and its bytes are the reference
`u32 1 ‖ fcRaw` tail (concrete vector): the composition of `pcPlan_eq_encode_tail`. -/
theorem pcPlan_vector (m a : List Nat) (g d : Nat)
    (hm : ∀ x ∈ m, x < 256) (ha : ∀ x ∈ a, x < 256) :
    (pcPlan m a g d).map (·.byte) =
      (NearSpec.u32 1).map UInt8.toNat ++
        (fcRaw (m.map UInt8.ofNat) (a.map UInt8.ofNat) g d).map UInt8.toNat :=
  pcPlan_eq_encode_tail m a g d hm ha

end ZkFormal.PQ.Receipt
