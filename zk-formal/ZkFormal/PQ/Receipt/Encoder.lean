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



inductive BField where
  | str (bs : List Nat)
  | u64 (v : Nat)
  | u128 (v : Nat)
  deriving DecidableEq, Repr

def BField.len : BField → Nat
  | .str bs => 4 + bs.length
  | .u64 _ => 8
  | .u128 _ => 16

def BField.bytes : BField → List Nat
  | .str bs => prefixBytes bs.length ++ bs
  | .u64 v => (NearSpec.u64 v).map UInt8.toNat
  | .u128 v => (NearSpec.u128 v).map UInt8.toNat

theorem BField.bytes_length (f : BField) : f.bytes.length = BField.len f := by
  cases f with
  | str bs => simp [BField.bytes, BField.len, prefixBytes_length]
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

width 15. -/

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
def eWidth : Nat := 15

def eBits : List Expr := [eAct, eF, eSelTag, eSelBody].map (fun x => bool (c x))

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
    .mul (sub (k 1) (n eF)) (sub (n ePos) (.add (c ePos) (k 1))) ]

def eLenCons : List Expr :=
  [ .mul (c eAct) (sub (c eLen) (.add (c ePos) (.add (c eGap) (k 1)))),
    mul3 (n eF) (c eAct) (sub (c eLen) (.add (c ePos) (k 1))) ]

/-- **The framing identity**: `len = 1 + 4·nStr + strLen + tail`.  For `TR` that is `17`, for `DA`
`5 + |beneficiary|`, for `FC` `33 + |method| + |args|`.  `nStr` and `tail` are per-class constants
(like `knd`), so one constraint covers the whole family (`tr_frame_len`/`da_frame_len`/
`fc_frame_len`). -/
def eFrameCons : List Expr :=
  [ .mul (c eAct) (sub (c eLen) (.add (.add (.mul (k 4) (c eNStr))
      (.add (c eStrLen) (c eTail))) (k 1))) ]

def ePhaseCons : List Expr :=
  [ .mul (c eAct) (sub (.add (c eSelTag) (c eSelBody)) (k 1)),
    .mul (c eSelTag) (c ePos),
    .mul (c eSelBody) (sub (sub (c ePos) (k 5)) (c eD)),
    .mul (sub (k 1) (c eSelBody)) (c eD),
    .mul (c eSelTag) (sub (c eByte) (c eKnd)) ]

def eCons : List Expr := eBits ++ eGroupCons ++ eLenCons ++ eFrameCons ++ ePhaseCons

def B_PBSRC : Nat := 214
def B_PBPREFIX : Nat := 213
def eMsg : List Expr := [c eTs, c eHid, .const 1, c ePos, c eByte]
def eSrcMsg : List Expr := [c eTs, c eHid, c eD, c eByte]
def ePreMsg : List Expr := [c eTs, c eHid, c eStrLen, c ePos, c eByte]

def eInters : List Interaction :=
  [ { bus := ZkFormal.PQ.Join.B_HOSTB, send := true, mult := [c eAct], msg := eMsg },
    { bus := B_PBSRC, send := false, mult := [c eSelBody], msg := eSrcMsg },
    { bus := B_PBPREFIX, send := false,
      mult := [sub (sub (k 1) (c eSelTag)) (c eSelBody)], msg := ePreMsg },
    { bus := B_PBRANGE, send := false, mult := [c eAct], msg := [c eGap] } ]

def etable : ZkFormal.Air.Table :=
  { width := eWidth, constraints := eCons, interactions := eInters, maxLog := 22 }

theorem pbe_shape : etable.width = 15 ∧ etable.constraints.length = 23 ∧
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

/-- **A group constant is the same on the next row.**  `ts`, `hid`, `len`, `knd`, `strLen` are
group-constant: unchanged from row `r` to `r+1` while `r+1` is inside the group (`f = 0`). -/
theorem pbe_const_step (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r + 1 < tr.height tt)
    (hnf : tr.cell tt (r + 1) eF = 0) (x : Nat)
    (hx : x = eTs ∨ x = eHid ∨ x = eLen ∨ x = eKnd ∨ x = eStrLen ∨ x = eNStr ∨ x = eTail) :
    tr.cell tt (r + 1) x = tr.cell tt r x := by
  have hmem : .mul (sub (k 1) (n eF)) (sub (n x) (c x)) ∈ eCons := by
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
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

/-- **Framing lemma 3 (AIR side) — the group's `len` is `1 + 4·nStr + strLen + tail`.**  This is
the borsh framing identity exactly as the `PBE` row constrains it.  `tr_frame_len`/`da_frame_len`/
`fc_frame_len` show the three concrete instances. -/
theorem pbe_len_framing_general (hL : TableLocal etable tr tt pub) {r : Nat}
    (hr : r < tr.height tt) (ha : tr.cell tt r eAct = 1) :
    tr.cell tt r eLen = 4 * tr.cell tt r eNStr +
      (tr.cell tt r eStrLen + tr.cell tt r eTail) + 1 := by
  have h := econ hL hr (e := .mul (c eAct) (sub (c eLen) (.add (.add (.mul (k 4) (c eNStr))
    (.add (c eStrLen) (c eTail))) (k 1))))
    (by simp [eCons, eFrameCons])
  simp only [eval_mul, eval_sub, eval_add, eval_c, eval_k] at h
  rw [ha] at h
  have h3 : tr.cell tt r eLen - (4 * tr.cell tt r eNStr +
      (tr.cell tt r eStrLen + tr.cell tt r eTail) + 1) = 0 := by
    have h1 : ((1 : Fp)) * (tr.cell tt r eLen - (4 * tr.cell tt r eNStr +
        (tr.cell tt r eStrLen + tr.cell tt r eTail) + 1)) = 0 := h
    rwa [Lean.Grind.Semiring.one_mul] at h1
  exact sub_eq_zero'.mp h3

/-- **The `TR` instance of the framing identity, as a `Nat` equation.**  From the row's constraint
with `nStr = 0`, `strLen = 0`, `tail = 16`, the declared `len` is `17` — the reference `trRaw`'s
length.  This is the framing lemma a receipt-side reader uses. -/
theorem pbe_len_framing_tr (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r eAct = 1)
    (hns : tr.cell tt r eNStr = 0) (hsl : tr.cell tt r eStrLen = 0)
    (htl : tr.cell tt r eTail = 16) (_hb : 17 < P) :
    cv tr tt r eLen = 17 := by
  have h := econ hL hr (e := .mul (c eAct) (sub (c eLen) (.add (.add (.mul (k 4) (c eNStr))
    (.add (c eStrLen) (c eTail))) (k 1))))
    (by simp [eCons, eFrameCons])
  simp only [eval_mul, eval_sub, eval_add, eval_c, eval_k] at h
  rw [ha, hns, hsl, htl] at h
  rw [Lean.Grind.Semiring.one_mul] at h
  have h2 : tr.cell tt r eLen = (17 : Fp) := by
    rw [sub_eq_zero'.mp h]
    decide
  have h17 := congrArg Fp.toNat h2
  have h17' : Fp.toNat (17 : Fp) = 17 := by decide
  rw [h17'] at h17
  simpa [cv] using h17

/-- **The `DA` instance**: `nStr = 1`, `tail = 0`, so the declared `len` is `5 + strLen`. -/
theorem pbe_len_framing_da (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r eAct = 1)
    (hns : tr.cell tt r eNStr = 1) (htl : tr.cell tt r eTail = 0)
    (hb : cv tr tt r eStrLen + 5 < P) :
    cv tr tt r eLen = cv tr tt r eStrLen + 5 := by
  have h := econ hL hr (e := .mul (c eAct) (sub (c eLen) (.add (.add (.mul (k 4) (c eNStr))
    (.add (c eStrLen) (c eTail))) (k 1))))
    (by simp [eCons, eFrameCons])
  simp only [eval_mul, eval_sub, eval_add, eval_c, eval_k] at h
  rw [ha, hns, htl] at h
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

theorem pbe_phase (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r eAct = 1)
    (hb : cv tr tt r eSelTag + cv tr tt r eSelBody + 1 < P) :
    cv tr tt r eSelTag + cv tr tt r eSelBody = 1 := by
  have h := econ hL hr (e := .mul (c eAct) (sub (.add (c eSelTag) (c eSelBody)) (k 1)))
    (by simp [eCons, ePhaseCons])
  simp only [eval_mul, eval_sub, eval_add, eval_c, eval_k] at h
  rw [ha, Lean.Grind.Semiring.one_mul] at h
  have h2 : tr.cell tt r eSelTag + tr.cell tt r eSelBody = (1 : Fp) := sub_eq_zero'.mp h
  have h4 := congrArg Fp.toNat h2
  rw [ZkFormal.Algebra.Fp.add_def, Fp.toNat_add] at h4
  have h1 : Fp.toNat (1 : Fp) = 1 := by decide
  rw [h1] at h4
  simp only [cv] at hb ⊢
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

theorem pbe_body_pos (hL : TableLocal etable tr tt pub) {r : Nat} (hr : r < tr.height tt)
    (hs : tr.cell tt r eSelBody = 1)
    (hb : cv tr tt r eD + 5 < P) : cv tr tt r ePos = cv tr tt r eD + 5 := by
  have h := econ hL hr (e := .mul (c eSelBody) (sub (sub (c ePos) (k 5)) (c eD)))
    (by simp [eCons, ePhaseCons])
  simp only [eval_mul, eval_sub, eval_c, eval_k] at h
  rw [hs, Lean.Grind.Semiring.one_mul] at h
  have h2 : tr.cell tt r ePos = tr.cell tt r eD + (5 : Fp) := by
    grind
  exact cell_add_nat h2 hb

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

end ZkFormal.PQ.Receipt
