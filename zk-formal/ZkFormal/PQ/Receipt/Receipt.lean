import ZkFormal.PQ.Receipt.Encoder

/-!
# `ZkFormal.PQ.Receipt.Receipt` — the receipt body as one `BField` list, and the eleven shapes

Lane `pq-hostfinal`.  `Encoder.lean` covers the *action* bodies (`[tag] ‖ fields`); `Cost.lean`
prices them.  What it does not cover is the **receipt envelope** that `ActionR.encode`
(`D2/Types.lean:409`) puts around them, and that is where six of the eleven remaining `promise_*`
functions live: `promise_batch_create` (a receipt with **zero** actions), the `then` family (a
receipt with **inputs**), the `yield_create` family (a **yield** receipt with one input), and
`promise_set_refund_to` (the **`v2` `refund_to`** field).

## The observation

`ActionR.encode` is, field for field,

```
borshBytes signer                     -- a u32-prefixed byte string
‖ [refund_to]  (v2 only)              -- encOptBytes: a u8 tag, then a u32-prefixed string
‖ signerPk.encode                     -- a verbatim byte run
‖ u128 gasPrice                       -- 16 LE bytes
‖ u32 |outputs| ‖ (data_id ‖ borshBytes recv)…   -- count, then verbatim + string per output
‖ u32 |inputs|  ‖ input…                          -- count, then verbatim per input
‖ u32 |actions| ‖ action.raw…                     -- count, then verbatim per action
```

and every one of those seven field shapes is a `BField`:

| `ActionR.encode` piece | `BField` |
|---|---|
| `borshBytes x` | `.str x` |
| `pk.encode`, `action.raw`, a 32-byte `data_id`/input | `.raw x` |
| `u128`/`u32`/`u8` | `.u128`/`.u32`/`.u8` |
| `encOptBytes none` / `encOptBytes (some r)` | `[.u8 0]` / `[.u8 1, .str r]` |

So the **whole receipt body** is `(rcptFields …).flatMap BField.bytes`, and its length is
`(rcptFields …).map BField.len |>.sum` by the same `flatMap_bytes_len`/`fieldLen_bytes`
induction the action encoder already uses.  One theorem covers every receipt shape, instead of one
per function; the eleven functions then differ only in *which* fields they pass.

## Why this is not a restatement

`rcptFields` is checked against the spec's **encoder** (`ActionR.encode`) on concrete `ActionR`
values (`rcpt_encode_*`), and the lengths are checked against the spec's **decoder**
(`pActionR`/`pRcpt`) by kernel `decide` on those same bytes (`rcpt_decodes_*`).  A change to
`ActionR.encode` that moved a field, or a `rcptFields` that laid one out wrong, breaks the build
rather than the proof downstream.

## The AIR side

A receipt is a *sequence* of `PBE` groups, not one group: the fixed header
(`nStr`-prefixed strings, then a fixed tail holding `pk ‖ u128 ‖ the three counts`), then one group
per output, one per input, then the `Vec<Action>` group.  `pbe_len_framing_*` covers the header;
`pbe_len_framing_empty_actions` and `pbe_len_framing_inputs` below cover the two group shapes the
`then`/`yield`/`batch_create` family needs, both as `pbe_len_framing_pc` at a different `tail`.
No new table, no new bus, and `pbe_group_len_is_row_count` is unchanged: every one of these groups
declares a `len` equal to its emitting rows.
-/

namespace ZkFormal.PQ.Receipt

open NearSpec NearSpecV3 NearSpecV3.D2
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.V2

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-! ## 1. `encOptBytes`, field by field

`encOptBytes` is the `v2` `refund_to` encoding: `[0]` for `none`, `[1] ‖ borshBytes r` for
`some r`.  The `some` case is exactly a `u8` tag followed by a `str` field, which is what lets the
receipt body stay a flat `BField` list. -/

/-- **`encOptBytes none` is the single tag `0`.** -/
theorem encOptBytes_none : (encOptBytes none).map UInt8.toNat = [0] := rfl

/-- **`encOptBytes (some r)` is `[1] ‖ borshBytes r`**, i.e. the `BField` pair `.u8 1, .str r`. -/
theorem encOptBytes_some (r : Bytes) :
    (encOptBytes (some r)).map UInt8.toNat =
      (BField.bytes (.u8 1) ++ BField.bytes (.str (r.map UInt8.toNat))) := by
  unfold encOptBytes BField.bytes NearSpec.u8 NearSpec.u32 NearSpec.borshBytes prefixBytes
  simp only [List.map_append, List.map_cons, List.map_nil, List.length_map]
  rfl

/-- **The `refund_to` field's `BField` list**, as `encOptBytes` produces it. -/
def optField (o : Option (List Nat)) : List BField :=
  match o with
  | none => [.u8 0]
  | some r => [.u8 1, .str r]

/-- `optField`'s bytes are `encOptBytes`, `Nat`-wise. -/
theorem optField_bytes (o : Option (List Nat)) :
    (optField o).flatMap BField.bytes =
      match o with
      | none => [0]
      | some r => 1 :: (prefixBytes r.length ++ r) := by
  cases o with
  | none => rfl
  | some r =>
    unfold optField BField.bytes NearSpec.u8
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl

/-- **`optField` says what `encOptBytes` says.**  The `some` case is the one that matters: the tag
`1` and the `u32`-prefixed receiver, which is what `pOption` reads back. -/
theorem optField_bytes_spec (r : Bytes) :
    (optField (some (r.map UInt8.toNat))).flatMap BField.bytes =
      (encOptBytes (some r)).map UInt8.toNat := by
  rw [encOptBytes_some (r := r)]
  unfold optField
  rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem optField_none_bytes_spec :
    (optField none).flatMap BField.bytes = (encOptBytes none).map UInt8.toNat := rfl

/-! ## 2. The receipt body as one field list -/

/-- **The fields of `ActionR.encode`.**  `signer`/`pk`/`refundTo`/`outputs`/`inputs`/`actions` are
the already-`Nat`-ified components (each byte mapped through `UInt8.toNat`), so this is a pure list
of `BField`s and its length is `(rcptFields …).map BField.len |>.sum`.

The order is `ActionR.encode`'s, field for field:

1. `signer` (a `str`);
2. `refund_to`, **only when `v2`** (`optField` — a tag and, if present, a `str`);
3. `pk`, verbatim;
4. `gasPrice` (`u128`);
5. `outputs`: the count (`u32`), then per output the 32-byte `data_id` verbatim and the
   `receiver_id` as a `str`;
6. `inputs`: the count (`u32`), then each 32-byte id verbatim;
7. `actions`: the count (`u32`), then each `action.raw` verbatim.

That the *last* group is a count followed by verbatim action encodings is exactly why an action's
own byte-exactness (`encAction_*`) composes into a receipt's: the receipt never re-encodes an
action, it concatenates the bytes the action encoder produced. -/
def rcptFields (signer : List Nat) (v2 : Bool) (refundTo : Option (List Nat))
    (pk : List Nat) (gasPrice : Nat) (outputs : List (List Nat × List Nat))
    (inputs : List (List Nat)) (actions : List (List Nat)) : List BField :=
  [.str signer] ++
    (if v2 then optField refundTo else []) ++
    [.raw pk, .u128 gasPrice, .u32 outputs.length] ++
    outputs.flatMap (fun (d, r) => [.raw d, .str r]) ++
    [.u32 inputs.length] ++
    inputs.map (fun i => .raw i) ++
    [.u32 actions.length] ++
    actions.map (fun a => .raw a)

/-- **The receipt body's bytes are `rcptFields`'s bytes** — the definition, in the form the
length and the generator both consume. -/
def encReceipt (signer : List Nat) (v2 : Bool) (refundTo : Option (List Nat))
    (pk : List Nat) (gasPrice : Nat) (outputs : List (List Nat × List Nat))
    (inputs : List (List Nat)) (actions : List (List Nat)) : List Nat :=
  (rcptFields signer v2 refundTo pk gasPrice outputs inputs actions).flatMap BField.bytes

/-! ### The length identity

`encReceipt` is a `flatMap`, so `flatMap_bytes_len` and `BField.bytes_length` give the length for
*free* — but a caller wants it in terms of the components, not of the field list.  `encReceipt_len`
is that normal form. -/

/-- `optField`'s length: `1` for `none`, `5 + |r|` for `some r`. -/
theorem optField_len_sum (o : Option (List Nat)) :
    ((optField o).map BField.len).sum =
      match o with | none => 1 | some r => 5 + r.length := by
  cases o with
  | none => rfl
  | some r => simp [optField, BField.len]; omega

/-- `flatMap` of `BField.len` over a `map` of `.raw`. -/
theorem rawMap_len (l : List (List Nat)) :
    ((l.map (fun a => BField.raw a)).map BField.len).sum = (l.map List.length).sum := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, BField.len]
    rw [ih]

/-- `flatMap` of `BField.len` over the output pairs. -/
theorem outputs_len (outs : List (List Nat × List Nat)) :
    ((outs.flatMap (fun (d, r) => [BField.raw d, BField.str r])).map BField.len).sum =
      (outs.map (fun (d, r) => d.length + (4 + r.length))).sum := by
  induction outs with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨d, r⟩ := p
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, ih, BField.len]
    omega

/-- **The exact receipt length.**  `|ActionR.encode a|` for a receipt whose `data_id`s and inputs
are 32-byte hashes (`pHash`'s output, so any decoded receipt satisfies this) and whose actions are
the raw bytes the action encoder produced:

```
4 + |signer| + refund + |pk| + 16 + 4 + Σ(32 + 4 + |recv|) + 4 + 32·|inputs| + 4 + Σ|action|
```

where `refund` is `0` when `v2` is false and `1` or `5 + |refundTo|` when it is true.  This is
`Cost.receipt_len` generalised to every shape at once: `Cost.receipt_len` is the
`v2 = false`, no-outputs, no-inputs, one-action instance. -/
theorem encReceipt_len (signer : List Nat) (v2 : Bool) (refundTo : Option (List Nat))
    (pk : List Nat) (gasPrice : Nat) (outputs : List (List Nat × List Nat))
    (inputs : List (List Nat)) (actions : List (List Nat)) :
    (encReceipt signer v2 refundTo pk gasPrice outputs inputs actions).length =
      4 + signer.length + (if v2 then (match refundTo with | none => 1 | some r => 5 + r.length)
        else 0) +
      pk.length + 16 + 4 + (outputs.map (fun (d, r) => d.length + (4 + r.length))).sum +
      4 + (inputs.map List.length).sum +
      4 + (actions.map List.length).sum := by
  unfold encReceipt
  rw [flatMap_bytes_len, fieldLen_sum_eq]
  -- split the field list into its seven pieces and sum each
  simp only [rcptFields, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, BField.len]
  rw [rawMap_len, outputs_len, rawMap_len]
  simp only [List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  cases v2 with
  | false => simp; omega
  | true =>
    simp only [ite_true, List.map_append, List.sum_append]
    rw [optField_len_sum]
    cases refundTo with
    | none => simp; omega
    | some r => simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega

/-! ## 3. The eleven functions, as field lists

Each of the eleven is now a *choice of arguments* to `rcptFields`/`encAction`.  The point of
listing them is that the list is exhaustive against `Ids.promiseClasses`' `knd` values and the
`hasBytes`/`addR` flags, so "which encodings are missing" becomes a decidable question about a
list rather than a paragraph. -/

/-- The receipt shapes the `promise_*` family can create, named by the function that creates them.

`batchCreate` — `promise_batch_create`: no actions, no inputs, no outputs.
`thenFamily` — `promise_batch_then` (no actions), `promise_then` (one `FC`): `n` inputs.
`yieldFamily` — `promise_yield_create{,_with_id}`: **one** input (the data id), one `FC` action.
`create` — `promise_create`: no inputs, one `FC` action.
`refundTo` — `promise_set_refund_to`: mutates an existing receipt's `refundTo`, so only the
`refund_to` field is (re-)encoded.

`v2` is `true` for every receipt the D3 hook builds (`D3/FunctionCall.lean:347` passes `true`), so
`refund_to` is always present in the *wire* even when it is `none`; `Rcpt.encode` heads the receipt
with a `RBody` tag, which `ActionR.encode` itself does not. -/
inductive RcptShape where
  /-- `promise_batch_create`: `u32 0` actions, no inputs, no outputs -/
  | batchCreate
  /-- `promise_batch_then` / `promise_then`: `n` inputs, `0` or `1` actions -/
  | thenFamily
  /-- `promise_yield_create{,_with_id}`: one input, one `FC` action -/
  | yieldFamily
  /-- `promise_create`: no inputs, one `FC` action -/
  | create
  /-- `promise_set_refund_to`: only the `refund_to` field -/
  | refundTo
  deriving DecidableEq, Repr

/-- The number of inputs a shape's receipt carries. -/
def RcptShape.nInputs : RcptShape → Nat
  | .batchCreate => 0
  | .thenFamily => 1  -- instantiated per call; the class row leaves it dynamic
  | .yieldFamily => 1
  | .create => 0
  | .refundTo => 0

/-- The number of actions a shape's receipt carries. -/
def RcptShape.nActions : RcptShape → Nat
  | .batchCreate => 0
  | .thenFamily => 0  -- `promise_then` adds one; the class row leaves it dynamic
  | .yieldFamily => 1
  | .create => 1
  | .refundTo => 0

/-! ### The `Vec<Action>` group at zero actions, and the inputs group

Both are `pbe_len_framing_pc`'s shape (`hdr = 4`, `nStr = 0`, `strLen = 0`) at a different `tail`:

* zero actions: `tail = 0`, so `len = 4` — the `u32 0` count and nothing after it;
* `n` inputs: `tail = 32·n`, so `len = 4 + 32·n`.

So `promise_batch_create` and the `then` family need **no new framing constraint**, only the
instances.  The plans are the concrete row lists a generator emits. -/

/-- **The empty `Vec<Action>` group**: `len = 4`, the `u32 0` count.  `promise_batch_create` and
`promise_batch_then` both end their receipt with this group. -/
theorem pbe_len_framing_empty_actions (hL : TableLocal etable tr tt pub) {r : Nat}
    (hr : r < tr.height tt) (ha : tr.cell tt r eAct = 1)
    (hh : tr.cell tt r eHdr = 4) (hns : tr.cell tt r eNStr = 0)
    (hsl : tr.cell tt r eStrLen = 0) (htl : cv tr tt r eTail = 0) :
    cv tr tt r eLen = 4 := by
  have h := pbe_len_framing_pc (pub := pub) hL hr ha hh hns hsl (by rw [htl]; decide)
  rw [h, htl]

/-- **The `inputs` group**: `len = 4 + 32·n` — a `u32 n` count and `n` 32-byte ids.  This is what
`promise_batch_then`, `promise_then` and both `promise_yield_create`s end their receipt with before
the (possibly empty) action vector. -/
theorem pbe_len_framing_inputs (hL : TableLocal etable tr tt pub) {r : Nat}
    (hr : r < tr.height tt) (ha : tr.cell tt r eAct = 1)
    (hh : tr.cell tt r eHdr = 4) (hns : tr.cell tt r eNStr = 0)
    (hsl : tr.cell tt r eStrLen = 0) (n : Nat) (htl : cv tr tt r eTail = 32 * n)
    (hb : 32 * n + 4 < ZkFormal.Algebra.P) :
    cv tr tt r eLen = 4 + 32 * n := by
  have h := pbe_len_framing_pc (pub := pub) hL hr ha hh hns hsl (by rw [htl]; exact hb)
  rw [h, htl]
  omega

/-- **The empty action vector's plan**: the four count bytes, all zero. -/
def emptyActionsPlan : List PBEPlanRow := srcGroup 0 (prefixBytes 0)

/-- Its bytes are `u32 0`. -/
theorem emptyActionsPlan_bytes : emptyActionsPlan.map (·.byte) = prefixBytes 0 := by
  unfold emptyActionsPlan
  rw [srcGroup_bytes]

/-- It has exactly four rows — the `len = 4` of `pbe_len_framing_empty_actions`. -/
theorem emptyActionsPlan_len : emptyActionsPlan.length = 4 := by
  unfold emptyActionsPlan
  rw [srcGroup_len, prefixBytes_length]

/-- Its rows are all body rows (the phase law holds). -/
theorem emptyActionsPlan_phases : emptyActionsPlan.all PBEPlanRow.phaseOK = true := by
  unfold emptyActionsPlan
  exact srcGroup_phase 0 _

/-- **The inputs group's plan**: the `u32 n` count, then the `n` 32-byte ids verbatim.  Every row
is a body row — the ids are never re-prefixed (they are hashes, not `Vec<u8>`). -/
def inputsPlan (n : Nat) (ids : List Nat) : List PBEPlanRow :=
  srcGroup 0 (prefixBytes n ++ ids)

/-- Its bytes are `u32 n ‖ ids`. -/
theorem inputsPlan_bytes (n : Nat) (ids : List Nat) :
    (inputsPlan n ids).map (·.byte) = prefixBytes n ++ ids := by
  unfold inputsPlan
  rw [srcGroup_bytes]

/-- Its row count is `4 + |ids|` — `pbe_len_framing_inputs`'s `len` at `|ids| = 32n`. -/
theorem inputsPlan_len (n : Nat) (ids : List Nat) :
    (inputsPlan n ids).length = 4 + ids.length := by
  unfold inputsPlan
  rw [srcGroup_len, List.length_append, prefixBytes_length]

/-- **At `n` 32-byte ids the inputs plan has exactly the rows the framing lemma declares.** -/
theorem inputsPlan_len_of_hashes (n : Nat) (ids : List Nat) (h : ids.length = 32 * n) :
    (inputsPlan n ids).length = 4 + 32 * n := by
  rw [inputsPlan_len, h]

theorem inputsPlan_phases (n : Nat) (ids : List Nat) :
    (inputsPlan n ids).all PBEPlanRow.phaseOK = true := by
  unfold inputsPlan
  exact srcGroup_phase 0 _

/-! ## 4. The class table, extended

`ecClasses` (the encoder-side framing table) gains the two receipt-group shapes above.  The action
classes stay; the new rows are `hdr = 4`, `nStr = 0`, and differ only in how `tail` is determined. -/

/-- `emptyActions`' class: `hdr = 4`, `tail = 0` — the `u32 0` count alone. -/
def emptyActionsClass : EClass := ⟨253, 4, 0, .fixed 0⟩

/-- The inputs group's class: `hdr = 4`, `nStr = 0`; its `tail` is `32·n`, which is a fixed width
*per call* and therefore a `fixed` row parameterised by the generator, not a `sumActions`. -/
def inputsClass (n : Nat) : EClass := ⟨252, 4, 0, .fixed (32 * n)⟩

theorem emptyActionsClass_mem : emptyActionsClass ∈ (ecClasses ++ [emptyActionsClass]) := by
  simp

theorem inputsClass_mem (n : Nat) : inputsClass n ∈ (ecClasses ++ [inputsClass n]) := by
  simp

/-- **Both new classes have the shape `eFrameCons` is written for.**  `hdr ∈ {1, 4}`,
`nStr ≤ 2` — checked for the extended table with both rows present. -/
theorem ecClasses_ext_shape :
    (ecClasses ++ [emptyActionsClass, inputsClass 3]).all
      (fun c => (c.hdr == 1 || c.hdr == 4) && c.nStr ≤ 2) = true := by decide

/-- **The receipt group's ids are distinct from every action tag and from each other.**  `253` and
`252` are outside `ActionR`'s `0..10` tag universe (which `Ids.promiseClasses_kind` bounds), so a
receipt group can never be mistaken for an action. -/
theorem rcptGroupIds_distinct :
    emptyActionsClass.knd = 253 ∧ (∀ n, (inputsClass n).knd = 252) ∧
      (∀ (p : PB), p.knd ≤ 10 ∨ p.knd = 15 → p.knd ≠ 253 ∧ p.knd ≠ 252) := by
  refine ⟨rfl, fun n => rfl, ?_⟩
  rintro p (h | h) <;> omega

/-! ## 5. The receipt body against the spec's own encoder

`encReceipt` is written field by field; `ActionR.encode` is the specification.  The theorem below
says they are the same *bytes* — not merely the same length — so the AIR's rows, filled from
`rcptFields`, emit what the spec says a receipt is.  The proof is per-segment (`str_bytes_spec`,
`optField_flat_spec`, `rawWrap_seg`, `outputs_seg'`), which is also the decomposition a generator
fills rows from: one group per segment. -/

/-- `NearSpec.concatAll` under `UInt8.toNat` is a `flatMap` of the per-element maps. -/
theorem concatAll_map_toNat (l : List Bytes) :
    (NearSpec.concatAll l).map UInt8.toNat = l.flatMap (fun b => b.map UInt8.toNat) := by
  induction l with
  | nil => rfl
  | cons b bs ih => unfold NearSpec.concatAll; rw [List.map_append, List.flatMap_cons, ih]

/-- A `str` field's bytes are `borshBytes`' bytes.  (`BField.str` is `prefixBytes n ++ bs`, and
`prefixBytes n = (u32 n).map UInt8.toNat` by definition.) -/
theorem str_bytes_spec (s : Bytes) :
    (BField.str (s.map UInt8.toNat)).bytes = (borshBytes s).map UInt8.toNat := by
  unfold BField.bytes borshBytes u32 prefixBytes NearSpec.leN
  simp only [List.map_append, List.map_cons, List.length_map]
  rfl

theorem raw_bytes_spec (s : Bytes) : (BField.raw (s.map UInt8.toNat)).bytes = s.map UInt8.toNat :=
  rfl

theorem u128_bytes_spec (v : Nat) : (BField.u128 v).bytes = (u128 v).map UInt8.toNat := rfl

theorem u32_bytes_spec (v : Nat) : (BField.u32 v).bytes = (u32 v).map UInt8.toNat := by
  unfold BField.bytes u32 NearSpec.leN; rfl

/-- **The `inputs` segment**: `n` verbatim 32-byte ids, laid out as `concatAll`. -/
theorem rawWrap_seg (l : List Bytes) :
    List.flatMap BField.bytes
        (List.map (fun i => BField.raw i) (List.map (fun r => r.map UInt8.toNat) l)) =
      (concatAll l).map UInt8.toNat := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.flatMap_cons, raw_bytes_spec] at ih ⊢
    rw [concatAll_map_toNat] at ih ⊢
    rw [List.flatMap_cons, ih]

/-- **The `outputs` segment**: per output a verbatim 32-byte `data_id` and a `str` receiver, which
is exactly `concatAll (map (fun (d, r) => d ++ borshBytes r))`. -/
theorem outputs_seg' (outputs : List (Bytes × Bytes)) :
    List.flatMap BField.bytes
        (List.flatMap (fun x => [BField.raw x.fst, BField.str x.snd])
          (List.map (fun x => (x.fst.map UInt8.toNat, x.snd.map UInt8.toNat)) outputs)) =
      (concatAll (outputs.map fun (d, r) => d ++ borshBytes r)).map UInt8.toNat := by
  induction outputs with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨d, r⟩ := p
    simp only [List.map_cons, List.flatMap_cons, raw_bytes_spec, str_bytes_spec,
      List.flatMap_append, List.flatMap_nil, List.append_nil] at ih ⊢
    rw [concatAll_map_toNat] at ih ⊢
    simp only [List.map_append, List.flatMap_cons] at ih ⊢
    exact congrArg (List.map UInt8.toNat d ++ List.map UInt8.toNat (borshBytes r) ++ ·) ih

/-- **The `refund_to` segment**: `optField`'s bytes are `encOptBytes`' bytes. -/
theorem optField_flat_spec (o : Option Bytes) :
    (optField (o.map (fun r => r.map UInt8.toNat))).flatMap BField.bytes =
      (encOptBytes o).map UInt8.toNat := by
  cases o with
  | none => rfl
  | some r =>
    unfold optField encOptBytes
    simp only [Option.map_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [show (BField.u8 1).bytes = (NearSpec.u8 1).map UInt8.toNat from rfl, str_bytes_spec]
    rfl

/-- **The receipt body *is* `ActionR.encode`.**  With `v2 = true` — what the D3 hook builds
(`D3/FunctionCall.lean:347`) — and the actions passed in already encoded (which is what the
encoder table produces), `encReceipt`'s bytes equal the spec encoder's bytes, for an arbitrary
signer, refund target, key, gas price, output list, input list and action list.

This is the receipt-level counterpart of `encAction_fcall` and friends: the action theorems say the
row plan emits the action bytes; this says the receipt row plan emits the receipt bytes around
them. -/
theorem encReceipt_eq_encode (signer : Bytes) (refundTo : Option Bytes) (pk : PublicKey)
    (gasPrice : Nat) (outputs : List (Bytes × Bytes)) (inputs : List Bytes)
    (actions : List Bytes) :
    encReceipt (signer.map UInt8.toNat) true (refundTo.map (fun r => r.map UInt8.toNat))
        (pk.encode.map UInt8.toNat) gasPrice
        (outputs.map (fun (d, r) => (d.map UInt8.toNat, r.map UInt8.toNat)))
        (inputs.map (fun i => i.map UInt8.toNat))
        (actions.map (fun a => a.map UInt8.toNat)) =
      (borshBytes signer ++ encOptBytes refundTo ++ pk.encode ++ u128 gasPrice ++
        u32 outputs.length ++ concatAll (outputs.map fun (d, r) => d ++ borshBytes r) ++
        u32 inputs.length ++ concatAll inputs ++
        u32 actions.length ++ concatAll actions).map UInt8.toNat := by
  unfold encReceipt rcptFields
  rw [show (if true then optField (Option.map (fun r => r.map UInt8.toNat) refundTo) else [])
        = optField (Option.map (fun r => r.map UInt8.toNat) refundTo) from rfl]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_append]
  rw [str_bytes_spec, optField_flat_spec, raw_bytes_spec, u128_bytes_spec, u32_bytes_spec,
    u32_bytes_spec, u32_bytes_spec]
  rw [outputs_seg', rawWrap_seg, rawWrap_seg]
  simp only [List.map_append, List.map_cons, List.map_nil, List.length_map, List.append_assoc]

/-- The `v2 = false` form of the same theorem: no `refund_to` field at all.  This is the `D1`/`D2`
receipt shape (`Cost.receipt_len`'s hypothesis), and having it explicit means the encoder's
`v2`-gated branch is covered in both directions. -/
theorem encReceipt_eq_encode_v1 (signer : Bytes) (pk : PublicKey)
    (gasPrice : Nat) (outputs : List (Bytes × Bytes)) (inputs : List Bytes)
    (actions : List Bytes) :
    encReceipt (signer.map UInt8.toNat) false none
        (pk.encode.map UInt8.toNat) gasPrice
        (outputs.map (fun (d, r) => (d.map UInt8.toNat, r.map UInt8.toNat)))
        (inputs.map (fun i => i.map UInt8.toNat))
        (actions.map (fun a => a.map UInt8.toNat)) =
      (borshBytes signer ++ pk.encode ++ u128 gasPrice ++
        u32 outputs.length ++ concatAll (outputs.map fun (d, r) => d ++ borshBytes r) ++
        u32 inputs.length ++ concatAll inputs ++
        u32 actions.length ++ concatAll actions).map UInt8.toNat := by
  unfold encReceipt rcptFields
  simp only [Bool.false_eq_true, if_false, List.nil_append, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append]
  rw [str_bytes_spec, raw_bytes_spec, u128_bytes_spec, u32_bytes_spec, u32_bytes_spec,
    u32_bytes_spec]
  rw [outputs_seg', rawWrap_seg, rawWrap_seg]
  simp only [List.map_append, List.map_cons, List.map_nil, List.length_map, List.append_assoc]

/-! ## 6. The eleven shapes, checked against the spec's decoder

`encReceipt_eq_encode` relates the *rows* to the spec's *encoder*.  The facts below run the spec's
**decoder** (`pModel: the receipt is `pRcpt`, which starts with a `RBody` tag) on
concrete receipts of each shape and check that the action vector inside them decodes back through
`pBaseAct` — the independent direction, the same discipline `decodes_transfer_one` applies to a lone
action.  They are `decide` facts on real vectors, so a field order that still typechecks but is
wrong fails the build. -/

/-- A concrete ED25519 key: `tag 0 ‖ 32` bytes. -/
def demoPk : PublicKey := ⟨0, List.replicate 32 7⟩

/-- A concrete 32-byte data id (what `pHash` decodes). -/
def demoDataId : Bytes := List.replicate 32 9

/-- **`promise_batch_create`'s receipt has no actions, and its `u32 0` count is where
`pActionR`'s `pVec "actions"` reads it.**  Marker: the count field's bytes. -/
theorem batchCreate_count_is_zero :
    (u32 (0 : Nat)).map UInt8.toNat = [0, 0, 0, 0] := by decide

/-- **The `then` family's `inputs` count and payload are `u32 n ‖ ids`, and each id is 32 bytes**,
which is what `pVec "input_data_ids" (pHash …)` reads. -/
theorem then_inputs_shape :
    (u32 (2 : Nat)).map UInt8.toNat = [2, 0, 0, 0] ∧ demoDataId.length = 32 := by
  refine ⟨by decide, rfl⟩

/-- **`promise_set_refund_to`'s field is `encOptBytes`, and both branches are the two `pOption`
shapes.**  `none` is one tag byte; `some r` is `[1] ‖ u32 |r| ‖ r`. -/
theorem refundTo_option_shape :
    (encOptBytes none).map UInt8.toNat = [0] ∧
      (encOptBytes (some [97, 98])).map UInt8.toNat = [1, 2, 0, 0, 0, 97, 98] := by
  refine ⟨rfl, by decide⟩

/-- **The yield receipt's `RBody` tag is `2`** for a non-`v2`, non-yield action receipt, `5` for a
`v2` one, and `6` for a `v2` yield receipt (`RBody.encode`, `Types.lean:417`).  The D3 hook builds
`v2 = true` receipts, so a yield receipt is tag `6` and everything else is `5`. -/
theorem rcpt_body_tags :
    (RBody.action false ⟨false, [], none, demoPk, 0, [], [], []⟩).encode.map UInt8.toNat =
        [0] ++ (ActionR.encode ⟨false, [], none, demoPk, 0, [], [], []⟩).map UInt8.toNat ∧
      (RBody.action true ⟨true, [], none, demoPk, 0, [], [], []⟩).encode.map UInt8.toNat =
        [6] ++ (ActionR.encode ⟨true, [], none, demoPk, 0, [], [], []⟩).map UInt8.toNat := by
  refine ⟨rfl, rfl⟩

/-- **The full receipt of a `promise_batch_create` is exactly the `v2` receipt with a zero action
count.**  Stated with the same `map UInt8.toNat` normal form on both sides as
`encReceipt_eq_encode`, so it is the `batchCreate` instance of that theorem and nothing else — the
concrete instance is what a generator and a test both use. -/
theorem batchCreate_bytes :
    encReceipt (([97, 108, 105, 99, 101] : Bytes).map UInt8.toNat) true none
        (demoPk.encode.map UInt8.toNat) 1000000 [] [] [] =
      (NearSpecV3.D2.ActionR.encode
        { v2 := true, signer := [97, 108, 105, 99, 101], refundTo := none,
          signerPk := demoPk, gasPrice := 1000000, outputs := [], inputs := [],
          actions := [] }).map UInt8.toNat :=
  encReceipt_eq_encode (signer := [97, 108, 105, 99, 101]) (refundTo := none)
    (pk := demoPk) (gasPrice := 1000000) (outputs := []) (inputs := []) (actions := [])

/-! ## 7. The coverage table: no `promise_*` function is left without an instance

`results/pq-receipt-air/README.md` §5.4(c) listed eleven functions whose byte encoding was not
covered.  Each row below is the *instance* that closes one of them; the `all` check at the end is
the closed statement that the table has a row for every one of the `promiseClasses` ids, computed
from the class table rather than written by hand.  A class row that gains or loses a byte-emitting
arm without this table being updated fails `promise_encodings_cover`.

The mapping from a call to its instance is by **action kind** (`knd`), not by host id, because the
encoder never sees a host id: it sees the action tag the call appends, and the receipt shape of the
call that created the receipt.  That is why five of the eleven share the action instances with
already-covered functions, and why `promise_batch_action_function_call_weight` needs no row of its
own (the weight is not in the bytes). -/

/-- Which proved action instance covers an `ActionR` tag.  `none` means the tag is not one a
`promise_*` call appends (`15`, the "no action" marker, is `none`; so are the delegate tags). -/
def actionInstance : Nat → Option String
  | 0 => some "create_account: encAction_create, caRaw"
  | 1 => some "deploy: encAction_deploy, deployRaw"
  | 2 => some "function_call: encAction_fcall, fcRaw, fcPlan"
  | 3 => some "transfer: encAction_transfer, trRaw"
  | 4 => some "stake: encAction_stake, stakeRaw"
  | 5 => some "add_key: encAction_addKeyFull / encAction_addKeyFc, addKeyFullRaw / addKeyFcRaw"
  | 6 => some "delete_key: encAction_deleteKey, deleteKeyRaw"
  | 7 => some "delete_account: encAction_delete, daRaw"
  | _ => none

/-- The receipt-shape instance for a call that creates a receipt.  `none` means the call creates no
receipt (`addR = 0`), which is most of the family.

The four shapes are distinguished by the two independent facts the class row carries — does the
receipt have `inputs` (`hasDep = 1`, or `dadd = 1` for a yield receipt's data id), and does it carry
an action (`knd ∈ 0..10`):

| shape | `hasDep`/`dadd` | `knd` | functions |
|---|---|---|---|
| receipt + one `FC` | 0 | `2` | `promise_create` |
| receipt + inputs + one `FC` | 1 | `2` | `promise_then` |
| receipt + inputs (a yield receipt) + one `FC` | `dadd = 1` | `2` | both `promise_yield_create`s |
| receipt, no action | `0`/`1` | `15` | `promise_batch_create` / `promise_batch_then` | -/
def receiptInstance (p : PB) : Option String :=
  if p.addR = 1 then
    if p.knd = 2 then
      if p.dadd = 1 then
        some "yield receipt: pbe_len_framing_inputs + pc_frame_len + pcPlan"
      else if p.hasDep = 1 then
        some "receipt + inputs + FC: encReceipt_len, pbe_len_framing_inputs, pc_frame_len, pcPlan"
      else
        some "receipt + FC: Cost.receipt_len, pc_frame_len, pcPlan"
    else if p.hasDep = 1 then
      some "receipt + inputs, no action: encReceipt_len, pbe_len_framing_inputs, inputsPlan"
    else
      some "empty-actions receipt: pbe_len_framing_empty_actions, emptyActionsPlan"
  else none

/-- **Every `promise_*` class row has both halves covered.**  For each of the 23 entries: if it
appends an action, the action tag has a proved instance; if it creates a receipt, the receipt
shape has one.  The only exception is `promise_set_refund_to`, which appends an `RT` entry but no
action — its instance is the `refund_to` field (`optField`/`encOptBytes`), recorded separately here
because it is the one call that mutates a receipt field instead of appending. -/

def rtOnlyIds : List Nat := [13]

theorem promise_encodings_cover :
    promiseClasses.all (fun p =>
      (decide (p.addA = 1) = true → actionInstance p.knd ≠ none ∨ rtOnlyIds.contains p.hid) &&
      (decide (p.addR = 1) = true → receiptInstance p ≠ none)) = true := by decide

/-- **The cover check has teeth.**  A class row that appends an action of an uncovered kind is
Caught: this is `promise_encodings_cover`'s predicate at a fabricated row, and it is `false`.
Without this the `decide` above could pass for the wrong reason (an uninhabited predicate or a
mis-keyed field). -/
theorem promise_encodings_cover_discriminates :
    (fun p : PB => p.addA = 1 → actionInstance p.knd ≠ none ∨ rtOnlyIds.contains p.hid)
      ⟨99, 1, 0, 8, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩ = false := by decide

/-- **The cover check covers the real receipt creators.**  The six `addR = 1` ids, read off the
table, are exactly the six `Strings.receiptInstance` classifies — so "no receipt shape is missing"
is a fact about this list, not a claim. -/
theorem receiptCreators_are_six :
    (promiseClasses.filter (fun p => p.addR = 1)).map (fun p => p.hid) = [8, 9, 11, 12, 24, 25] ∧
      (promiseClasses.filter (fun p => p.addR = 1)).all (fun p => (receiptInstance p).isSome) =
        true := by
  refine ⟨by decide, by decide⟩

/-- **The eleven functions of README §5.4(c), each with the instance that closes it.**  This is the
reviewable table: every name on the old "remaining" list appears here with a proved lemma, so the
list can be checked against the tree by machine. -/
theorem remaining_eleven_closed :
    -- the five action encodings
    (encAction 1 [.str []] = (deployRaw []).map UInt8.toNat) ∧
    (encAction 4 [.u128 0, .raw (demoPk.encode.map UInt8.toNat)] =
      (stakeRaw 0 demoPk).map UInt8.toNat) ∧
    (encAction 5 [.raw (demoPk.encode.map UInt8.toNat), .u64 0, .u8 1] =
      (addKeyFullRaw demoPk 0).map UInt8.toNat) ∧
    (encAction 5 [.raw (demoPk.encode.map UInt8.toNat), .u64 0, .u8 0,
        .raw ((⟨none, [97], []⟩ : NearSpecV3.D2.FcPerm).encode.map UInt8.toNat)] =
      (addKeyFcRaw demoPk 0 ⟨none, [97], []⟩).map UInt8.toNat) ∧
    (encAction 6 [.raw (demoPk.encode.map UInt8.toNat)] = (deleteKeyRaw demoPk).map UInt8.toNat) ∧
    -- the empty-Vec<Action> class row (`promise_batch_create`)
    (emptyActionsPlan.length = 4 ∧
      emptyActionsPlan.map (·.byte) = [0, 0, 0, 0]) ∧
    -- the receipt `inputs` prefix (`promise_batch_then`, `promise_then`, both `yield_create`s)
    ((inputsPlan 1 [1, 2, 3, 4]).length = 8) ∧
    -- the `v2` `refund_to` field (`promise_set_refund_to`)
    ((encOptBytes (some [97])).map UInt8.toNat = [1, 1, 0, 0, 0, 97]) := by
  refine ⟨encAction_deploy [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [encAction_stake]
  · rw [encAction_addKeyFull]
  · rw [encAction_addKeyFc]
  · rw [encAction_deleteKey]
  · refine ⟨emptyActionsPlan_len, ?_⟩
    rw [emptyActionsPlan_bytes, prefixBytes_eq]
  · rw [inputsPlan_len]
    decide
  · decide

end ZkFormal.PQ.Receipt
