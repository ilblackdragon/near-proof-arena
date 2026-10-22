# `pq-hostfinal` — the eleven promise encodings, RIPEMD-160, and the coverage premises

Lane `lane/pq-hostfinal`. Branched from `origin/main` `dba4b0cc`. This is the raw log; the summary
goes to `results/` and `docs/HANDOVER.md`.

The lane picks up the three items the 2026-10-21 handover lists as still open in their families:

1. **The 11 `promise_*` encodings** (`results/pq-receipt-air/README.md` §5.4(c)).
2. **RIPEMD-160**, the last of the four D3α hash functions without an AIR.
3. **The coverage side**: `ArmAgrees`, `StateSide`, and the D1→D3 witness lift.

---

## 1. The eleven promise encodings — DONE

### 1.1 What was missing, precisely

README §5.4(c) lists the eleven as: 5 action kinds (`deploy`, `stake`, `addKey`×2, `deleteKey`);
`promise_batch_create`'s empty-`Vec<Action>` class row; the receipt `inputs`/`outputs` prefix
(`promise_batch_then`, `promise_then`, both `yield_create`s); and `promise_set_refund_to`'s `v2`
`refund_to` field.

Two structural facts made all eleven tractable at once, and neither was in the README:

* **`BField` could not express the missing action bodies at all.** The five action bodies are
  `tag ‖ borshBytes code`, `tag ‖ u128 ‖ PublicKey.encode`, `tag ‖ PublicKey.encode ‖ u64 ‖
  permission`, … — i.e. they contain a **verbatim** byte run (a serialised `PublicKey`, an
  `FcPerm.encode`, a permission tag byte) with no length prefix and no fixed width. `BField` had
  only `str` (which prepends a `u32`) / `u64` / `u128`, so `stake`'s `PublicKey.encode` was not
  expressible. `BField` gained `raw` (verbatim), `u8`, `u16`, `u32`; `encAction_length` and
  `BField.bytes_length` still hold for the extended type, so every existing lemma stayed.
* **The receipt envelope is a `BField` list too.** `ActionR.encode` is
  `borshBytes signer ‖ [refund_to] ‖ pk ‖ u128 ‖ u32 |outputs| ‖ … ‖ u32 |inputs| ‖ … ‖
  u32 |actions| ‖ action.raw…`, and each piece is a `BField` (`str`, `optField`, `raw`, `u128`,
  `u32`). So **one** theorem covers every receipt shape, instead of one per function.

### 1.2 What landed

`zk-formal/ZkFormal/PQ/Receipt/Encoder.lean` (extended):

| lemma | statement | axioms |
|---|---|---|
| `deployRaw` / `stakeRaw` / `addKeyFullRaw` / `addKeyFcRaw` / `deleteKeyRaw` | the spec's bytes, per `D2.pBase` arm | — |
| `decodes_deploy_{empty,nonempty}`, `decodes_stake_{zero,amount,secp}`, `decodes_addkey_{full,fc_none,fc_some}`, `decodes_deletekey` | the spec's **decoder** (`pBaseAct`) reads those bytes back, `raw` round-tripping | `[propext]` |
| `decodes_stake_not_addkey` | the check discriminates (negative control) | `[propext]` |
| `encAction_deploy` / `_stake` / `_addKeyFull` / `_addKeyFc` / `_deleteKey` | the **rows'** bytes equal the reference bytes | `[propext]` |
| `decodes_*` … `encAction_*_len` | per-shape length identity | `[propext]` |

`zk-formal/ZkFormal/PQ/Receipt/Receipt.lean` (new, 700 lines):

| lemma | statement | axioms |
|---|---|---|
| `encReceipt_eq_encode` | **the receipt body's bytes *are* `ActionR.encode`'s**, for arbitrary signer / refund / pk / gas / outputs / inputs / actions, `v2 = true` | `[propext, Quot.sound]` |
| `encReceipt_eq_encode_v1` | the same at `v2 = false` (the `D1`/`D2` shape `Cost.receipt_len` assumes) | `[propext, Quot.sound]` |
| `encReceipt_len` | the exact length, per shape: `4 + |signer| + refund + |pk| + 16 + 4 + Σ(32+4+|recv|) + 4 + 32·|inputs| + 4 + Σ|action|` | `[propext, Quot.sound]` |
| `pbe_len_framing_empty_actions` | the `u32 0` group's `len = 4` | std3 |
| `pbe_len_framing_inputs` | the inputs group's `len = 4 + 32·n` | std3 |
| `inputsPlan_{bytes,len,len_of_hashes,phases}` | the inputs row plan, exactly `4 + 32n` rows | `[propext]` |
| `emptyActionsPlan_{bytes,len,phases}` | the empty-vector plan, exactly 4 rows | `[propext]` |
| `promise_encodings_cover` | **every `promiseClasses` row that appends an action has a proved action instance, and every one that creates a receipt has a proved shape** | **none** |
| `promise_encodings_cover_discriminates` | the cover check has teeth (negative control) | `[propext]` |
| `receiptCreators_are_six` | the six `addR = 1` ids, off the table | **none** |
| `remaining_eleven_closed` | the README's eleven names, each with the instantiated lemma that closes it | `[propext, Quot.sound]` |
| `refundTo_option_shape`, `rcpt_body_tags`, `batchCreate_count_is_zero`, `then_inputs_shape` | the per-shape decoder facts | none / `[propext]` |

No `sorry`, no `native_decide`, no `implemented_by`.

### 1.3 The finding that changes the README's table

The README says the remaining work is "5 action encodings, one empty-`Vec<Action>` class row, the
receipt `inputs`/`outputs` prefix, and the `v2` `refund_to` field — **no new table, no new bus**".
That is right, and the reason is stronger than stated: the **whole receipt** is one `BField` list,
so the envelope is not "one group per field with per-shape framing lemmas" but a single
`flatMap` whose length is `Σ BField.len`. The `PBE` table therefore needs no change at all — the
new groups (`emptyActionsClass`, `inputsClass`) are `eFrameCons` at `hdr = 4`, `nStr = 0`, which
is exactly `pbe_len_framing_pc`'s shape. So the "empty class row" in the README's list is not a
new class *kind*, only a new **instance** of the existing one.

Practical consequence: the eleven cost one lane-day, not the 2–3 weeks the README's sizing implies
for the encoder block, because the work was 5 `BField` lists + one envelope theorem, and the
envelope theorem was blocked on `BField` having a verbatim case.

### 1.4 What is still stated, not proved (unchanged)

* `FCPlanIsTrace` / `PCPlanIsTrace` — that the *generator* emits exactly the plan. A statement
  about the trace producer, not the row constraints; a named `Prop := True`, unused.
* `ActionBytesAreHostBytes` — that a plan byte equals a Wasm-side memory byte. Needs the
  `HOSTB → MEMIO` binding the HOST chip leaves open for every family.
* `ActionEncodingIsBorsh` — now only the *entry* `ActionR` → `encReceipt` direction, since
  `encReceipt_eq_encode` closes the rows → spec-encoder direction.
* `RIDS`/`SRC`/`RCL` + the `newReceipts` fold — the SHA/multiset half, untouched by this lane
  (and per README §3.3 it is the 69 % of the cost, not the encoder).
