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

---

## 2. RIPEMD-160 — the row is defined and differentially tested; the cost is 14× the README's estimate

### 2.1 What landed

`research/near-compression/wasm-base-lean/WasmBase/RipemdAir.lean` (735 lines, namespace
`WasmBase.Chips.Ripemd`):

| group | columns | meaning |
|---|---:|---|
| `L` | 160 | left working words `al bl cl dl el` (word `w`, bit `k` at `32w+k`) |
| `R` | 160 | right working words `ar br cr dr er` |
| `X` | 512 | the block's 16 message words |
| `fL`/`fR` | 64 | the `f` value of each line |
| `xL`/`xR` | 64 | the selected message word `x[rl[j]]` / `x[rr[j]]` |
| `t` | 256 | four chained sums per line (`t1 = al+fL`, `t2 = t1+xL`, `t3 = t2+kL`, `tf = rot+el`) |
| `rot` | 64 | `rotl32 t3 sl[j]` (left), `rotl32 t6 sr[j]` (right) |
| `cy` | 248 | one carry per binary addition, 31 each (bit 31's carry dropped: mod 2^32) |
| `sel` | 80 | one-hot step selector |

`ncols = 1608`, `constraints.length = 2625`, `inters = []`, max degree **4**. Families and their
lengths (`constraints_len` is a kernel `decide`):

| family | len | degree |
|---|---:|---|
| `boolConstraints` | 1,608 | 2 |
| `selConstraints` (one-hot) | 1 | 2 |
| `fConstraints` (group-gated `f`, both lines) | 64 | 4 |
| `xselConstraints` (selector-gated message word) | 64 | 2 |
| `rotConstraints` (selector-gated rotation) | 64 | 2 |
| `adderConstraints` (8 additions x 63) | 504 | 3 |
| `shiftConstraints` (ungated `nxt` wiring) | 320 | 2 |

Design choices, each a fork in the road:

* **Both lines in one row.** The spec runs the left and right lines in lockstep
  (`Crypto.lean:129-133`), so one row is step `j in [0,80)` of *both*. No second table, no cross-table
  bus.
* **Rotation as a selector-gated index map, not a barrel shifter.** Each step's offset `sl[j]`/`sr[j]`
  is a constant from the spec's own array, so `rot_k = t3[(k + 32 - sl[j]) mod 32]` is a column index
  under a selector gate. A barrel shifter would cost ~5x32 selector bits and degree-2 products per
  bit; this costs 64 constraints total.
* **The right line's group is `4 - g`.** `rf (79-j)` walks the five forms in reverse, so the same
  `formBit` builder serves both lines with the group argument flipped — one definition, not two.
* **`majE` needs the triple-product correction.** `a*b + a*c + b*c` is **3**, not 1, when all three
  bits are set, so it is not a carry. `majE := a*b + a*c + b*c - 2*a*b*c` is; `majE_is_carry` proves
  the eight-case identity and `majE_discriminates` shows the uncorrected form fails at `(1,1,1)`.
  A real bug the differential test caught, not review.

`WasmBase/RipemdVectors.lean` (333 lines) is the compiled differential test. `genRow` fills every
column **from the step's own equations** (nothing copied from the constraint list); `nxtState` defines
the next state **by the shift equations alone**, so the traced state is read out of the AIR's columns;
`rowOk` evaluates all 2,625 constraints in `Fp`; `tampers` flips one constrained column and requires
failure; `airDigest` runs 80 rows per block through `nxtState` plus the spec's feed-forward and compares
against `NearSpecV3.Wasm.Crypto.ripemd160` and the published `RIPEMD-160("")` KAT.

Build output — and a mismatch **fails the build**, it does not print:

```
RipemdVectors: 320 rows satisfy all 2625 constraints, 17 tampers rejected,
  13 digests == spec, 2 message-columns confirmed free (named gap), RIPEMD-160 KATs ok
```

`#print axioms` on `constraints_le`, `constraints_len`, `shiftConstraints_le`, `formBit_le`,
`formBit_is_spec`, `adderConstraints_le`: `[propext, Quot.sound]` only — no `sorryAx`, no
`native_decide`, no `implemented_by`, and no `Classical.choice` on this side. Both files are reachable
from the `WasmBase` root and both `.olean`s exist, so the 2026-10-21 root-import trap does not apply.

### 2.2 The cost finding — this changes `pq-hash-air/README.md` §3.6's row

The README estimated `ripemd160` at **≈9-11 k cells/block**, and "~2-3 weeks, same shape as SHA-256".
That estimate assumed a *limb* layout like SHA-256's. The row as built is **bit-sliced, one step per
row**, and costs

```
1,608 columns x 80 rows = 128,640 committed cells per block
```

i.e. **13.8x SHA-256's 9,333** and ~12-14x the README's own figure. The reason is structural, not a
coding mistake: bit-slicing buys degree-4 polynomials and selector-gated index maps and pays in
columns — 832 of the 1,608 are just the 26 words (10 state + 16 message) at 32 bits each. A limb layout
would cut those to ~52 columns but reintroduce 16-bit limb additions with per-limb carries and a
bit-extraction gadget for every rotation.

So "≈9-11 k/B" is **not achievable by this design**, and the "2-3 weeks" sizing was written for the limb
design. The honest position: the bit-sliced row is **done and tested**, it is **14x the assumed cost**,
and whether that is acceptable depends on the `G_alpha` budget — a decision for the D3alpha cost review,
not for this lane. Both numbers are now measured rather than estimated.

### 2.3 What is stated, not proved (the gaps, named in the file)

* **No round-agreement lemma (the `M3` analogue).** Nothing proves a satisfying row *implies* the
  spec's step function; the vectors are a compiled test, not a theorem — the same gap `KeccakAir` and
  `ShaAir` carry. Needs the `Holds`->`eval` bridge per family.
* **The message-word binding.** `X` columns are free row inputs: the only link from the block to the
  row is `xselConstr`, which reads just the selected word. So the AIR proves "the digest follows from
  the message columns", not "the message columns are the padded block". That half is the
  `HOSTB -> MEMIO` binding (`inters = []`), the obligation `Sha.HashInputLink` names. The test
  *asserts* that two unselected columns stay free (`freeInputsStillOk`), so the gap is visible instead
  of silently absent — a fake tamper there would have been a lie.
* **No digest bus.** With `inters = []` the row cannot be consumed by a host call's proof yet. SHA-256
  has `busHashCall`/`busHashDigest`; RIPEMD's absorb/pad/digest boundary rows and bus are not here.
  This is row *arithmetic* only.
* **The feed-forward lives in the vectors, not the AIR.** `feedForward` (`Crypto.lean:134-135`) is
  applied by the generator between blocks; there is no feed-forward row family. A joined proof needs
  that row.

### 2.4 The bugs the test found (recorded because that is the point of the test)

Multi-block chaining first restarted only the *left* line and zeroed the right line's five words, so
every message of length >= 56 bytes — i.e. two or more blocks, since `len >= 56` forces a padding block —
produced a wrong digest; 8 of 13 digests failed before the fix. The bit-sliced `majE` triple product was
the second. Neither was visible in the constraint list: both surfaced only by running the digest against
the spec's own `ripemd160`. That is the argument for keeping the compiled differential test as a build
gate rather than a print.

---

## 3. The coverage side — premises rewritten so they are about separate artifacts

### 3.1 Why the earlier draft had to go

The 2026-10-21 gap analysis (`pq-d3-chain-gap-2026-10-21.md` §5) found `coverage : ArmAgrees ->
StateSide -> RelD3` **circular**: `StateSide` was, once `ArmAgrees` held, just `RelD3` again, so the
"theorem" was a rewrite wearing a join's clothes. That is fixed in
`zk-formal/ZkFormal/PQ/Join/Coverage.lean` (205 lines, rewritten; `Fold.lean` untouched).

### 3.2 What is actually proved now

| declaration | content | axioms |
|---|---|---|
| `coverage` | the fold: the pipeline run on the state proof's arm **is** the run on `d3Hooks`, given agreement at `.fcall` | `[propext, Classical.choice, Quot.sound]` |
| `coverage_pv86` | `ArmAgrees` + `StateSide` => `RelD3` at the deployed parameters | same |
| `patchArm_noncall` | the patch changes *only* `.fcall` — the checked form of "the join touches nothing else" | same |
| `armAgrees_d3` | the first premise is **inhabited**: the D3 hook agrees with itself, so `coverage` is not vacuous by contradiction | same |
| `armAgrees_iff_eq` | `ArmAgrees` is *exactly* the pointwise `.fcall` equation — the join's content and no more | same |
| `coverage_identity` | at the identity arm the patched pipeline *is* the `RelD3` pipeline | same |
| `relD3_of_lift` | how the witness lift composes into the join | same |

The two premises now name *different artifacts*:

* **`ArmAgrees cfg sa`** — the state proof's answer function `sa : ActCtx -> ActSt -> AR -> Base ->
  Except ...` agrees with the spec's D3 call arm at every `FunctionCall`. Since that arm *is* `runCall`
  (`D3/FunctionCall.lean:364-368`), this says "the state tables' answer is the Wasm run's outcome". One
  side is computed from the D1 state tables (`PQ/StatePort/`), the other by the Wasm machine
  (`WasmBase.Main.ExecHost`); neither is imported by `zk-formal` (the Wasm base is a separate Lake
  package). That is why it stays a hypothesis — the same reason `Register.RegBusSound` is one.
* **`StateSide cfg cb w sa`** — the D2 chunk pipeline *accepts* the chunk when `sa` replaces `.fcall`.
  This is the state half's own statement and is **not** a restatement of `RelD3`: the patched hook is a
  different `ActionHooks` value unless `ArmAgrees` holds, which is exactly why the fold is needed.

`armAgrees_iff_eq` matters for review: it shows the hypothesis cannot be strengthened or weakened, and
`armAgrees_d3` shows it is satisfiable — so the reduction is neither vacuous nor a tautology.

### 3.3 The D1->D3 witness lift — a documented negative fact, not a placeholder

The lift is now stated as the existential it is (`WitnessLift B cb w := RelD1a B cb w -> exists w2,
RelD3 cb w2`), and the header records *why* it cannot be an implication on the same bytes:

* `RelD1a`'s transaction decoder `pTxD1` rejects every action tag but `3` (Transfer) —
  `spec/lean/v3/NearSpecV3/TxD1.lean:97`;
* its receipt decoder `NearSpec.pReceipt` does the same — `spec/lean/NearSpec/Codec.lean:75`;
* `checkD1` rejects any contract code blob — `ChunkValidationD1.lean:63` (`w.no_code`).

So a `RelD1a` witness contains **no `FunctionCall` and no code at all**: "every call is backed by a Wasm
run" is *vacuously* true on it, and `RelD1a B cb w -> RelD3 cb w` is not merely unproved but the **wrong
shape**. `RelD3` is checked on the **D2** witness format (`ChunkValidationD2.decodeStateWitnessD2`), which
admits both. The lift is therefore *witness production*, not a re-reading of the same bytes, and it is
the state port's remaining item. `relD3_of_lift` records the composition so neither half has to be
restated later — and note its `hstate` premise: the produced witness must be one `StateSide` accepts.

### 3.4 Verification

`lake build ZkFormal.PQ.Join.Coverage` and the full `lake build` are green (764 jobs); the seven
declarations above are in the axiom audit above. `Coverage.lean` is still **modified, not committed**
(see §4), so the numbers in this section are from the working tree.

---

## 4. Lane state at handover

Committed on `lane/pq-hostfinal` (newest first).  The `§` references are to this log.

| commit | content |
|---|---|
| `2e90a315f` | `RipemdRound`'s header corrected to match the file (§5) |
| `3fb84f5f1` | RIPEMD stage 4, part 2: bit-to-word readout, eight shift-wired next words (§5) |
| `e13129b84` | RIPEMD stage 4, part 1b: `bitOf_ofBitsN`, `ofBitsN_congr` (§5) |
| `7cddf9289` | RIPEMD stage 4, part 1: the five gated sums in general form (§5) |
| `ceee23052` | RIPEMD stage 4 scaffolding: `gsumAux`/`csumAux` collapse |
| `45af882a9` | RIPEMD stages 1–3: plumbing, selector collapses, adder chain (§2) |
| `14af4935e` | coverage: `relD3_of_lift` was a tautology; add the `StateSide` conjunct (§3) |
| `f7b1a6e0c` | RIPEMD row defined and differentially tested; coverage premises de-circularised (§2) |
| `598d85bd2` | docs: the ripemd160 cost corrected; the `promise_*` encodings marked closed (§1) |
| `bdf80d018` | the eleven `promise_*` encodings (§1) |

Nothing is left uncommitted except the Rust `target/release/**` churn from the KAT run, which is
build output, not a source change.

The KAT harness was rebuilt on both sides and re-run (`run_kat.sh`, 8 progs x 64): **97 passed, 0
failed** (python ref = Lean spec = Rust trace + AIR pre-check). That is the "existing behaviour did not
move" check for this lane, since none of §1/§2/§3/§5 touches the host-function tables.

### 4.1 The RIPEMD round lemma is *partly* done — say which part

`RipemdRound.lean` (488 lines) now holds:

| section | content |
|---|---|
| §A/§B | `gsumG` + `gsumG_zero` + `gsumG_at`, and the five instances (`xselAux`, `rotAux`, `gselAux`, `fSumAux`, `kSelAux`), plus `xsel_eq`, `rot_eq`, `f_eq`, `gsel_profile` |
| §C | `bitOf_eq_testBit`, `testBit_ofBitsN`, `bitOf_ofBitsN`, `ofBitsN_congr`, `ofBitsN_foldl` |
| §D | `curWord`/`nxtWord`, `nxt_bit_of_shift`, `nxtWord_eq_cur` — a shift constraint lifts to a word |

What is **not** there, and should not be claimed:

* `round_agrees` itself.  The eight wiring-only next words are immediate from §D, but `bl'` and `br'`
  need the four-addition chain composed with the `f` column, the selected message word and the rotated
  `t3`, matched against `rot32 (…) sl[j] + el`.  `adder_chain` gives each addition separately; the
  composition is unwritten.
* Any *general* rotation bridge.  `rotl32n_is_rot` is a `decide` over 80 offsets × 8 values, not a
  proof for arbitrary arguments.  Rotation claims should be read as concrete checks.
* The feed-forward row family and the digest bus, so the row still cannot be consumed by a host call.

### 4.2 Axiom audit of the stage-4 declarations (measured, not asserted)

`lake env lean` on a probe file importing `WasmBase.RipemdRound`:

```
gsumG_at          [propext, Classical.choice, Quot.sound]
xsel_eq           [propext, Classical.choice, Quot.sound]
rot_eq            [propext, Classical.choice, Quot.sound]
f_eq              [propext, Classical.choice, Quot.sound]
gsel_profile      [propext, Classical.choice, Quot.sound]
bitOf_ofBitsN     [propext, Quot.sound]
testBit_ofBitsN   [propext, Quot.sound]
ofBitsN_congr     [propext, Quot.sound]
ofBitsN_foldl     [propext, Quot.sound]
nxtWord_eq_cur    [propext, Quot.sound]
```

`Classical.choice` appears exactly where the `Fp` field instance is used (the collapse lemmas go
through `sub_eq_zero'`/`Fp.ext`); the pure `Nat` lemmas do not.  No `sorryAx`, no `native_decide`, no
`implemented_by`.  The first two lines matter for the same reason as §3.2: they are the honest
statement, not the shorter one.

### 4.3 Next steps, in order

1. `bl'`/`br'`: compose `adder_chain` over the four additions per line with `f_eq`, `xsel_eq`,
   `rot_eq`, `kSelAux_at`, and state the result as the spec's `t`/`t'`.  This is the last piece of
   `round_agrees`.
2. The feed-forward row family and the digest bus (so the row is consumable by a host call).
3. `ArmAgrees` and the D1→D3 witness lift remain the state port's items (§3.3).


