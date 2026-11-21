# M5d leaf-template spec: INIT and FINAL as tree leaves (lane G → lane D)

Status 2026-11-21, M5d-T1. What lane D needs to wrap the M5d templates as tree leaves
(`build_seg_leaf`, plan §5.0.1.4) and what the wrap may rely on. Labels as in the README.
Everything below is built and measured on T1 unless marked **[S]** (proposal / not built).

## 1. Common to both templates

| item | value |
|---|---|
| stack | lane B's M5a prover family (`prover/`): unified SWIRL, BabyBear Ext12, SHA-384 MMCS 42-B digests, stacked WHIR, `NEARPROOF_{DIGEST_BYTES=42,COSET_LEAF=1,TSTAR=1}` |
| parameters | seg-v1: `l_skip 2`, `log_blowup 1`, `k 4`, `k_first 1`, final poly `2^7`, list decoding `m = 16`, query PoW 24, 268-bit target, LogUp `2^30` / message length `2^6`, `max_constraint_degree 9` (the chip); `n_stack` = least of 14/18/22 with `2^(n+2) ≥` max height and `w_stack ≤ 24`; `w_stack = ⌈cells / 2^(n+2)⌉ + 4` (≥ 8). T1 FINAL: `n_stack 18`, `w_stack 8` |
| AIRs | the Lean export (`m5d-tool air-final` / `air-init`) in table order, then `Sha512Air4`, `TableAir4` (native chip v4, buses 100–103) |
| cached / public tables | **none**. No tape, no cached root: nothing of the template is checked natively except its public values |
| public values | every table carries the first `num_pub` global public values (the interpreter's convention); the template's public-value vector is §3 / §4 |
| digests | `bdigest m = SHA-384(m)[0..42)` (lane E `Bnd.bdigest`, U-10); as public values: 14 limbs, limb `i` = `65536·d[3i] + 256·d[3i+1] + d[3i+2]` |
| I3 (review-D7) | INIT's input boundary is "before the chunk" (no `B_in`); FINAL's output phase is `done`. Neither accepts a `done` input |

## 2. The statement digest (`ctx` = `claimDigest`) [K for the encoding identity, S for adoption]

```
pre  = borsh(claim_tag) ‖ borsh(statement_id) ‖ u32 pv ‖ borsh(chain_id) ‖ epoch_id ‖ borsh(chunk_inner)
post = u16 rs_data_parts ‖ u16 rs_total_parts ‖ encList epochs ‖ borsh(epoch_start_after)
       ‖ encList apply_facts ‖ borsh(tx_valid) ‖ encOpt genesis_chunk_extra
stmtBytes(S) = u32 |pre| ‖ pre ‖ post
claimDigest  = bdigest(stmtBytes(S))
```

`pre`/`post` are the public prefix and suffix of `Claim.encode`, so `assemble ci secB secC =
pre ‖ encList BlockRec.encode secB ‖ post` (by definition of `Claim.encode`; the dump checks it on
T1). **V_d computes `claimDigest` from the public statement alone**; lane D's `D_wrap(ctx)` takes
it as `ctx`. Proposal to lane D/E: adopt `stmtBytes` as *the* `claimDigest` preimage (plan §3.2
"SHA-384 of the public statement" with the encoding fixed). T1: `claimDigest = 6ae2236e…22d7`.

## 3. INIT template

**Proves:** `claimDigest = bdigest(u32|pre| ‖ pre ‖ post)` and
`ctxRoot = bdigest(0x00 ‖ u32 ℓ_B ‖ u32 |cb| ‖ cb ‖ wb)` with `cb = pre ‖ blocks ‖ post`,
`ℓ_B = |blocks|`, over the same witness bytes (`CLM` rows feed both SHA-384 messages; the statement
message skips the `blocks` rows). `blocks`, `wb` stay private.

**Public values (28):** `[claimDigest (14 limbs), ctxRoot (14 limbs)]`.

**Leaf (lane D):** check `pv[0..14) = ctx`; build `B_0` = lane E's `view (init cb wb)`:
`claimDigest = ctx`, `phase 0`, all indices / clock / counters `0`, `ctxRoot = pv[14..28)`,
`stRoot = stD(.none)`, `outcomeAcc, outRcptAcc, proposalsAcc, bwAcc = outD(.none)`,
`vmAcc = vmD([])`, `wasm = none` — the `.none` components are view constants (lane B / M5d / lane E
fix them; for the M5d accumulators `outD(.none) = (bdigest [], [bdigest []], bdigest [], bdigest [])`
**[S]**); expose `s_out = [init, h(B_0)]`, `a = 0`.

**Obligation on INTAKE (lane B) [S]:** INTAKE opens `ctxRoot` (re-hashing `cb ‖ wb`) and must check
that `decodeClaimE cb`'s block list spans exactly `ℓ_B` bytes after `pre`. Without it a prover could
choose `blocks` so that the claim decoder consumes part of `post` as blocks and re-reads section C
from other bytes; with it, `cb = assemble ci secB secC` for the decoded `secB`
(`WitnessExtraction`). (Alternatively INIT and INTAKE share one leaf and the check is a bus.)

**Shape:** `CLM` height = `|cb| + |wb|` rounded up (T1: 14,734 → 2^14), `S384` ≈ `(|cb| + |wb|)/128`
(T1: 124 compressions → 2^7). Height classes by witness size.

## 4. FINAL template (class F1)

**Input point.** Lane E's `FINAL` step is `fin I out → done H o` = `finK` then `tailNew`. The template
covers `tailNew` + `headerOk` and starts at `t = (root, congestion, outgoing)`, the result of `finK`
(main post-state root check, implicit transitions, outgoing reassignment — state work: lane B
M5a FINAL root + M5c). Its input is the record

| `FinIn` bytes | field | source |
|---|---|---|
| 0..32 | post-`finK` state root | `t.1` |
| 32..75 | congestion `0 ‖ u128 delayed ‖ u128 buffered ‖ u64 receipt_bytes ‖ u16 allowed_shard` | `t.2.1` |
| 75..83 | `u64` gas used | `out.gasUsed` |
| 83..99 | `u128` balance burnt | `out.balanceBurnt` |
| 99..107 | `u64` gas limit | `I.slotB2.gasLimit` |
| 107 | proposed split (`0` = none; class F1) | `I.proposed` |
| 108..112 | `u32` proposals count (`0`; class F1) | `out.proposals` |
| 112..116 | `u32` bandwidth requests count (`0`; class F1) | `out.bwRequests` |
| 116..158 | outcome accumulator `chainD(leaf)` over `OutD1.leaf` | `out.outcomes` |
| 158..200 | outgoing accumulator `chainD(u64 routedShard ‖ u32 ℓ ‖ Rcpt.encode r)` | `t.2.2` |
| 200..242 | transaction accumulator (`bdigest []`; class F1: none) | `I.w.newTxs` |
| 242..246 | `u32` shard count (6, class) | `I.L.shardIds` |
| 246..294 | shard ids, `u64` each, layout order | `I.L.shardIds` |

`chainD` is lane E's (`View.chainD`): `acc_0 = bdigest []`, `acc_{i+1} = bdigest(acc_i ‖ item_i)`.
`finInDigest = bdigest(0x46 ‖ FinIn)`.

**Proves (in-circuit):** `claimDigest` of the statement (the template hashes the whole `stmtBytes`
and reads the header from its fixed window); the outcome root (`merklize` of the leaves the
accumulator opens to), the outgoing receipts root (`merklizeBorsh` over the layout's shards of
`sha256(u64 s ‖ encodeRcpts(receipts routed to s))`), the body `u32 0 ‖ encodeRcpts outgoing`, its
Reed–Solomon parts and `encoded_merkle_root`, `encoded_length = |body|`, `tx_root = zeroHash`; and
the 13 `headerOk` comparisons against the header (`Lean: final_template_sound`).

**Public values (30):** `[claimDigest (14), finInDigest (14), n, L]` (`n` = header
`encoded_length`, `L = ⌈n/d⌉`; both are constrained to the hashed header, so they need no check).

**Leaf (lane D):** check `pv[0..14) = ctx`; tie `pv[14..28)` to the input boundary (below); expose
`s_out = [done, h(B_out)]`. The wrap's `B_N.phase = done` then implies FinalOut (rec. 1(b)(ii)).

**Joining the input [S], two options:**
* (a) *one segment*: lane B's FINAL rows (post-state root) + M5c's implicit transitions + M5d's
  tables in one trace, `FinIn` carried on a bus instead of `finInDigest` (no digest, no new
  configuration). **Recommended.**
* (b) *a cut at `finK`*: a boundary with `phase = fin2` and `stRoot = finInDigest`; this needs lane E
  to split `CM`'s `fin → done` step at `finK` (a new configuration `fin2 I out t`).

**`B_out` [S].** `done H o`: the wrap reads only `phase`. For lane E's view: `ctxRoot =
ctxD(.header H)`, proposed `bdigest(0x04 ‖ chunk_inner)`; `outD(.done o)`, proposed
`(bdigest(0x05 ‖ encOutputs o), [], bdigest [], bdigest [])` — two more `S384` messages in the
template (not built; the template has the bytes).

**Class F1 pins** (fixed in the AIR; another class = another template in `{C_t}`): V5 header, no
proposals / bandwidth requests / split / transactions, 6 shards with `u16` ids, `|chain_id| = 14`,
`(d, t) = (5, 16)`, `n < 2^24`, `≤ 2^16` receipts per shard. General classes add: the transaction
segments (same `SEG`/`BODY` path, destination the tx hash + tx accumulator), proposal and
bandwidth-request encodings (variable header layout), the split option, other `(d, t)`.

**Heights on T1** (lane D's pinned `(log)` vector would be a class cap ≥ these): `SHA 12, S384 5,
RNG 8, STMT 10, FIN 2, BODY 10, SEG 3, RS 8, PART 5, SHD 3, OUTL 2, MRK 5, SHA512 12, SHA512T 7`.
Every table but `SHA` and the chip accepts padding rows (activity is a prefix, the last row is
inactive), so padding to class caps is a generator change; the `SHA` table and the chip pad by
their generators (`sha256gen`, `s384::trace`) — a minimum-height option is needed there.

**Measured (T1):** 989,626 B proof, 268.2-bit, prove 35.0 s, verify 102 ms; 32/32 mutants rejected.
