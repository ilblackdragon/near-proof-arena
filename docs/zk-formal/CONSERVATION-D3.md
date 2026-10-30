# Conservation of NEAR by a D3 chunk — statement, and why it differs from `TOP_LEVEL_THEOREM.md`

**Status: statement, tested on 26,888 chunks; not proved.** Lean: `spec/lean/v3/NearSpecV3/D3/Conservation.lean`
(`ChunkConservation`, `MissingChunkConservation`, `ObsAgrees`, all `Prop`s; the module builds).

## The claim

For every chunk the D3 runtime applies (`applyNewChunkD2` with `D3.d3Hooks Wasm.pv86`, the function
`checkD3` runs):

```
nearIn(post) + value(outgoing receipts) + balance_burnt
  ≤ nearIn(pre) + value(incoming receipts) + epoch reward credited on the shard
```

— **the chunk creates no NEAR beyond the epoch reward** — under hypotheses that exclude inputs no
real chain produces (see "Hypotheses" below). On every tested chunk the two sides are *equal*.

where `nearIn` is the NEAR in the shard's trie (accounts' `amount + locked`, gas-key balances, and
receipts at rest: postponed, yield, delayed, buffered) and a receipt's value is its deposit plus its
gas at its gas price. Summed over a block's shards, every outgoing receipt is another shard's incoming
one, so the total changes by `Σ rewards − Σ balance_burnt` — the identity the block header's
`total_supply` check enforces (`Supply.verifyTotalSupply_accept`). With the reward bounded by
`Supply.creditedRewards_le_supply_div_40`, that is **"total supply grows only by the epoch reward,
at most 2.5 %/yr"** at the level of the runtime's own state, not just the header field.

It is sharp in the direction that matters: an over-credit or over-refund of 1 yoctoNEAR anywhere
breaks it. It is `≤` rather than `=` because the runtime overwrites some queue slots blindly
(`delayPush`, `bufferReceipt`, postponed and yield registrations); a value at rest at such a slot is
destroyed, and for slots named by SHA-256-derived ids, exact freshness would need a hash
no-collision assumption.

## Hypotheses (current pin)

The pre-state trie is well-formed (`t.wf`); `gasLimit < 2^64` (a decoded `u64`; bounds the 1-yocto
subsidy mints); no revealed account `system` (the runtime cannot create one); no input system
receipt — incoming or at rest — carries a gas price (`SysGasFree`); the incoming receipts and the
transactions' signers belong to the shard; incoming receipts and each transaction's receipt encode
canonically (`CanonRcpt`); and NEAR held + incoming + reward `< 2^120` (real supply ≈ `2^110`).
Every one excludes only inputs a witness cannot produce, and each was added after the deepseek-fv
provers found, usually with a kernel-checked counterexample, that the statement was false without
it. All hold on every corpus chunk.

## Tested

A harness (a copy of `checkD2CoreObs` that stops after the main transition) evaluated both sides on
every `checkD3`-accepted case of the `d3c7`, `d3c8`, `d3c10` and `d2corpus.v2` corpora
(`nearproof-deps/corpora/*/{d3,d2}`) on 2026-10-30: **26,888 chunks, both sides equal on every one,
no harness error**. 641 of them start an epoch and credit validator rewards; the rest include
function calls with promises and attached deposits, refunds, burns, delayed and buffered receipts.
The statement was tested before any proof effort, so a failing proof cannot be blamed on a false
target.

**One false case was found by the prover, not the corpus, and fixed.** The first deepseek-fv lead
noticed that `delayPop` (`D2/Queues.lean:459-480`) drops delayed receipts routed to another shard —
resharding leftovers: both children of a split inherit the parent's delayed queue and each drops
its sibling's copies — while the measure counted them, so the identity failed on such a pre-state.
No corpus chunk has such a leftover. `nearIn` now takes the layout and shard id and counts a
delayed receipt only on the shard it routes to (buffered receipts are outgoing and always count);
this removes a double count rather than adding a hypothesis. Re-run on the fixed statement: all
26,888 chunks equal.

**A second false case, also found by the prover.** With the shard-aware measure, a receipt for
another shard passed in as `incoming`, or created by a foreign signer's transaction to itself, can
be delayed into this shard's queue and is then not counted. So the statement now assumes the chunk's
inputs belong to the shard: every incoming receipt routes to `own` (what `checkD2CoreObs`'s filter
at `ChunkValidationD2.lean:213` establishes) and every transaction's signer does (the chunk
producer's invariant; **`checkD2` does not check it**, so a bridge from `RelD3` to this statement
needs either that check or an argument that a foreign signer's transaction fails without writes).

## Why the obligations in `TOP_LEVEL_THEOREM.md` / `ConservationStatement.lean` are not used

Read against the code, each is false as written:

1. **`applyActionReceipt … → rsSupply rs' = rsSupply rs`.** The receipt `r` is an argument, not part
   of `rs`, and a successful transfer credits its deposit to the receiver (`Receipts.lean:141-162`):
   the measure rises by the deposit. The true form is `+ value r`.
2. **`processTxD2 … → rsSupply rs' = rsSupply rs + fee`.** The signer *pays* `totalCost =
   burntAmount + rgp·rem + dep` (`Fees.lean:376-384`); `burntAmount` goes to `txBurnt`, `dep` into the
   receipt, and `rgp·rem` travels as the receipt's gas, which `rcptAmount` does not count. The measure
   falls by `rgp·rem`; it does not rise by the fee. With gas counted, it is unchanged.
3. **`processReceipt`** fails on the same branches, and on receipts stored in the trie (postponed
   `[6]`, yield `[12]`, delayed `[7]`, buffered `[14]`), which the measure omits.
4. All three quantify over arbitrary `ActionHooks`; a hook can set `st.account` to anything.

And the measure they build on, `StateMeasure.acctSumOf` / `akSumOf`, cannot measure a chunk's trie:

* `PTrie.allKeys` is `none` as soon as any subtree is a hash stub, and a chunk's trie is always a
  partial trie, so both sums are `0`.
* `headVals t k` selects keys by their first **nibble**: `k = 0` matches every key whose first byte is
  `0x00–0x0F` (accounts, code, access keys, received data, …), and `k = 2` matches `0x20–0x2F`, which
  contains no access keys (those start with byte `0x02`), so gas-key balances are never counted.

`Conservation.lean` therefore measures the *revealed* leaves (`revealedT`) and classifies keys by
their first byte.

## Not exact conservation: the 1-yocto subsidy

`one_yocto_on_promise` (`Wasm/Host.lean:480,671`): a promise attaching 1 yoctoNEAR from a zero balance
is not deducted, and `subsidized` is incremented; the chunk subtracts it from `balance_burnt`
(`D2/RuntimeD2.lean:225-227`). So NEAR *is* created there — 1 yocto per such promise — and netted
against the burn; the identity is stated with `balance_burnt`, as the header's is.

## Proof

Being attempted with deepseek-fv (`deepseek-fv/envs/nearproof`, problem `nearproof_d3_conservation`).
