# Proof debt (workplan item 11): split, float range, Logged spine, wider kernel non-vacuity

Lane of 2026-10-29. Package: `spec/lean/v3` (Lean `v4.34.1`), branch base `4f07a7fdf`. Target:
nearcore 2.13.4 (`44f7ae6c`), PV86. Full log: [`docs/logs/lean-proof-debt-2026-10-29.md`](../../../logs/lean-proof-debt-2026-10-29.md).

No definition of `checkD3`, `RelD3`, `checkSuccessor` or any tier changed in this lane. Everything
below is a theorem about the existing definitions, a repair of proofs that had stopped building, or a
new kernel evaluation of the existing checkers on real chunks. So no fixture family, breakage control
or verdict table is required by the workplan rules; §5 says why the one behavioural surface touched
(the read-logging mirror `Logged.*`) is not a semantic change.

## 1. Status per sub-item

| sub-item | status | where |
|---|---|---|
| float overlap/range (W04) | **proved**. Range/fuel: `bitLen`'s and `isqrt`'s fuel, and every float operator maps `w`-bit inputs to `w`-bit results. Overlap (round 2): `checkD3F` returns `checkD3`'s result wherever `checkD3` decides, on every chunk (`Successor.FloatOverlap`, a corollary of W12's `relSuccessor_floats_mono`) | `NearSpecV3/Wasm/FloatRange.lean`, `Successor/FloatOverlap.lean` |
| split correctness and authentication (W11) | **proved**: key-level correctness through squashing, per-column partition, independence from unread parent nodes (same child root on any refinement) | `NearSpecV3/ReshardingProofs.lean` |
| `WitnessLift` (`Coverage.lean:191`) | **not provable as stated** (round 3): `D2 ⊂ D3` is proved, but `D1 ⊂ D2` is **false** — a kernel-checked counterexample in `RelD1a B0` but not `RelD3` (§7). Needs a decision: D2's genesis rule in D0/D1, or a claim condition | `NearSpecV3/D2SubD3.lean`, `NearSpecV3/D2SubD3/*` |
| wider kernel non-vacuity | **done**: storage-writing 3-receipt chunk and a split child, each accepted and its root mutant rejected, for `RelD3` and `Tier.rel .allFeatures` (8 kernel decisions, measured) | `NearSpecV3/Examples/RealCaseD3{Store,Split}*.lean` |
| `Logged.API` / `D3LSpec` build | **repaired**, built and axiom-audited by the default target; the oracle driver `nearspec-v3-check-logged` and `AuditLogged.lean` are built and run by `make d3-drivers` (CI job `d3-drivers`) | `Logged/WasmCRCrypto.lean`, `Logged/Audit.lean`, `lakefile.toml`, `Makefile`, `oracle/wasm-d3/lean/LoggedHarness.lean` |

## 2. Theorems (all: no `sorry`; axioms ⊆ {`propext`, `Classical.choice`, `Quot.sound`})

The axiom sets are enforced by `#guard_msgs` in `NearSpecV3/ProofDebtAudit.lean` (imported by
`NearSpecV3`) and `NearSpecV3/Logged/Audit.lean` (a default target), so a `sorryAx` fails the build.

| theorem | statement (informal) | axioms |
|---|---|---|
| `retainSplit_get`, `retainSplitKids_get` | if the split succeeds on the subtree at key `κ`, the child answers `p` as the parent does iff `κ ++ p` is in a retained range, else nothing | P C Q |
| `splitChild_get` | the same for `splitRootE`'s trie (ranges = `intervalsToNibbles (boundaryAccountToIntervals b mode)`) | P C Q |
| `splitKey_partition` | left `[c, c‖b)` and right `[c‖b, c+1)` cover column `c` exactly and never overlap | P C Q |
| `allColumns_id_lt` | every pinned column id is `< 255` (side condition of the above) | none |
| `retainSplit_refinedBy`, `splitRootE_refinedBy` | split success and child root are invariant under revealing more of the parent (`PTrie.refinedBy`) | P C Q |
| `bitLenF_spec`, `bitLen_spec`, `bitLen_lt_iff` | `bitLen` (fuel 4096) is exact below `2^4096` | P Q / P C Q |
| `isqrt_spec` | `isqrt n = ⌊√n⌋` for `n < 2^128` | P Q |
| `neg_lt`, `abs_lt`, `copysign_lt`, `specials_lt` | bit operators and special values are `w`-bit | ⊆ P Q |
| `encodeNormal_lt`, `encodeSub_lt` | the encoders give `w`-bit patterns from ≤ `p`-bit significands | P Q |
| `roundPackS_lt` | every rounding result is `w`-bit (significand below `2^4096`) | P C Q |
| `add_lt`, `sub_lt`, `mul_lt`, `div_lt`, `sqrt_lt` | the arithmetic results are `w`-bit (f32, f64); `decode_e_bounds` bounds the aligned `add` operands by `2^(p + 2^eb)` | P C Q |
| `min_lt`, `max_lt`, `truncSat_lt` / `roundToInt_lt`, `convertInt_lt`, `demote_lt`, `promote_lt` | the remaining operators stay in range | P Q / P C Q |
| `Logged.checkD3L_eq`, `checkD3Reads_eq`, `checkD3_congr`, `reads_restrict_eq`, `reads_fixed`, `checkD2L_eq`, `runL_spec`, `runUntil_spec`, `E_step` | (pre-existing statements, rebuilt) the read-logging checker computes `checkD3` and its read set is exact | P C Q |
| `Logged.W.CR_cryptoHostCall`, `CR_dispatchArm`, `runCallWithLimitsL_spec` | (new) the curve-host arms and the loading preflight commute with the store erasure | P C Q |

P = `propext`, C = `Classical.choice`, Q = `Quot.sound`.

## 3. Kernel non-vacuity, wider cases (measured)

`decide +kernel` (no `native_decide`) on the Bool mirrors, transported by the existing bridges
(`RealCaseD3Bridge`). On demand, not in CI (decision in force). One module per kernel decision, so
each runs in its own Lean process:

```
lake build NearSpecV3.Examples.RealCaseD3StoreK0   # … K3, then RealCaseD3Store (umbrella)
lake build NearSpecV3.Examples.RealCaseD3SplitK0   # … K3, then RealCaseD3Split (umbrella)
```

Generated by `spec/lean/scripts/gen_realcase_d3.py --name Store|Split` (the default
`RealCaseD3{,Data}.lean` output is byte-identical after the generator change; checked by
regeneration).

| module | case | what it exercises | nearcore (cold) | theorem | wall | user CPU | max RSS |
|---|---|---|---|---|---|---|---|
| `StoreK0` | `d3c9/d3/02-h10008-s1` | 3 receipts (refund, `FunctionCall` ok, refund); contract `d3tiny` writes contract data (`0x09` key) | ok | `relD3_02_h10008_s1` | 4:10 | 235 s | 43.0 GB |
| `StoreK1` | same | same, successor | ok | `relAllFeatures_02_h10008_s1` | 3:59 | 224 s | 43.1 GB |
| `StoreK2` | `d3c9/mutants/02-h10008-s1-w.main_post_root` | same chunk, wrong main post-state root (the writes must be executed to see it) | `InvalidChunkStateWitness("Post state root …")` | `not_relD3_…` | 2:19 | 130 s | 23.1 GB |
| `StoreK3` | same | successor | same | `not_relAllFeatures_…` | 2:18 | 129 s | 23.2 GB |
| `SplitK0` | `resharding-fixtures-2/cases/seed37-00-h10085-s7` | first chunk of a split child (shard 7 = right half of shard 5 at `s0ctr2-0`); walk across the layout change; `apply_old_chunk` then `resharding` transition | ok | `not_relD3_seed37_00_h10085_s7` (the signed tier excludes it: `c.same_layout`) | 0:25 | 22 s | 5.5 GB |
| `SplitK1` | same | successor accepts the split child | ok | `relAllFeatures_seed37_00_h10085_s7` | 1:22 | 77 s | 14.5 GB |
| `SplitK2` | `…seed37-00-h10085-s7-w.split_child_post_root` | wrong child post-state root after the split | `InvalidChunkStateWitness("Post state root …")` | `not_relD3_…` | 0:24 | 22 s | 5.5 GB |
| `SplitK3` | same | successor rejects at the split's root | same | `not_relAllFeatures_…` | 1:17 | 72 s | 13.5 GB |

The umbrella modules `RealCaseD3Store` and `RealCaseD3Split` build. The compiled checker agrees
(`--tier signed`/`allFeatures`: accept/reject as in the table; the split mutant is rejected with
`invalid: implicit transition post state root`, the storage mutant with
`invalid: main transition post state root`).

Cases tried and dropped because the kernel run exceeded the 40 GB cap (OOM-killed, so not claimed):
`d3c10/d3/00-h10050-s1` (two `d3rich` calls, 1.8·10¹² call gas) and `d3c7/d3/06-h10009-s0`
(`d3rich`, 5.6 KB code). Kernel memory is dominated by preparing and running the contract: the
same-size `d3tiny` (345 B) case fits. A `d3rich` storage case needs a larger memory budget.

Resources: these runs used the `heavy` guards (own scope, `MemoryMax=40G`, no swap,
`oom_score_adj=1000`) but outside `zkbuild.slice`. A first attempt inside the slice made almost no
progress: the slice was above its 42.9 GB `MemoryHigh` with ~80 % "full" memory pressure
(7 s of CPU per 3 min).

## 4. `WitnessLift` — open, with the reason

`WitnessLift B cb w := RelD1a B cb w → ∃ w2, RelD3 cb w2` (`zk-formal/ZkFormal/PQ/Join/Coverage.lean`).
Not proved in this lane. Analysis:

* `checkD1` and `checkD2Core` both start with `decodeWitnessFile w` and decode the same nearcore
  `ChunkStateWitness` bytes; the D1 decoder is a restriction of the D2 one (Transfer-only actions, no
  code). So the natural witness is `w2 = w`, and `WitnessLift` follows from the same-bytes inclusion
  `RelD1a B cb w → RelD3 cb w`. The Coverage docstring's "wrong shape" remark is about the absence of
  `FunctionCall`s in a D1 witness (true) — it does not prevent the identity lift.
* That inclusion is `D1a ⊂ D1 ⊂ D2 ⊂ D3` on identical bytes. Only `D0 ⊂ D1` is proved
  (`relD0_relD1`, a five-phase simulation of ≈1,900 lines). `D1 ⊂ D2` needs the D2 runtime (actions,
  queues, congestion, bandwidth, fees, validators) to be shown equal to the D1 transfer runtime on
  Transfer-only chunks; `D2 ⊂ D3` needs a "success never invokes the `FunctionCall` hook" lemma
  through `checkD2Core` (D2's hook throws, D3's runs WASM) plus `allowCodes`/`gAlpha` monotonicity.
  The hook lemma is plausible: `d2Hooks.functionCall` always errors and no layer of the D2 runtime
  catches an action error (the only dispatch is `D2/Actions.lean:465`; there is no `tryCatch` in
  `D2/Actions`, `D2/Receipts`, `D2/RuntimeD2`), so a successful `checkD2` run never reached it —
  but stating it needs an induction through the whole `checkD2CoreObs` pipeline (the existing
  `checkD2Core_patch` in `zk-formal` only handles pointwise-equal hooks).
  Both are simulation proofs of the `D0SubD1` kind but several times larger; they were not attempted
  here. Both inclusions are tested, not proved (`ChallengeChunkV3.lean:18-19`).

## 5. Why the `Logged` repair is not a semantic change

`Logged.*` is a read-logging mirror of `checkD3`; its headline theorem `checkD3L_eq` states that it
*computes* `checkD3`. The repair changed the mirror (seed `curveHosts` like `runCall`, the widened
`callHost` guard, `runCallWithLimits` in `functionCall`) so that the theorem holds again, without
touching `checkD3`. The only consumer outside the package is `oracle/wasm-d3/lean`'s logged driver
(`MainLogged`, `AuditLogged`), which had not built since `St` gained `globalActions`/`curveHosts`; it
was not rebuilt in this lane.

## 6. Round 2 (2026-10-30)

**D2 ⊂ D3 (proved).** `NearSpecV3.Successor.relD2_relD3 : RelD2 cb w → RelD3 cb w`, on the same
bytes, via `checkD3_refines_checkD2 : Refines (checkD2 c w) (checkD3 c w)`. The three differences
between the checkers, each a refinement:

| step | lemma | argument |
|---|---|---|
| gas cap `none → some G_α` | `checkD2CoreObs_cap_free` | under a gas-free hook the chunk's `wasmGas` is 0: `D2.applyAction_gasFC` (every action but `FunctionCall` keeps `gas_burnt_for_function_call`; the walk covers all eleven action bodies) and `D2.applyNewChunkD2_wasmGas` (a postcondition walk, `PostE`, through every runtime function: queues, buffers, delayed receipts, transactions, receipts, instant receipts, yield timeouts) |
| `allowCodes false → true` | `checkD2CoreObs_codes_mono` | only the `w.no_code` exclusion goes |
| `d2Hooks → d3Hooks` | `d2Hooks_refine` + W12's `checkD2CoreObs_hooks_mono` | `d2Hooks` answers every `FunctionCall` with the exclusion `out of domain (e.wasm)`; the legacy pipeline binds the hook's result and never catches it |

Files: `NearSpecV3/D2SubD3/GasFree.lean`, `NearSpecV3/D2SubD3/WasmGas.lean`, `NearSpecV3/D2SubD3.lean`
(new default target; `#guard_msgs` on `relD2_relD3`'s axioms).

**`WitnessLift` reduced.** `relD1a_relD3_of_d1_d2 (hd12 : ∀ cb w, RelD1 cb w → RelD2 cb w) :
RelD1a B cb w W Dp N → RelD3 cb w` (and the same from `RelD0`). With the identity witness this is
`WitnessLift`, so the only obligation left is the `D1 ⊂ D2` rung.

**D1 ⊂ D2 (open).** Not proved. Unlike D2 ⊂ D3 (the same pipeline with three parameters changed),
`checkD1` and `checkD2` are separate implementations: different witness types (`Receipt`/`Tx` vs
`Rcpt`/`TxD2`), different trie machinery (`partialTrie` + `PTrie.set` vs `revealAll` + overlay +
`finalize` with squashing), a special-purpose transfer runtime (`RuntimeD0`/`RuntimeD1`) vs the
general action runtime with fees, refunds, delayed/buffered queues, bandwidth requests and yield
timeouts, and different claim walks (single epoch vs multi-epoch). A proof is a phase simulation of
the `D0SubD1` kind with, at least: decoder agreement on D1-shaped witnesses; claim-walk agreement on
single-epoch segments; trie-update agreement (`PTrie.set` roots vs `Ovl.finalize` roots, via the
`NearSpec.TrieUpsert*` refinement lemmas); D1 transaction processing = D2 `processTxD2` on transfer
transactions; system/transfer receipts through `applyActionReceipt`; empty bandwidth requests and
zero congestion under D1's `c.own_congestion_zero`; and equal outcome/receipt-root encodings. That is
several thousand lines and was not attempted in this round.
Empirical check (measured, this round): the compiled `checkD1`, `checkD2` and `checkD3` (`--tier signed`) on `d1run/d1` and `d1run/ood` (6,975 cases; 5 output lines were garbled by concurrent writers and are not counted): 3,393 D1 accepts, all 3,393 accepted by `checkD2` and by `checkD3`, 0 counterexamples. The `d1run/mutants` sample was not run (the case list hit the shell argument limit), so mutant D1 accepts, if any, are not covered.

**Float overlap (closed).** See the status table: `relD3_relD3F`,
`checkD3F_reject_of_checkD3_reject`, `checkD3F_verdict_of_decided`.

**Oracle logged driver (rebuilt, in CI).** `nearspec-v3-check-logged` builds; `LoggedHarness`
needed the `TTN.BMap` overlay type. `make d3-drivers` builds both and runs `AuditLogged.lean`
(passes). Smoke: `--d3` and `--d3l` agree on 300/300 d3c9 cases (150 honest, 150 mutants; 190
accept, 109 reject, 1 out of domain).

**`d3rich` storage case at 60 GB (optional item).** tried `d3c7/d3/06-h10009-s0` (`d3rich`, two receipts, contract-data write) at a 60 GB cap: the first attempt hit the kernel heartbeat limit after 5:08 at 48.6 GB; with `maxHeartbeats 0` it was OOM-killed at 60 GB. Not claimed; the modules were not committed. A `d3rich` kernel case needs more than 60 GB.

## 7. Round 3 (2026-10-30): D1 ⊂ D2 is false

Scoping phase B of the planned D1 ⊂ D2 simulation (the claim checks) turned up a check D2 has and
D1 lacks: D2 requires `!b.isGenesis || epoch_start_after = 1` for every block of the segment; D0/D1
only require all flags to be 0. A d1run chunk whose segment ends at the genesis block, with that
(trusted) flag falsely set to 0, is accepted by D0, D1 and D1a and rejected by D2 and D3. Proved by
kernel evaluation: `not_d1_sub_d2`, `not_d1_sub_d3`, `not_d0_sub_d3`, `not_d1a_sub_d3`
(`spec/lean/v3/NearSpecV3/Examples/D1NotSubD2*.lean`; evidence and the six cases in
[`d1-genesis-flag/`](d1-genesis-flag/README.md)). The witness is the honest, nearcore-valid one, so
this is not a Lean accept of a nearcore reject; it is a claim-discipline difference between the
rungs. It does mean `WitnessLift` (and `RelD1a ⊂ RelD3` on the same bytes) cannot be proved without
changing D0/D1 or adding a claim hypothesis, so the phase simulation was **not started**: its target
statement needs that decision first.

**Phase status of the D1 ⊂ D2 simulation** (the running list requested by the coordinator):

| phase | content | status |
|---|---|---|
| A | claim decode, witness file, code / size gates | not started (identical terms in both checkers) |
| B | witness decode (`decodeStateWitnessD1` ⇒ `decodeStateWitnessD2`, `pReceipt`/`pTxD1` ⇒ `pRcpt`/`pTxD2`) and claim checks | **blocked**: the claim checks differ by the genesis rule (counterexample above) |
| C | chain walk and source receipts | not started |
| D | main transition (`applyNewChunkD1` vs `applyNewChunkD2`: trie, transactions, receipts, congestion, bandwidth) | not started |
| E | implicit transitions, header comparison, Reed–Solomon body | not started |

Phase B's decoders turned out closer than feared: both use the strict `pAccountId` and reject
ML-DSA signer keys, so no second decoder-level gap was found by reading.

**Censuses (re-run serially, one process per case, at most 3 workers).** The round-2 numbers came
from `xargs -P 3` writing to one file, which interleaved a few output lines; the serial re-runs:

| population | cases | D1 accepts | D2 accept | D3 (`--tier signed`) accept |
|---|---|---|---|---|
| `d1run/d1` + `d1run/ood` | 7,039 | 3,394 | 3,394 | 3,394 |
| `d1run/mutants`, every 8th (case list in a file) | 5,751 | 951 | 951 | 951 |

The real corpora never contain the false genesis flag, which is why no census found the gap.

**Recommendation.** The cleanest closure is the follow-up already in `docs/CONTRACTS.md`: define the
lower rungs as restrictions of the top relation (`Rel_Dk := RelD3 ∧ InDk`), which makes every
inclusion and `WitnessLift` a projection. The minimal alternative is to add D2's genesis rule to
D0/D1 (it moves only false-flag claims from accept to reject), then run the phase simulation under
it. Either changes a rung of the signed `near-chunk-v3` statement, so it needs the owner's decision.
