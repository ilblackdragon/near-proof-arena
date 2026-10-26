# Tier refinement proofs and census cross-check (W12 + W10, 2026-10-26)

Lean: `spec/lean/v3/NearSpecV3/Successor/{TierProofs,GenesisOverlap,TierMono}.lean`, built by the
default `lake build` (`NearSpecV3.Successor.TierMono` is a default target). No `sorry`; the axiom
audit is `axioms.txt` (`#print axioms` output from the build log: only `propext`,
`Classical.choice`, `Quot.sound`). No definition was changed; the proofs are about the existing
terms. Doc comments only in `GenesisD3.lean` (the overlap obligation is now a theorem) and
`Config.lean` (pointer from `Tier.rank`).

Census binary: `nearspec-v3-check-successor` sha256 `29bf5217f43a23d3…` (the `5c60547b3` checker of
`corpus-blind-and-pipeline/`). The binary rebuilt from this branch gives byte-identical rows on a
seeded 3,000-case sample for `signed` and `allFeatures` (0 of 6,000 rows differ).

## 1. The relation

`Refines x y` (`TierProofs.lean`): `x = y`, or `x` is an exclusion (`out of domain …`). So wherever
the lower checker decides — accept, or reject with a given error string — the higher one returns
exactly the same result. `Tier.verdict_of_refines` is the verdict form: a decided verdict is
preserved. The census checks the same thing: a *violation* of `lo ⊑ hi` is a case where `lo`
returns accept/reject and `hi` returns anything else (different verdict, or the same verdict with a
different reason string).

## 2. Theorems

Proof method: `refines_lockstep` walks the two elaborated checker bodies together (identical
subterms by reflexivity; binds, `if`s and `match`es by congruence; an exclusion guard only on the
left by `check_bind_left`; a weaker numeric exclusion bound on the right by `check_le`). The W10
overlap needs one more idea: the genesis-capable shell re-runs the non-genesis checker from scratch,
so the walk tracks that the non-genesis checker's full result still equals its remaining computation
(`Overlap`), which makes the fresh run at the delegation point the same value.

### Per-feature lemmas (shell level, `TierProofs.lean`)

| lemma | statement |
|---|---|
| `checkD2CoreWithObs_segment_mono`, `checkD2CoreWith_segment_mono`, `checkD2CoreGWith_segment_mono`, `checkReshardCoreObs_segment_mono` | any driver `d`: shell at `d` ⊑ shell at `{d with segmentUnbounded := true}` |
| `checkD2CoreObs_gas_mono`, `checkD2Core_gas_mono`, `checkD2CoreWithObs_gas_mono`, `checkD2CoreWith_gas_mono`, `checkD2CoreGWith_gas_mono`, `checkD2CoreG_gas_mono`, `checkReshardCoreObs_gas_mono` | `CapLe g₁ g₂` (larger bound or no bound): shell at `g₁` ⊑ shell at `g₂` |

### W10 overlap (`GenesisOverlap.lean`)

| theorem | statement |
|---|---|
| `checkD2CoreGWith_overlap` | any driver with `resharding = false`: `checkD2CoreGWith d … = checkD2CoreWith d …` **or** `checkD2CoreWithObs d … = .error "out of domain (c.not_genesis)"`. The common prefix (decoding, epoch table, layout, segment, hash links, walk to `B2`) is included: both fail there with the same error or both reach `B2`. |
| `checkD2CoreG_overlap` | the same for the signed pair `checkD2CoreG` / `checkD2Core` (legacy driver). |
| `checkD2CoreGWith_eq_of_not_genesis` | equality whenever the non-genesis checker does not report the genesis exclusion. |

The restriction to `resharding = false` is necessary, not an artefact: with the resharding driver the
non-genesis shell lifts `c.same_layout`/`c.no_split_gate` while the genesis-capable prefix keeps
them. No named tier is affected (every resharding tier also sets the genesis flag).

### Configuration and tier level (`TierMono.lean`)

| theorem | statement |
|---|---|
| `checkSuccessor_segment_mono` | every `cfg`: `cfg` ⊑ `{cfg with segmentUnbounded := true}` |
| `checkSuccessor_gas_mono` | every `cfg`, `CapLe cfg.gasCap g`: `cfg` ⊑ `{cfg with gasCap := g}` |
| `checkSuccessor_genesis_mono` | every `cfg` with `resharding = false`: `cfg` ⊑ `{cfg with genesisMainTransition := true}` |
| `checkD2CoreWith_refines_GWith`, `checkD2Core_refines_G` | the overlap as a refinement |
| `checkD2CoreWithObs_resharding_mono`, `checkD2CoreGWith_resharding_mono`, `checkD2CoreGWith_reshardingDriver_mono` | the resharding driver (guards lifted, `splitApply` unreachable on these shells) refines the recorder driver |
| `relSuccessor_protoGas_mono` | `.signed ⊑ .protoGas` |
| `relSuccessor_floatsProtoGas_mono` | `.floats ⊑ .floatsProtoGas` |
| `relSuccessor_genesis_mono` | `.signed ⊑ .genesis` |
| `relSuccessor_genesisFloatsProtoGas_mono` | `.floatsProtoGas ⊑ .genesisFloatsProtoGas` |
| `relSuccessor_signed_genesisProtoGas` | `.signed ⊑ {signed with protocol gas, genesis}` |
| `relSuccessor_resharding_mono_genesis` | `.curveHosts ⊑ .resharding` on every claim whose segment has a genesis block |
| `runCallWithLimits_eq_of_fits` | the loading-limits correction is inert on every call whose module fits |
| `recorderDriver_receiptShard_globals`, `recorderDriver_outgoingRoot_globals` | with `globals = true` the recorder driver's receipt routing and outgoing-receipts root equal the D2 ones on receipts that are not distribution receipts (part of O3) |
| `relSuccessor_resharding_allFeatures_of` | `.resharding ⊑ .allFeatures` given the global-action lift at the resharding configuration (the `c.segment` step is discharged) |
| `relSuccessor_curveHosts_allFeatures_of`, `relSuccessor_globalActions_allFeatures_of` | the same for `.curveHosts` and `.globalActions`, at verdict level (`VRefines`), because their path crosses the resharding step (Finding 2) |
| `Refines.toV`, `VRefines.trans`, `VLift.trans`, `Lift.toV` | the verdict-level relation and its composition |

### Open obligations (also the closing doc comment of `TierMono.lean`)

| id | step | what is missing | census |
|---|---|---|---|
| O1 | floats | induction showing `NearCfg.floats` is read only by the three `Prepare` guards | 0 violations |
| O2 | curve hosts | propagation of `successorDispatch_extends` through `runCall`/`St`/runtime | 0 |
| O3 | global actions | routing/outgoing root proved for non-distribution receipts; missing: global codecs extend the D2 codecs, `globalTarget` never excludes a non-distribution receipt, `StorageExecution.run` monotone in `globals` | 0 |
| O4 | storage resolution | agreement of `applyNewChunkD2` and `StorageExecution.run` on the legacy domain (engine change, W08 rule), **restricted to `lastSplit = none`** | 1 counterexample on a V3 post-split layout (Finding 1) |
| O5 | loading limits | not a lift (correction); chunk-level form of `runCallWithLimits_eq_of_fits` | 0 (no case in the corpora differs) |
| O6 | resharding, non-genesis | `checkReshardCore` reduces to `checkD2CoreWithObs` on one-layout, no-split-gate segments, **at verdict level** (`VRefines`) | 1 reason-only difference (Finding 2) |
| O7 | complete-code witness | not a lift; counterexamples below | violations, all `w.code_complete` |

## 3. Census cross-check

Populations (`tools/strat.py`, `tools/p2.py`, seed 20261026):

* **STRAT** — 18,553 cases of the 235,716 in d1run, d2corpus.v2, d3c7–d3c10: every `ood`-dir case
  (7,004), every gap mutant (`nearcore: ok` and not `RelD3` per meta, 169) and a seeded 5 % of the
  rest (11,380). All 13 tiers.
* **P2** — the 7,178 STRAT cases where tiers can differ (`ood` dirs, signed ≠ allFeatures, or
  allFeatures excludes). All 13 tiers.
* **W08** — the 103 code mutants whose allFeatures verdict changed with the W08 pipeline rule
  (`corpus-blind-and-pipeline/code-mutant-pipeline-diff.json`). All 13 tiers.
* **FULL** — all 235,716 cases, tiers `signed` and `allFeatures`; see §3.4.
* **FX** — the 461 cases of the committed fixture sets (curve-host, key-family, yield, resharding,
  global-cache, global-promise). All 13 tiers.
* **MAINNET** — the 1,223 mainnet shard-13 chunks of `mainnet-w13-shard13`. All 13 tiers.

Every ordered pair of the 13 tiers was compared (`census-summary.json`, 156 pairs per population).

### 3.1 Verdicts, STRAT (18,553)

| tier | accept | reject | out of domain |
|---|---|---|---|
| signed | 7,715 | 8,185 | 2,653 |
| floats | 7,840 | 8,185 | 2,528 |
| protoGas | 8,562 | 8,185 | 1,806 |
| floatsProtoGas | 8,701 | 8,185 | 1,667 |
| genesis | 7,980 | 8,185 | 2,388 |
| genesisFloatsProtoGas | 8,966 | 8,185 | 1,402 |
| runtimeLimits | 8,966 | 8,185 | 1,402 |
| storageResolution | 9,359 | 8,186 | 1,008 |
| globalActions | 10,084 | 8,204 | 265 |
| completeCodeGlobal | 9,906 | 8,386 | 261 |
| curveHosts | 9,599 | 8,186 | 768 |
| resharding | 9,599 | 8,186 | 768 |
| allFeatures | 10,345 | 8,204 | 4 |

### 3.2 Violations of `lo ⊑ hi`

Pairs whose feature flags are contained (`lo`'s lift flags ⊆ `hi`'s): 60 not involving
`completeCodeGlobal`, 9 with `completeCodeGlobal` as target.

| population | cases | contained pairs (60) with any difference | note |
|---|---|---|---|
| STRAT | 18,553 | **0** (verdict and reason string) | |
| P2 | 7,178 | **0** | |
| W08 | 103 | **0** | |
| MAINNET | 1,223 | **0** | |
| FULL (`signed`, `allFeatures`) | 235,716 | **0** | the one pair run on the full corpus |
| FX | 461 | 40 pairs, from **2 cases** | the two findings below |

This covers the four proved pairs, `signed ⊑ allFeatures` (old-domain agreement) and every wide
tier ⊑ `allFeatures`.

**Finding 1 — the storage-resolution step (O4) is not a refinement on V3 post-split layouts.**
`resharding-fixtures/cases/seed11-02-h10077-s2` is honest, nearcore-valid (cold validator), one
layout across the claim's epochs (a V3 layout after a split), non-empty bandwidth requests. Every
legacy-engine tier (`signed`, `floats`, `protoGas`, `floatsProtoGas`, `genesis`,
`genesisFloatsProtoGas`, `runtimeLimits`) **rejects** it with `invalid: InvalidBandwidthRequests`;
every recorder-engine tier (`storageResolution`, `globalActions`, `curveHosts`, `resharding`,
`allFeatures`) accepts. Cause: the legacy `bandwidthRequests` (`D2/Queues.lean`) has no V3 parent
chaining, which `StorageExecution.bandwidthRequestsV3L` added for the resharding fixtures (W11). This
is a completeness gap of the signed statement on post-split V3 layouts (it rejects a valid chunk; it
never accepts an invalid one here) and a legitimate semantic correction in the successor. The
signed sources are immutable, so the exact restricted statement is: O4, and old-domain agreement,
on witnesses whose layout has `lastSplit = none`. None of the six corpora nor the mainnet shard-13
window contains a case of this kind (0 violations there).

**Finding 2 — the resharding step (O6) holds only at verdict level.**
`resharding-fixtures/cases/seed23-02-h10062-s5-c.child_layout_is_parent` (a mutant): every tier
rejects, but the `ReshardCore` tiers (`resharding`, `allFeatures`) report `invalid: shard not in
layout` where every other tier reports `invalid: slot count` — `ReshardCore` checks a malformed layout
in a different order. So `Refines` (error string included) fails for `curveHosts ⊑ resharding`, and
the composition theorems through the resharding step are stated with `VRefines` (accept ↦ accept,
reject ↦ reject).

**`completeCodeGlobal`** is the only other target with differences, and every one is its
complete-code rule:

| population | lo ⊑ completeCodeGlobal | accept→reject | same verdict, other reason |
|---|---|---|---|
| STRAT | signed (and every narrow tier) | 5 | 909 |
| STRAT | storageResolution | 177 | 910 |
| STRAT | globalActions | 178 | 928 |
| W08 | globalActions | 8 | 0 |
| MAINNET | any | 0 | 0 |

Characterization (`ccg.json`): every case where `completeCodeGlobal` and `globalActions` differ has
the `completeCodeGlobal` reason `invalid witness (w.code_complete): raw contract code is required for
pre-state or unresolved-origin execution`; there is no other difference. On STRAT (1,110 differing
cases): 178 accept→reject on chunks nearcore accepts (170 cold-validated d3c7–d3c10 mutants, 3 honest
d3c7/d3c8 cases, 5 producer-verdict `ood`/d2 cases); 928 reject→reject with the reason replaced (704
cold-validated mutants nearcore rejects, 224 d2corpus.v2 `ood` cases whose witnesses predate code);
4 out-of-domain→reject (nearcore rejects). On W08: 8 accept→reject (nearcore accepts) and 95
out-of-domain→reject (nearcore rejects). The 5 signed-accept/complete-code-reject cases include
honest cases, e.g. `d3c7/d3/07-h10167-s4` and `d3c8/d3/04-h10057-s1` (nearcore `ok`): the
complete-code policy is not a refinement even of the signed tier, so it cannot be in the join. (The
workplan's "86" is the same family on the 3,138-case gap set at an earlier binary.)

### 3.3 Mainnet shard 13 (1,223 chunks)

| tier | accept | out of domain |
|---|---|---|
| signed, protoGas, genesis | 944 | 279 |
| floats | 1,170 | 53 |
| every other tier | 1,223 | 0 |

No tier rejects any of these chunks (all are nearcore-valid), and no contained pair differs.

### 3.4 Full corpus

All 235,716 cases of d1run, d2corpus.v2 and d3c7–d3c10, `signed` and `allFeatures`:

| signed → allFeatures | cases |
|---|---|
| accept → accept | 73,577 |
| reject → reject (same reason string) | 159,381 |
| out of domain → accept | 2,630 |
| out of domain → reject | 33 |
| out of domain → out of domain | 95 |
| signed decides, allFeatures differs | **0** |

The 95 still excluded by `allFeatures` are the W08 thread-race code mutants (nearcore rejects all 95).
The other eleven tiers were run on STRAT, P2, W08, FX and MAINNET only; a full-corpus run of all 13
tiers did not fit the machine time available (about 35 minutes per tier per 235,716 cases).

## 4. Old-domain agreement (signed `checkD3` vs `allFeatures`)

Census: 0 violations on STRAT, P2, W08, MAINNET and FULL (§3.4). On STRAT (18,553): 7,715
accept/accept, 8,185 reject/reject with the same reason string, 2,630 out-of-domain→accept, 19
out-of-domain→reject, 4 out-of-domain in both. Named differences between the signed statement and the
current tiers:

* **V3 post-split bandwidth requests (Finding 1).** `signed` rejects one honest fixture that
  `allFeatures` accepts. Exact statement: old-domain agreement holds on layouts with
  `lastSplit = none`; the signed checker is incomplete (not unsound) on V3 post-split layouts.
* **SECP256K1 delegate (accepted strengthening).** `actDelegate` is shared by `checkD3` and the
  successor, so the widening moved 35 signed verdicts out-of-domain→accept in the signed tier itself
  (workplan, W06). Signed and allFeatures agree on all of them.
* **W08 pipeline code rule.** The successor's deploy-served preparation rule changed 103
  allFeatures verdicts. The signed tier excludes all 103 (`pre-state contract served only by the
  in-chunk compiled-contract cache`), so the rule changes no signed-decided verdict.

What is proved for the old domain: `.signed ⊑ .protoGas`, `.signed ⊑ .genesis` (W10) and the
`c.segment`/gas/genesis lifts at every configuration. `.signed ⊑ .allFeatures` itself additionally
needs O1–O4 (floats, curve hosts, global actions, storage resolution on `lastSplit = none`).

## 5. Reproduction

`tools/census.py BIN CASELIST OUTDIR TIERS JOBS BATCH` (resumable JSONL per tier),
`tools/summarize.py` (all-pairs table), `tools/ccg.py` (complete-code characterization). The tools
carry the scratch paths they were run with; the case lists are regenerated by `tools/strat.py` and
`tools/p2.py` from the corpus enumeration; FX is every `claim.bin` directory under
`docs/evidence/lean-chunk-completion/*-fixtures/`, MAINNET is
`/data/illia/nearproof-deps/mainnet-w13/replay-cases/`.

Files: `census-summary.json` (per-population verdict counts and all-pairs table),
`violations.jsonl.gz` (every difference row of a flag-contained pair, ≤ 200 per pair and population),
`ccg.json`, `axioms.txt`.
