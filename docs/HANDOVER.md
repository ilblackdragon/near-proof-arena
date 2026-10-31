# Handover — 2026-10-25

## Global actions and complete-code policy — 2026-10-24 (historical)

Global deploy/use/state-init, distribution receipts and seven promise hosts now execute in the
`globalActions` successor. `completeCodeGlobal` additionally enforces authenticated complete-code
witness admission. Both pass 265 targeted cases and 83 promise chunks each; paired missing-code
checks retain native expectations separately. W05 is excluded and lanes remain available.
See [integration handoff](logs/lean-chunk-cache-global-2026-10-24.md) and the
[remaining workplan](requirements/LEAN_CHUNK_COMPLETION_WORKPLAN.md). Gas-key, historical cache
identity, obsolete-layout distribution, overlap/full observable validation and release gates remain.


**Latest code promoted to main: `8c6694412` (2026-10-25)** — five commits past `4ae27c76e`, whose CI
run was the first fully green tip. The prior promotion in this paragraph was `628551b85`; main is now
17 commits past it (62 past `25efc7265`). Those 17 add strict tier replay, the pinned pooling
allocation correction, the versioned fixture generator, the seven-case D3 smoke widening, the four
red-job repairs, the W06 widening and two base repairs (below). The five after `4ae27c76e` are
documentation-only except for the honest `RipemdRound` header correction (`2466d7299`), which removes a
claim that the rotation bridge was proved: `round_agrees` is still unproved and the file now says so.
Evidence from that `25efc7265` sequence (not re-measured here): 1,030 full runtime matches, 209 whole
chunks, 366 mutants, and a 1,788-case combined verdict checkpoint. Float evidence now adds 2,050
operator outputs, 32 input-driven bundle outputs, 1,284 input-driven chunks (1,200 accepts), and 350
mutant comparisons (302 rejects/48 accepts).
Committed regressions cover success, traps, phase priority and removal controls. Full driver build and CI smoke pass; Python tests: 58 pass / one skip.
See [execution log](logs/lean-chunk-completion-2026-10-24.md) for artifact identities and limits.
No package or gate is certified complete. W02's checker theorem, W01 computed observables,
remaining semantic adapters and representative/release/admission gates remain open.
W13 requires an authenticated witness source. W05's curve code is now merged; its whole-chunk parity
evidence obligation is still open (see "Distance to completion" below).


**Current Lean integration — 2026-10-25, merge `628551b85`.** All committed inspected
L0/L1/L2/L4/L5/L6/L7/L8 work is on the integration tip promoted to main, plus L4's gas-key promise
hosts. L4's six earlier commits through `06dffaac6` were merged in `c3976e326`. **W05's commits are
merged too** — L3's seven commits through `4a333be4e` and the curve-host integration `5bf2ee8f4` are
ancestors of main, and `lane/lean-chunk-L3` tip `34f4daed2` has 0 unique commits. What remains open is
W05's *evidence obligation* (whole-chunk parity for every curve host), not its code. Lanes/worktrees
remain intact. See the [merge ledger and fresh validation](logs/lean-chunk-integration-except-w05-2026-10-24.md).

This checkpoint also repaired two things main was carrying red: W11's broken `Layout` literals in two
test drivers (so `make d3-drivers` and `make d3-smoke` exited 2) and the resulting inventory drift.
Both are detailed under "Merged since the last checkpoint" below. Re-run those two targets before
trusting a green build on main: neither test file is in v3's `defaultTargets`, so a plain
`lake build` does not reach them.

**W06 key widening is now on main as `4ae27c76e`, and it changes the signed statement.**
That merge carries a SECP256K1/ML-DSA-65 widening: `Secp256k1.verify` is called at `D2.actDelegate`
and `D2.actDelegateL`, `TxD2.sigOk` dispatches on the new `TxD2.sigTag`, `PublicKey.handle` maps an
ML-DSA-65 key to its 33-byte `SHA3-256` handle, and the successor decoders `pTxD2Global` /
`pPkGlobal` / `pBaseGlobalKeyed` admit what the signed decoders still refuse. Measured on that tree
against the 3,138-case gap census under `allFeatures`: **3,130 accept / 8 reject / 0 out-of-domain**
(from 2,743/8/387); the 2,743 accepts and the 8 rejects are the same case set, so all 387 moves are
`out_of_domain → accept`. Re-checked on main after the merge: the two censuses
`census-signed-before-full.json` → `census-signed-widened-full.json` reproduce the signed numbers
below exactly. Those two JSONs were produced outside the repo; the population itself is reproducible
from the pinned corpora as `nearcore == "ok" ∧ expected_rel_d3 == false` over `d3c7`–`d3c10`
(3,138 cases, 898/1,376/429/435), replayed through `tools/d3/replay_successor.py --tier signed` on the
reverted-arm and widened trees.

**The earlier "signed tier is bit-identical" note is withdrawn — it is false.** `D2.actDelegate` is
shared: `checkD3` is `checkD2Core (d3Hooks …)`, which reaches `applyAction … .delegate d =>
actDelegate …`, and the pre-widening `e.secp` exclusion *was* that arm's `throw`, not an entry in
`signedExclusions` (ten features, none named secp). Re-measured against a real baseline — same 3,138
cases, `--tier signed`, delegate arm restored to the `throw` and rebuilt — the signed tier moves
**2,438 out-of-domain / 700 accept → 2,403 / 735**: **35 verdicts change, all `out_of_domain →
accept`, all within the 41-case SECP256K1 delegate set.** So the widening is *not* successor-only and
the signed statement moved. **Decided 2026-10-26: option (a).** The user accepts these 35 moves, plus
the 2 high-s delegate `reject → accept` moves, as a signed-statement strengthening (nearcore accepts all
37). This is recorded against UQ-010 in
[`research/lean-chunk-w00-owner-map.md` §3.2](research/lean-chunk-w00-owner-map.md), with the population
and reproduction command. The two candidate resolutions as originally posed:
(a) accept the 35 as a signed-statement strengthening and record it against UQ-010's named statement
of record; or (b) re-isolate the signed layer behind its own decoder so the widening stays
successor-only — the pattern the tx-key path already uses (`D2.pTxD2` excludes, `pTxD2Global` admits).
Do not merge this branch while claiming "signed unchanged"; the smoke does not catch it either, because
the two widened smoke fixtures are excluded at `signed` by `GlobalContractDistribution receipt`, not by
the delegate arm.

Deliberate-breakage controls all reproduce on the tree (measured, not copied): dropping the
`near:ml-dsa-65-pubkey-hash:v1` domain tag fails **73/266** ML-DSA cases (72 on a state-root
mismatch, 1 on `MissingTrieValue (access key)`); forcing `TxD2.sigOk`'s secp arm to `false` fails
**34/80** tx-key cases; forcing the delegate secp arm to `false` fails **30/41** delegate cases
(27 signed rejects + 3 more at `allFeatures`).

**CI is fully green on the merged tree: run `40207431857`, 16 jobs passed / 0 failed / 2 skipped.**
That includes every job that was red on `40181642479` — `rust`, `formal-checker`, `lean (zk-formal)`,
`lean (research/near-compression/wasm-base-lean)` — plus `d3 successor drivers (build + smoke)` and
`lean (spec/lean/v3)`. So the d3-smoke fix and the 10-vs-13 base-arm fix are confirmed in CI, not only
locally. Local gates on the same tree: `spec/lean/v3` 247 jobs, `zk-formal` 3,077 jobs / 0 errors,
`wasm-base-lean` 262 jobs, `make d3-smoke` exit 0, `make pin-check` all ok, coverage drift check
matches, `pytest oracle/tools` 86 passed / 1 skipped.

**One known CI flake, not a regression — and it has since passed on rerun.** Run `40214402787`
(docs-only commit `1348c421f`) failed only `rust` at `make test-rust`, in `arena-worker`'s
`fork_bomb_and_background_daemon`: `failed to spawn thread: … Resource temporarily unavailable`
(EAGAIN) when the deliberately fork-bombing child exhausted the runner's threads. That test passes
locally in 0.72 s and the same flake is already recorded in
`docs/UNTRUSTED_NEAR_ZK_AUDIT_2026-10-05.md` ("failed once from host thread exhaustion (EAGAIN) under
full-workspace parallelism and passed on two isolated reruns. That flakiness predates this branch").
The commit touched only two Markdown files, so it cannot have caused it. Re-checked on attempt 2 of
the same run: `conclusion=success`, all 18 jobs green, so the flake cleared without a code change and
`40214402787` is no longer a red run. The newest run `40218347295` (on `8c6694412`) is green too —
16 passed / 0 failed / 2 skipped, including `d3 successor drivers (build + smoke)`.

**Distance to completion:** no Gate A/B/C closure. Inventory: **222 rows, 147 implemented /
36 validated / 2 missing / 26 partial / 11 impossible-at-boundary** (recounted from the merged
`docs/research/lean-chunk-coverage.json`, not carried over). The earlier "5 missing / 23 partial"
was stale: L3's BLS merge moved `L0-host-alt_bn128_{g1_multiexp,g1_sum,pairing_check}` from
`missing` to `partial`, so 28 missing/partial rows remain. The resolving checker still uses old D2
action decoders and retains the ETH-local guard. Its 539-case replay is carried over from
`c3976e326` and was not re-run at `628551b85`; the resolving checker's source is untouched by this
merge, so "unchanged" means unchanged source, not a re-measured replay. No newly validated scoped
acceptance. UQ-006 remains open; the imported lane log's non-instant-receipt argument does not prove
impossibility.

**Next work:** shared runtime host/action/recorder adapters → semantic completion → combined relation
and tier proofs → representative replay/frozen validation → admission. Capacity, runtime errors,
float coverage, keys, actions/resolution, storage and resharding can progress in parallel behind those
interfaces. L7 can acquire authenticated witnesses and L8 can audit restricted admission now.
The [completion workplan](requirements/LEAN_CHUNK_COMPLETION_WORKPLAN.md) lists every W00–W16
remaining obligation, owner and dependency. Fresh checks at merge `628551b85`: Lean build **246 jobs
green**, `make d3-drivers` and `make d3-smoke` both **exit 0** (both were exit 2 before this
checkpoint's base repairs), `make pin-check` all `ok`, coverage and schema checks exit 0, and
`research/near-compression/wasm-base-lean` builds **262 jobs** (the 248 figure in the earlier
checkpoint paragraphs is historical, from `be3ebbca8`). The 539
replay comparisons and 49 Python passes/1 skip figures are from the earlier `c3976e326` checkpoint and
were **not** re-run here; they are not reasserted. No full release validation is claimed.

The [earlier lane audit](logs/lean-chunk-lane-audit-2026-10-24.md) and notes below are historical;
recheck L3's reported test defects against its latest changes before a future W05 promotion.

**Earlier integration checkpoint: W00 and W01 landed on main (`be3ebbca8`, pushed), with the hosted corpus prerequisite repaired.** Two work packages that had been sitting unpushed on their lanes are now on main and verified here:

* **W00 (successor interfaces + owner map).** `spec/lean/v3/NearSpecV3/Successor/` publishes compiling contracts for the seven shared interfaces (canonical checker and tiers, host dispatch, actions and receipts, resolution, trie recorder, boundary facts, differential result) — 2,191 lines, zero `opaque` stubs. `docs/research/lean-chunk-w00-owner-map.md` assigns all 28 missing/partial inventory rows and all 17 UQs an owner, disposition, source justification and test obligation, and resolves UQ-010 explicitly: **`checkD3`/`RelD3` is the statement of record**, because `Wasm.DomainD3` is not in `checkD3`'s import closure at all. All 17 UQs stay open and Gate-B-blocking.
  * Integration edit applied in `565d1b9ca`: the successor modules were *not* reachable from the default target, so a green `lake build` never compiled them. Added `NearSpecV3.Successor` to `defaultTargets`; default build goes **184 → 195 jobs** and now compiles all eight modules. Verified by re-running default `lake build`.
* **L3 (nine BLS12-381 curve hosts), merged with two defects repaired.** The BLS implementation checkpoint was verified but unmerged and unmentioned here. It adds `NearSpecV3/BLS12381.lean` and `BLS12381Pairing.lean`, wires all nine `bls12381_*` hosts into the successor `CryptoHost` table, and corrects three tower defects (Fp6 multiplication's three dropped cross terms, Fp6 squaring's sign, Fp12 Frobenius scaling `c1^p` by the Fp2 scalar) plus gating the `p1_decompress` infinity rejection on a finite point. Re-measured on the branch: build 188 jobs, host-arm tests 135/135, oracle fixtures 9454/9454.
  * **Defect 1: the fixtures were never committed.** The "94/94 directed" and "9454/9454 generated" figures came from 5.4 MB of *untracked* JSONL in the branch worktree. Merged as-is, the test found no directory and printed `0/0 ok` while exiting 0 — a vacuous pass that looked like coverage. Fixed in `675b3f7cf` by committing the 45 files; the numbers now reproduce on main.
  * **Defect 2: the test could not fail on absent evidence.** `TestBLS12381.lean` tolerated a missing directory and returned 0. Fixed in `a7b691624`: exit 2 on a missing directory or zero rows read. Verified three ways — fixtures present `9454/9454 ok` exit 0, `/nonexistent/dir` exit 2, a tampered digest exit 1.
  * The branch also failed the coverage drift check, because it never regenerated the inventory after adding the hosts; `23d811483` regenerates it (**9 rows `missing → partial`, missing 19→10, partial 9→18**, `lean_crypto_host_arms` 2→11) and updates the W00 owner map's nine BLS rows to match. **Those nine rows stay open**: the successor table models the hosts but D3α's `Host.hostCall` still has no arm and no whole-chunk case runs them.
* **W01 (harness + CI repair).** The merged `difftest-gates` job ran `corpus_manifest.py --verify` with no `--corpora`, falling back to the hardcoded `/data/illia/nearproof-deps/corpora` and exiting 1 wherever that path is absent — **the check failed on every GitHub-hosted runner and passed only on this machine.** Reproduced on main: `--corpora /nonexistent/corpora` → `corpora directory not found`, exit 1. Split into `difftest-gates` (corpus-free schema, always runs), `corpus-content-gates` (real digest walk, gated on `vars.NEAR_CORPORA_AVAILABLE`, reports **skipped** when unset — never a false green) and `d3-drivers` (builds and smokes the four drivers, which nothing did before).
  * The comparison hole is closed: `compare()` short-circuited on the `g_alpha` and `code_cache` classifier paths before comparing verdicts, leaving **1,259 of 2,269 `ood` cases with an unasserted verdict** (710 `e.wasm-α`, 373 `w.shape`, 137 `c.not_genesis`, 36 `e.secp`, 3 `c.segment`). Every input now lands in exactly one asserted bucket and the bucket sum is checked against the input count.

Merged-state verification run on main `be3ebbca8`, not copied from the lanes' logs: `lake build` in `spec/lean/v3` **195 jobs green**; `make pin-check` all `ok`; coverage drift check matches pinned sources; `make d3-smoke` **SMOKE PASSED** (5 cases, 4 drivers, controlled breakage still detects a flipped verdict); 50 harness tests OK; `make workflow-lint` clean. `research/near-compression/wasm-base-lean` still builds at 248 jobs after the `defaultTargets` change.

**Integration accounting:** measure ancestry and content rather than treating a merge title as
proof that a moving lane is fully integrated. **No inspected Lean chunk lane remains unmerged:** L0–L8
and L3/W05 are all ancestors of main (`lane/lean-chunk-L3` tip `34f4daed2` has 0 unique commits, and
`4a333be4e`/`675b3f7cf`/`a7b691624` are all in main), so the earlier "remaining checkpoint is L3/W05"
line was stale. Branches that do carry unique commits are PQ/research lanes, not Lean chunk lanes;
see "Pending integration". Re-measure before merging.

**Also this checkpoint: `main` was red and CI could not see it.** The L2 float lane added `Val.f32`/`Val.f64` to `spec/lean/v3`, and `research/near-compression/wasm-base-lean` — a separate Lake project that *depends on* that module — stopped compiling: six `Missing cases` / `Alternative … has not been provided` errors in `Event.lean`, `Tool.lean` and `Main/Exec.lean`. No workflow and no `make lean` target built that project, so the breakage sat on `main` undetected. Fixed, and both now build it (248 jobs). See the shared-rules lesson on unbuilt Lean projects.

Merged since the last checkpoint:

* **L1** — exhibited the band chunk on real data. `d3c7/ood/00-h10007-s1` (`expected_rel: true`, its only violation `e.g_alpha`) is refused by `checkD3` and accepted by the new `checkD3Proto`; 846 protocol-valid chunks sit in the band across the four corpora. Added the `nearspec-v3-check-d3proto` driver. Overlap agreement sampled 12/12; band acceptance sampled 25/25. Still open: the monotonicity proof, and termination/fuel for newly reachable executions.
* **L4** — measured D3-hook replay over 388 corpus cases (`w.shape` 227, `e.eth_implicit_local` 161) confirming which single guard fires per group; no corpus case carries action tags 9 or 11.
* **L4 gas-key promise hosts, merged (`628551b85`).** The three gas-key promise hosts appended a bare `{ text := "OTHER" }` with no `rawAction`, so `finishActsGlobal` could not type them and they stayed in `realOodHosts` even with `globalActions` enabled — the flag lifted seven of ten translated hosts. They now emit canonical borsh bytes (`toGasKeyRaw`: tag 12 | PublicKey | u128 deposit; `addGasKeyRaw`: tag 5 | PublicKey | AccessKey; `gasKeyFullPerm` tag 3 / `gasKeyFcPerm` tag 2), written against the raw `PublicKeyBuffer` because `Wasm/Host.lean` must not import D2. A zero allowance encodes as option tag 0, matching nearcore's mapping before append. All ten hosts now lift with the flag on, and all ten stay excluded with it off, so the opt-in gate is tested in both directions. The signed D3α statement is unchanged.
  * **Limit 1: no pinned-nearcore whole-chunk replay.** The new fixture `tools/d3/global-promise-fixtures/gas-keys.wasm` (713 B) is a VM/action-log and serialization control: the suite decodes its emitted actions to `.transfer 16`, `.toGasKey` (deposit 16), `.addKey` (`.gasFull 0 4`) and `.gasFc 0 2` with `allowance = none` and methods `f,g,m`. It proves the emitted bytes decode to the intended typed actions, **not** that a chunk carrying them is accepted. The inventory's acceptance test for those rows stays unmet.
  * **Limit 2: target-side gas-key execution is out of scope here** — funding, nonce indices, withdraw/transfer out and key deletion with balance are separate.
  * **Two base repairs came with it.** Rebasing onto main's W11 resharding commit surfaced that W11 added three fields to `Layout` without updating `TestGlobalActions.lean` and `TestStorageResolution.lean`, which use the anonymous constructor `⟨boundaries, shardIds, idToIndex⟩` — that form does not fill structure defaults, so both stopped compiling and `make d3-drivers`/`make d3-smoke` exited 2 on main. W11's "full build green" missed it because neither file is in `defaultTargets`. Fixed with named fields, values unchanged. The chunk inventory also needed regenerating for W11's `Layout.lean` hash move; only `source_sha256.Layout.lean` changes and all 222 rows are identical.
* **L6** — **the genesis checker's soundness correction.** The committed draft re-implemented the non-genesis tail and dropped ten endorsed-header comparisons, wrongly accepting 307 header mutants. `checkD2CoreG` now delegates to `checkD2Core` for `!B2.isGenesis`. Verified over the full replay: **exactly 137 verdicts change, all `out_of_domain → accept`, all genesis; zero non-genesis changes across 115,147 cases.** 137/137 genesis cases accept. Adds inventory rows for the genesis transition and the two resharding guards.
* **L7 / W01** — differential-harness audit, UQ-014 answered per branch, readiness assessment, plus two new oracle test scripts. Then the W01 repair above: the red corpus gate, the 1,259 unasserted exclusions, and CI coverage for the four D3 drivers. Its lane log (`logs/lean-chunk-L7-2026-10-24.md`) records the full 115,284-case accounting; that run needs the pinned corpora and saved verdicts, so it was **not** re-executed on main — the merged-tree evidence is the schema gate, the 50-test suite and `make d3-smoke`.

Remaining Lean transition work, success criteria and parallel execution dependencies: [completion workplan](requirements/LEAN_CHUNK_COMPLETION_WORKPLAN.md). The plan's gates remain open; W00–W16 are work packages, not completed milestones.

Only unfinished work and shared rules belong here. Evidence/history: [logs](logs/).
Remove completed items; update their logs instead. Old lane labels are not proof of live activity.

## Pending integration

- **Lean chunk lanes: all merged.** L0/L1/L2/L5/L6/L7/L8 are ancestors of main with zero unique
  commits. **L3 and L4 are also merged now** — `lane/lean-chunk-L3` tip `34f4daed2` and
  `lane/lean-chunk-L4` tip `07fe9839c` both have 0 unique commits against main. The BLS fixtures and
  the fail-closed runner repair are on main and reproduce (9454/9454 ok, exit 2 on absent evidence);
  L4's resolving hook, successor checker, guard proofs and evidence are on main via `c3976e326`, and
  its gas-key promise hosts via `628551b85`. **Do not treat L4's 539 identical verdicts as positive
  global-path coverage** — that caveat still stands, as does L0-D3-006's negative result.
- **`lane/pq-hostfinal` is merged and its worktree is gone.** Re-checked by ancestry, not by message: `origin/lane/pq-hostfinal` = `54ce39baf`, and every lane commit — `bdf80d018`, `f7b1a6e0c`, `598d85bd2`, `45af882a9`, `ceee23052`, `14af4935e`, `7cddf9289`, `e13129b84`, `3fb84f5f1`, `2e90a315f`, `87d53f22c`, `78436ac9f`, `229518416` — is an ancestor of main. 0 unique commits. The promise encodings and the `Coverage.lean` tautology fix are on main; the lane's RIPEMD work is on main but **incomplete** (see "RIPEMD `round_agrees`" under Remaining work). Nothing from this lane needs re-merging; only the open proof items below.
- **`lane/lean-chunk-L0` (W00) and `lane/lean-chunk-L7` (W01) are merged** (`f4b9b4837`, `be3ebbca8`) and pushed. The L0 branch tip `190841d3d` and L7 tip `1edbf9cb4` are ancestors of main; the integration edit on top is `565d1b9ca`.
- `pq-chunk-e2e` (`lane/pq-chunk-perf`): **merged 2026-10-24.** Supersedes the earlier "not integrated" note. The production-target aggregation measurements, the depth-2 geometry wall, the size law and the `S` reconciliation are now on main, with the full evidence and the exact log citations in
  **[`logs/pq-agg-depth2-production-2026-10-24.md`](logs/pq-agg-depth2-production-2026-10-24.md)**.
  Read that file before acting on any aggregation number; four corrections it makes to earlier
  text are worth knowing up front:
  * **The root-shaped 2-child production node is 276,269–276,789 B** (`k_first=1`, 131 queries, `total=268.2`), **23.2–23.7 KB under the cap** — not 267,513 B. The 267,513 B figure is a **chain-shaped** node (`k_first=2`, 126 queries); both are real, but only `k_first=1` matches the delivered final layer, whose VK says so. (The 520 B spread between two identical-parameter runs is the same transcript-sampled effect that makes the cap non-structural.)
  * **At production `lb=7` the depth-2 deficit is 1 bit** (`log_height 21` vs `log_stacked_height 20`). The often-quoted `23 > 22` pair is the `lb=5` row, and `n_stack=20` fails on the field's 2-adicity (`2+20+7 = 29 > 27`), not on layout.
  * **The only structural exit is 18.3% fewer SHA compressions per child** (1,829 of 10,021). `multiproof` is measured not to help (`merkle_nodes` stays 464 in every lever config), and digest narrowing cannot help: all widths 40–48 pad to one 128 B SHA block.
  * **41-byte digests are refuted for the NV tree** (`104 != 90` at `nv/hash.rs:262`, 3,568 times); `d=40` is representable but its 16.7% is an in-circuit *unit* cut, not a compression cut. The ~6.9 KB / 5.8 KB margins for `d=40` are projections, not measurements.
  Nothing in it is a 1 Pgas result: every measured node is depth 1, and every production depth-2 attempt panicked before producing a proof.
- Check fresh Git/process state before touching any worktree, including the Claude checkout. MEMIO is merged; its remaining proof obligations are below. Recovery inventory: [worktree audit](logs/worktree-reconciliation-2026-10-23.md).
- `lane/pq-tail-architecture` (**~35 k lines across a dozen-plus commits, not on main and not referenced by this handover before now**): the PQ "tail" (succinct, recursively composable, sub-300 KB, 1–2 s final-proof) architecture experiment. Its own README is careful about what is *not* established, so do not read the byte counts as achieved goals. Highlights: a lattice/serialization carry defect was found and repaired; actual export **165,950 B** with both honest exports decoding and verifying in fresh processes against independently computed roots; a binary/lattice component (private 64 KiB SHA-256 message, 1,025 compressions) at 97,745 B analytical proof on one core; and declared-profile packets at 258,792 / 274,763 / 279,454 B with all nine width mutations rejected. But **none meets the 2 s final-proof deadline** (17.26–20.86 s wall on a loaded host), and the largest honest D0a witness (156,624,112 cells) passes constraint/bus precheck then **fails the fixed profile's 65,536-row capacity — no proof exists for it**. Open in the lane's own words: initial/outer PCS, structured attacks, transcript security, NEAR binding and history recursion; receipt binding, wire codec and PQ audit for the hash template; decoder safety for arbitrary metadata. Integrate deliberately: this changes assumptions away from the SHA384-only baseline. See `research/near-compression/tail-architecture/README.md` on the branch.
- `lane/d3-join` (**2 commits**): the hook-level `functionCall`→`prepare` lift analysis and the working "peel recipe" measured to 16 fully-open `do` goals. The bullets under "D3 succinct proof" already cite this finding, so the lane's remaining unique content is the two log commits themselves; merge or fold them into the cited log before retiring the worktree.

## 0. Goal and standing user directives

**2026-10-23 priority:** complete the proof-system-independent Lean chunk transition and arena
before treating any particular succinct-proof implementation as a prerequisite. Agent workstreams,
dependencies and acceptance gates are in
[`requirements/LEAN_CHUNK_TRANSITION_PLAN.md`](requirements/LEAN_CHUNK_TRANSITION_PLAN.md).
The full PV86 semantic target is broader than today's D3α domain; existing signed challenges remain
unchanged and broader coverage requires a versioned successor.

## Remaining work

- **PQ tail architecture** (`lane/pq-tail-architecture`, merged to main `7838aef7b` on 2026-10-31 to preserve it): **unproven research direction**. Lattice (LaBRADOR/SIS) circuits give flat 150–250 KB packets (NPMULT04 receipt+Wasm 250,226 B, 7.2 s CPU; Wasm ~1,452 AND/step). But the headline packets likely model below 128 bits (ring-648 main commitment 79 bits on the {3889,2917,4861} moduli), there is no accumulation/folding (2,048-step wall vs ~10⁹ steps per 1 Pgas), there are no GPU measurements, coverage is the D0a slice plus a Wasm subset, and nothing is linked to `RelD3`. It also needs an owner decision on accepting a lattice assumption. Go/no-go gates: [evaluation](../research/near-compression/tail-architecture/EVALUATION-2026-10-31.md).

- **D3 succinct proof:** build the D2/D3 chunk AIR, state render/overlay replay and real Wasm/state/recursion connection. The shipped D3 artifact proves witness re-execution, not succinctness. [Latest preparation/join analysis](logs/pq-prepare-link-2026-10-23.md).
  - **Scoped in two design docs (2026-10-23), with open PROPOSALS P-D2-1…6 / P-D3-1…5 awaiting a user decision:** [D2 design](zk-formal/V3-D2-DESIGN.md), [D3 design](zk-formal/V3-D3-DESIGN.md). Read them before starting AIR work; the headline findings are that **no D2 AIR exists and has never existed** (`grep nearAirV3D2` = 0), **D3 is strictly gated on D2** (`checkD3` *is* `checkD2Core (d3Hooks pv86)`), and **`RelTier .d2`/`.d3a` are unbounded** so no completeness claim holds at their current statements. Order is L0 (corpus maxima) → `D2a` spec → native/AIR split → tables → assembly → budget measurement; D3 work other than its own tier restatement is speculative until D2's AIR lands.
  - **Judge-budget wall (design-level, not scheduling):** D0a is 2.43 h of the 4 h elaboration budget, D1a projects 2.8–3.5 h, and D2 lands at **3.4–4.7 h** on the same per-table architecture — already over. `V3-D2-DESIGN.md` §5.3 gives three options (split the certificate / coarsen tables / native-extract more) and recommends native-extraction first because it adds no new admitted statement.
  - **Join: resolved, negatively then positively.** `compose_pv86` is *not* an independent join — `compose_pv86_premise_iff_conclusion` (`ZkFormal/PQ/Join/Compose.lean` §4) proves `ArmAgrees pv86 sa → (StateSide pv86 cb w sa ↔ RelD3 cb w)`, so its premise is its conclusion. It is retained as a documented non-join; its real content is the fold (`checkD2Core_patch`). **Do not cite it as the join and do not "strengthen" it.**
  - **The non-vacuous composition is `Read.check → RelD3`** (`examples/reexec-v3-d3/formal/ReexecV3D3/ReadCanonSplit.lean`, wired into `Certificate.lean` so it cannot rot). `check_iff` decomposes acceptance into `RelD3 cb w ∧ encodeReads cb w (d3Reads cb w) = w`; the second conjunct is absent from `RelD3`'s statement, so the premise is strictly stronger. Separated by witness across the whole public corpus **[M]**: 172/172 `RelD3`-true raw witnesses rejected by shipped `out/verify`, 10/10 canonical forms accepted on identical claim bytes (case `d3-04-h10105-s4`: same 5267 B claim, same 6023 B witness size). Reproduce with the three commands in the log. *Caveat:* a byte-flip mutant also destroys `RelD3`, so the 11/11 mutation-binding sweep is binding evidence, not the separation evidence — the separation evidence is the raw-witness vs canonical-form pair.
  - **Hook-level `functionCall`→preparation lift remains open.** `runCall_done_prepare_ok` is `[K]` at the `Run`/`prepare` level (a VM-produced `.done` implies `prepare = .ok p`); the converse is *false* (a compilation-abort line parses through `lineOutcome` as a zero-gas ordinary action failure the chunk still accepts). The route through `functionCall`'s do-block is now measured rather than guessed: the first blocker is **not** `runCall` opacity but the bind `let some acct := st.account`, whose matcher sits on a projection that `split`, `rw` and `cases hacc : st.account` all refuse to enter. Working recipe, probed to 16 fully-open `do` goals: `obtain ⟨o, account, actor, deploys⟩ := st` then `dsimp only at h`, `cases account`, `obtain` on `Acct`, `cases contract`, then `by_cases` + explicit `ite_true`/`ite_false` for the guard ifs — **never `split` a guard** (no budget knob; it fails outright on the balance guard). Remaining work is the `env.codeOf`/`contractOOD`/`runCall` scrutinees plus per-goal dead-branch closure. Do not `unfold functionCall` (146 goals). The lane log `docs/logs/d3-join-2026-10-23.md` (commit `fe491417f`) exists only on `lane/d3-join`, which is **not** merged — so this link is dead on main; read it from `/data/illia/nearproof-wt/d3-join/`. Do not import the untracked `Final.lean` containing `sorry`.
  - **D3 kernel non-vacuity: signed `RelD3` and successor `allFeatures` closed (2026-10-26).** `lake build NearSpecV3.Examples.RealCaseD3` (≈3.5 min, ≈21 GB peak, not in `defaultTargets` because hosted CI runners have 16 GB) kernel-checks `RelD3` on the real D3-only chunk `d3c7/d3/06-h10006-s0` (the `d3ed` contract is decoded, prepared, instantiated and run in the kernel; the receipt fails on an `ed25519_verify` host error and the chunk is accepted), and `¬ RelD3` on the nearcore-rejected mutant `d3c10/mutants/00-h10074-s1-code.drop.0` (27 s, 7 GB). Axioms: `propext`, `Classical.choice`, `Quot.sound`. Details and measurements: `spec/near-chunk-validation-d3.md` §12.1.
    - *Why the earlier attempts failed.* (1) `decide` on `RelD3` itself cannot work: its instance is `decidable_of_iff` over a theorem. The fix is to decide the Bool mirror `acceptsD3` and transport the result with `relD3_iff_acceptsD3`; no definition changes and no versioned successor is needed. (2) Kernel cost depends on the contract, not on the relation's form. WASM preparation's `ByteArray.extract` is list-backed and super-quadratic in the kernel, so the 958-byte d2program case exhausts 24 GB in 99 s while the 369-byte `d3ed` case closes. (3) A contract that touches storage cannot be decided at all: `Wasm.TTN`'s overlay, recorder and accounting caches are `Std.HashMap ByteArray`, and `ByteArray.hash` is an `opaque` extern.
    - *Successor blockers.* `Logged/LazyTrie`'s `(mf, sizeOf)` well-founded recursion compiles through `Lean.opaqueId`, so the kernel stops there. This is fixed: structural fuelled forms in `Logged/LazyTrie.lean` are proved equal in `Logged/LazyTrieKernel.lean`, and they are used at the four call sites. The recorder blocker is fixed too: `Wasm.TTN`'s byte-keyed maps are now `TTN.BMap` (a `Std.TreeMap` under lexicographic byte order), which the kernel reduces; `Tier.rel .allFeatures` and its negation are kernel-checked on the same two chunks. This edits definitions in `checkD3`'s closure without changing meaning (maps used only via `insert`/`contains`/`get?`); native verdicts and reasons are unchanged on all 577 fixtures and 3,138 census cases on both tiers and on all 235,716 corpus cases on `allFeatures`. See spec §12.1.
- **Host/state:** discharge `H0`/`HoldRow`, per-row gas/boundary and HOST message-tape correspondence. MEMIO still assumes `HostBLinked.linked`/`unique`, consumed-byte liveness and `BufOK`. CD needs `RealStoreMatchesTables`, `CdKeynibFromHostB`, `UpsV3AppliesLog`, memory-bound preservation and a parameterised upsert AIR (current polynomial hard-codes `[0,15]`). [MEMIO](logs/pq-memio-finalized-2026-10-23.md), [CD](logs/pq-d3-air-2026-10-22.md).
- **Wasm coverage:** IF checker soundness/full execution integration, result-carrying IF, and `loop`/`memory.grow`/`call_indirect` coverage. Conditional IF row facts are already on main. [IF](logs/pq-if-air-2026-10-22.md).
- **Hashes/receipts:** RIPEMD `round_agrees` (`bl'`/`br'`), general rotation bridge, feed-forward/digest bus and message binding; Keccak round agreement, absorb/squeeze and state bus; `RIDS`/`SRC`/`RCL`, `newReceipts`, host-trace/generator/byte-binding obligations. Separate Ed25519/SHA-512 proof layer is unbuilt. [Host/receipt gaps](logs/pq-hostfinal-2026-10-22.md).
  - **Promise encodings: closed, and the "done" claim is now checkable.** `ZkFormal.PQ.Receipt` proves all eleven README §5.4(c) functions (`remaining_eleven_closed`), that every action-kind row with `addA = 1` has an `actionInstance` (`promise_encodings_cover`, with `promise_encodings_cover_discriminates` showing the predicate rejects a fabricated uncovered row rather than passing vacuously), and that the six `addR = 1` ids are exactly the six `receiptInstance` shapes (`receiptCreators_are_six`). Axiom audit measured: `promise_encodings_cover` and `receiptCreators_are_six` depend on **no axioms**; `promise_encodings_cover_discriminates` uses `[propext]`; `remaining_eleven_closed` uses `[propext, Quot.sound]`. So "axioms: none" is true only for the first two — do not generalise it to the family. Remaining in this family: `promise_yield_resume*` pushes an `i32` result tag 0 while the chip's result tag is fixed at 1 (`results/pq-host-promise/DESIGN.md` §3), so those two rows do not yet match the chip's fixed result tag.
  - **RIPEMD `round_agrees` is *not* proved, and the file says so.** `WasmBase/RipemdRound.lean` contains the machinery — five gated sums in general form (`gsumG`) with instances, `xsel_eq`/`rot_eq`/`f_eq`/`gsel_profile`, the bit-extraction lemmas `bitOf_ofBitsN`/`testBit_ofBitsN`/`ofBitsN_congr`/`ofBitsN_foldl`, and `curWord`/`nxtWord`/`nxtWord_eq_cur`. An earlier note here said "plus 8 of the 10 next words"; that overstates it — the file has **zero** per-word instance theorems. The generic `nxtWord_eq_cur` plus `RipemdAir.shiftConstraints` reduce the eight wiring-only words in prose only. The two genuinely computed words, `bl'` and `br'`, need the four-addition chain composed with the `f` column, the selected message word and the rotated `t3`, matching the spec's `rot32 (…) sl[j] + el`. The header states this rather than claiming the rotation bridge is proved; `rotl32n_is_rot` is only a `decide` over 80 offsets × 8 values, not a proof for arbitrary `v`.
  - **RIPEMD row AIR cost, measured:** 1,608 columns × 80 rows = **128,640 committed cells/block**, 13.8× SHA-256's 9,333. The earlier "≈9–11 k" figure was wrong and is retracted. The row AIR's 2,625 constraints and 13 spec-matching digests are confirmed by the build's own report, but the AIR proves only "the digest follows from the message columns": 2 message columns remain **free**, and there is no feed-forward row family or digest bus. `RipemdAir.lean` names a fourth obligation the earlier note here omitted — the **`X`-column message-word binding**, that the 512 message columns really are the block's bytes at the call's `(ptr, len)`. The `X` columns carry no interaction, so this is the same stated join obligation `Sha.HashInputLink` carries (`HOSTB`/memory ↔ bytes) and is not closed by the AIR's constraints. Each of these is a named gap, not a fixed defect.
- **Recursion/security:** production-parameter aggregation node, real D3 segment leaves, single-database `NodeOK`, concrete family-QROM instantiation, WHIR transfer, arbitrary-trace NV semantics and concrete-hash bridge. The 299,967 B D0a packet is a linear chain with 33 B margin; another valid replay exceeds 300 KB. Test-target tree measurements do not certify production trees. Keep `security_established=false` until obligations close. [Aggregation](logs/pq-agg-tail-2026-10-22.md), [security](logs/pq-paper-blockers-recheck-2026-10-21.md).
  - **Superseded 2026-10-24/25: depth 2 and depth 3 both prove at production targets.** The `ns19/lb6` pairing keeps `l_skip+n_stack+log_blowup = 27` while raising the stacked ceiling to `2^21`: `AGG_DEPTH2_OK leaves=4` is **315,913 B** (700.5 s, 18.76 GB) and `AGG_DEPTH3_OK leaves=8` is **322,027 B** (752.2 s, 21.45 GB). That is +4–6 KB for one level, then flat. The remaining problem is size, not geometry: 315,913 B is 5.3 % over the cap. A second exit from the height wall, `sha_instances = 2` (unimplemented), is in [`logs/pq-agg-sha-instances-2026-10-24.md`](logs/pq-agg-sha-instances-2026-10-24.md); measurements in [`logs/pq-agg-depth2-legal-2026-10-24.md`](logs/pq-agg-depth2-legal-2026-10-24.md) and `research/near-compression/results/pq-agg-depth-law/EXTRAPOLATION-1PGAS.md`. The bullet below is kept as the falsified record (true only at `log_blowup = 7`).
  - *(Superseded)* **A root-shaped 2-child production node fits the cap; depth 2 does not fit the field.** Measured on `lane/pq-chunk-perf` (now merged): a 2-child node at the delivered final layer's own levers (`k_first=1`, 131 queries, 268.2 bits) is **276,269–276,789 B**, ~23.5 KB under the cap. But a node with **two NV children cannot be proved at production `log_blowup = 7`** — it needs 1 more bit of stacked height than the field's 2-adicity allows (`log_height 21` vs `log_stacked_height 20`; `n_stack=20` with `lb=7` is `29 > 27` outright). Every blowup step down costs exactly the bit it buys, so no parameter closes it; only `lb=3`, i.e. test-target soundness, fits. The "bytes flat in depth" result (132,301 B at depths 2–4) is therefore a `lb=3` result that does **not** transfer. The sole structural exit is **18.3% fewer SHA compressions per child** — a circuit change, unimplemented; `multiproof` is measured not to help. Details, citations and four corrections to earlier numbers: [`logs/pq-agg-depth2-production-2026-10-24.md`](logs/pq-agg-depth2-production-2026-10-24.md).
- **D1:** `A7D1Step`, `LinkD1CoreStmt`, R1/R2/A1; exercise stub/nmem queries and reprove the 33-table path. Archived phase-2 drafts fail through `LinkSched`/`RecModel`/`A7Bound`; L4's reference-prover draft fails honest tests. [Plan](zk-formal/V3-D1-PHASE2.md), [recovery](logs/worktree-reconciliation-2026-10-23.md).
  - **L4's successor-hook work is now fully merged — this note previously said the opposite and was stale.** The "L4 — measured D3-hook replay" merge (`e6c97d55b`) took 3 commits; the 6 later ones (`147e7c1d0`…`06dffaac6`) were merged in `c3976e326`, and all are ancestors of main. They carry the global-contract/ETH-guard analysis in `NearSpecV3/D3/GlobalContractCall.lean` and the successor chunk layer in `GlobalContractChunk.lean`, plus `probe-l4`/`nearspec-v3-check-l4` drivers, all present on main. The analysis below is what those commits established, and its negative result stands. The result is a **negative** one for `L0-D3-006`: a delegate cannot lift that row, because `resolvedContract_local_stays_local` shows the delegate only ever produces `.none`/`.local _`, so the ETH guard's premise survives it (`resolveAccount_eth_local_premise_survives`). Lifting `L0-D3-006` needs a narrower guard in `checkD3`, not a delegate — unlike `L0-D3-008`, which the delegate does close. `GlobalContractChunk.successorHooks_functionCall_{none,local}` prove the hook change is a no-op off the wallet-redirect domain. Axioms measured: the four guard theorems use `[propext]`; the two successor-hook theorems use `[propext, Classical.choice, Quot.sound]`. Builds clean on main (the merged tree compiles 246 jobs). The mechanical `docs/research/lean-chunk-coverage.json` and `lakefile.toml` conflicts anticipated on its branch were resolved in `c3976e326`; the Lean sources merged cleanly as expected.
- **Arena:** verify actual signed admission reports; deployment/local PASS is not admission. Resolve D0a supplied-witness rejection/resubmission status against [live-run evidence](logs/v3-deploy-d0a-2026-10.md). Successor work: one canonical relation with proved tier restrictions, measured workload weights/succinct thresholds, full semantic coverage, guest-image isolation upgrade. Python VM independence remains unresolved ([provenance](research/python-vm-independence.md)).

## Shared rules and lessons

- Binius `assert_false` checks only the MSB; use `assert_zero` for full-word/range guards. Test malformed private witnesses, not only mutated public inputs. [Failure/repair](../research/near-compression/tail-architecture/STRICT_METADATA.md).

- Target: artifact-bound, independently checked chunk validation replacing `validate_chunk_state_witness`. No weakened measurement rules or hidden domain assumptions. Prove semantic claims; label tests, conditional lemmas and estimates accurately.
- Keep one `near-chunk-v3` challenge with coverage tiers. Signed challenges, frozen `oracle/v3` and pins are immutable (`make pin-check`). Broader semantics/scoring need a versioned successor. Signed R5 forbids composition; long-term recursion research is separate. `G_α≈3.45 Tgas` is not 1 Pgas. Decisions: [D3 study](zk-formal/V3-D3A-STUDY.md), [contracts](CONTRACTS.md).
- One worktree per agent; integrate on `integration/*`, preserve concurrent edits, verify ancestry **and content**, push checkpoints. Never hard-link `.lake`; copy/reflink or rebuild. Check free disk before builds; retire merged worktrees only after preserving unique evidence.
- Rebuild Lean tools **and** Rust binaries before KATs; tracked binaries and mtimes can lie. Ensure new modules are root-imported and actually compiled. Audit theorem axioms and premises; green job counts, named `Prop`s, differential vectors and vacuous reductions do not establish soundness. Run relevant builds/tests, axiom audits, pin-check and affected proof manifests before promotion.
- **A Lean project not in `LEAN_PROJECTS`/the CI matrix is not built, so its breakage lands silently.** This has now happened twice. `spec/lean/v3` was invisible until `d4588471e` added it; then the L2 float lane added `Val.f32`/`.f64` in `spec/lean/v3`, and `research/near-compression/wasm-base-lean` — which *depends on* that module — stopped compiling on `main` with six `Missing cases`/`Alternative … has not been provided` errors in `Event.lean`, `Tool.lean` and `Main/Exec.lean`. Nothing caught it because no workflow and no `make lean` target built it. Fixed by adding the project to both; `make lean` now builds four projects and `wasm-base-lean` at 248 jobs. When adding or consuming a Lake project, add it to `LEAN_PROJECTS` and the CI matrix in the same commit, and check whether it is a path dependency of something already gated.
- **Test a join by asking whether its premise could be the conclusion.** Three placeholder relations were found in the D3 path by this one question and nothing else: `JoinStmt` (`RelD1a → RelD1a`, discharged `exact hrel`); `WasmRunStmt`'s host clause `∀ ts ∈ hostTimes, resp ts = resp ts` (tautology by `rfl`, documented as HOST-chip correspondence, so `resp` was inert — see `wasmRunStmt_iff`/`wasmRunStmt_resp_inert`); and `Statement.Compose`, which is a `def ... : Prop` with **no** theorem inhabiting it, as are `Joint`, `WasmHalf`, `StateHalf`. Relocating a vacuous premise one layer down (as `compose_pv86` did to `join_additive`) is the default failure mode, not an unusual one. Corollary: a relation that does not mention one of its arguments cannot constrain that argument — the `resp`-unused linter warning was the proof.
- Use dependency setup scripts; a compiling stale deps checkout may not match the recorded patch. Never bypass drift checks.
- Heavy work: `HEAVY_MEM=16G taskset -c 8-15,24-31 /data/illia/nearproof-deps/bin/heavy <cmd>` (32G only for D2 kernel evaluation). CPUs 0–7/16–23 belong to w1; stop only in logged empty-queue windows and restart. Avoid concurrent memory oversubscription.
- Loopback + `tailscale serve` only, never funnel. Keep secrets outside Git and output.
- Check AIR activity/count semantics: inactive HOSTB response/register rows invalidate inverse grouping; host restarts require fresh gas bounds; `HOSTO.mult` need not be a bit. Use the real table in active-row filters. Storage host IDs are 57–60; older canonical numbering collides with hashes.
