# Parallel execution plan for the Lean chunk completion workplan

Date: 2026-10-23. Baseline: `main` at `8ac3de9f6` (= `origin/main`).
Companion to [`LEAN_CHUNK_COMPLETION_WORKPLAN.md`](../requirements/LEAN_CHUNK_COMPLETION_WORKPLAN.md)
(W00–W16) and [`LEAN_CHUNK_TRANSITION_PLAN.md`](../requirements/LEAN_CHUNK_TRANSITION_PLAN.md)
(Gates A/B/C, authoritative).

This document is the *dispatch plan*: which work packages can run in parallel subagents right now,
which cannot, what each agent may touch, and where the collisions are. It assigns nothing and starts
nothing; the transition plan remains the only place gates close.

## 1. Measured starting state

Re-measured against source, not carried forward from lane logs.

| Fact | Value | How measured |
|---|---|---|
| Inventory rows | 222: 147 implemented, 36 validated, 19 missing, 9 partial, 11 impossible-at-boundary | `docs/research/lean-chunk-coverage.json` |
| Missing/partial rows | 28, all with owners | same |
| Unresolved questions | 17 (`UQ-001`…`UQ-017`), all owned | same |
| Lane branches | all 9 at 0 unique commits vs main except **L4** (3 ahead, 15 behind) | `git rev-list --left-right --count` |
| L4 active work | 3 commits: `147e7c1d0`, `7d983f391`, `9e6bc2b35` — successor hook, successor chunk checker, guard-premise gap theorems | `git log main..lane/lean-chunk-L4` |
| L4's base | `137dae895` — **does not contain** `GenesisD3.lean`/`ReshardingD3.lean` | `git cat-file -e lane/lean-chunk-L4:…/GenesisD3.lean` → absent |
| Free disk | **72 G of 880 G (92 % used)** | `df -h /data` |
| CPU / RAM | 32 cores, 125 G (117 G available) | `nproc`, `free -g` |

Two consequences that shape the whole plan:

* **L4 must be treated as in-flight.** Its branch predates the genesis/resharding merge, so its
  eventual integration needs a rebase across 15 commits, not a fast-forward. Any other agent editing
  `spec/lean/v3/NearSpecV3/D3/` or the v3 `lakefile.toml` will collide with it. W07 therefore goes to
  L4 only, and no second agent may touch `D3/GlobalContract*`.
* **Disk is the binding constraint, not CPU.** Each v3 worktree costs ≈1.0–1.4 G; a full `.lake`
  build ≈ 360 M. ~10 more worktrees plus build artifacts fits in 72 G but leaves little headroom for
  the 115,284-case replay outputs. Reuse existing worktrees; do not create a worktree per package.

## 2. Collisions to resolve before dispatch

### 2.1 My own CI addition is broken on hosted runners (W01's first item, confirmed)

The workplan flags this and it is correct. `.github/workflows/ci.yml`'s new `difftest-gates` job runs
`corpus_manifest.py --verify …` with no `--corpora`, and the script hardcodes
`DEFAULT_CORPORA = "/data/illia/nearproof-deps/corpora"` and `sys.exit`s when the directory is absent
(`tools/d3/corpus_manifest.py:27,84-85`). On a GitHub runner that path does not exist, so **the job
fails on every push**. It passed locally only because this machine happens to have the corpora.

Verified: `python3 tools/d3/corpus_manifest.py --verify … --corpora /tmp/does-not-exist` →
`corpora directory not found`. Note the exit status observed was 0 only because the shell captured
`tail`; the script's own `sys.exit(string)` exits 1.

This is the first thing to fix: the job as merged is worse than no job, because a permanently red
check trains people to ignore CI. Either provision content-addressed corpora for that runner, or split
the job into (a) a genuinely corpus-free schema/manifest-shape test and (b) a corpus-content check
gated on corpus availability with a distinct name. The workplan's wording — "must not be called a
corpus-content drift check" — is the right constraint.

### 2.2 The `difftest_d3` comparison hole is real but my first estimate was wrong

L7's "1,259 verdicts compared to nothing" **reproduces exactly**, but only by tracing the harness's
own control flow — my first attempt from `meta.json` alone gave 2,269 and was wrong. The `compare()`
function in `oracle/v3-d3/tools/difftest_d3.py:81-125` short-circuits on two classifier paths before
the accept/reject comparison, so those cases *are* compared, just not on the verdict:

| population (ood family, Lean `out_of_domain`) | count |
|---|---|
| total | 2,269 |
| counted via the `g_alpha` classifier path | 1,010 |
| counted via the `code_cache` classifier path | 279 |
| **compared to nothing** | **1,259** |

All 1,259 have `expected_rel: true`, i.e. nearcore accepted them. By reason: 710 `e.wasm-α`,
373 `w.shape`, 137 `c.not_genesis`, 36 `e.secp`, 3 `c.segment`. So "0 disagreements on 115,284 cases"
is precisely "0 mismatches among the 112,736 the harness compares" — L7's §4.4b accounting is right.
W01's job is to make those 1,259 explicit: an out-of-domain verdict with no asserted reason is an
unconditional pass, which is what the workplan forbids.

### 2.3 L4's uncommitted replay evidence

`evidence/lean-chunk-L4/replay/d3-hook-full-replay-{539.txt,summary.json}` are untracked in the L4
worktree. Preserve them; do not let a rebase drop them.

## 3. What can start now, in parallel

Ordered by (independence × value). "Blocked by" lists only *acceptance* blockers; coding can start
earlier unless stated.

| Wave | Packages | Why now | Hard blocker |
|---|---|---|---|
| 0 | **W01** (CI fix + comparison completeness), **W15** (admission audit) | W01's merged job is red; W15 depends on nothing | none |
| 1 | **W00** (inventory + successor API) — **serialization point** | Every W02–W11 package consumes its interfaces | none |
| 2 | **W02, W03, W04, W06, W09, W10, W11, W13-capture** | Independent files, independent proof/fixture work | W00 interface for *closing* |
| 2′ | **W05** (curves, splittable by curve), **W07/W08** (L4-only) | Independent arithmetic; L4 owns dispatch | W00 for closing |
| 3 | **W12** (combined successor) | Integrates accepted increments continuously | W00–W11 |
| 4 | **W14 → W16** | Release gates | W12, W13 |

### 3.1 Concurrency limit: 4–6 agents, not 16

The workplan's DAG has 11 semantic packages; launching 11 agents at once is wrong here because:

* disk headroom is ~72 G and each active Lean build tree is ~1.4 G plus replay output;
* W00 is a genuine serialization point — parallel API assumptions would produce incompatible
  adapters, which is exactly the "three permanent trusted transcriptions" failure W12 warns about;
* two pairs share interfaces by design (W07/W08 resolution; W09/W11 trie accounting) and must agree
  in W00, not converge later.

Recommended: **W01 + W15 + W00 concurrently first (3 agents)**, then 4–5 semantic agents against the
published W00 API. Add agents only as lanes free up.

### 3.2 Suggested first dispatch (6 agents)

| # | Package | Worktree | Branch | First deliverable |
|---|---|---|---|---|
| A | W00 | `lean-chunk-L0` | `lane/lean-chunk-L0` | Interface signatures + compiling adapter; owner map for the 28 missing/partial rows and 17 UQs |
| B | W01 | `lean-chunk-L7` | `lane/lean-chunk-L7` | CI job that does not depend on `/data/…/corpora`; re-derived comparison denominator |
| C | W15 | `lean-chunk-L8` | `lane/lean-chunk-L8` | Hashes + status of the existing signed D3α admission reports |
| D | W02 | `lean-chunk-L1` | `lane/lean-chunk-L1` | Fuel/termination audit; monotonicity + overlap theorems |
| E | W03+W04 | `lean-chunk-L2` | `lane/lean-chunk-L2` | LoadingError parity; float-contract generator |
| F | W06+W05(secp) | `lean-chunk-L3` | `lane/lean-chunk-L3` | secp256k1 tx/delegate verification; ML-DSA codecs |

Held back deliberately: **W05's BN128/BLS** (huge arithmetic, better after W00), **W07/W08** (L4 busy
and its branch is 15 behind), **W09/W11** (need the W00 trie-accounting interface), **W12** (needs
accepted increments), **W13-execute/W14/W16** (need W12).

## 4. Per-agent rules (enforce in every prompt)

These come from the workplan and the transition plan; restating them here so each subagent prompt can
point at one place.

1. **One worktree, one branch, no hard-linked `.lake`.** Reuse the existing lane worktree; do not
   create another.
2. **Shared files are integration-owner territory.** `ChunkValidationD2.lean`, `D3/FunctionCall.lean`,
   `Wasm/Exec.lean`, `Wasm/Host.lean`, `D2/Types.lean`, root `NearSpecV3.lean`, v3 `lakefile.toml`,
   claim/witness schemas. Lane agents submit adapter patches; they do not edit these directly unless
   W00 assigned the file to them.
3. **Preserve the signed statement.** `checkD2Core`/`checkD3`/`gAlpha` and the oracle pins are
   immutable; `make pin-check` must pass. Broader behaviour goes in a successor.
4. **Acceptance contract per package** (workplan §"Acceptance contract"): executable reachability
   through the successor checker; pinned nearcore correspondence with hashes and commands; directed
   coverage plus a controlled-breakage control; ≥1,000 generated comparisons per family across ≥4
   seeds; chunk observables; axiom closure limited to `propext`, `Classical.choice`, `Quot.sound` with
   no `sorryAx`; handoff committed with tip, premises, failures and next step.
5. **No overclaiming.** Measured ≠ proved; sampled ≠ full replay; "merged" ≠ validated. An exclusion
   may not disappear by relabelling. A timeout or crash is a failure, not an exclusion.
6. **Report honestly on failure.** If a proof does not close, say so with the measurement; do not
   land a stub or an assumption dressed as a result.

## 5. Dependency detail for the risky packages

### W02 (L1) — the package that can invalidate the approach
`ChallengeChunkV3Gas.lean` already has the successor relation and the band example. The open risk is
**evaluator totality at 1 Pgas**: raising the cap 290× makes executions reachable that never ran. If
the fuel formula in `D3/FunctionCall.lean` cannot cover valid metered execution, the widening is
wrong rather than merely unproven. This should be examined early even though its *acceptance* waits on
W00. Also: the monotonicity theorem over `checkD2Core` resisted naive unfolding when I probed it (the
`do`-block will not `simp`); a `check`-level monotonicity lemma or a factored checker is the likely
route.

### W03 (Wasm owner + L7) — measured discrepancy, needs a design decision
UQ-014: a prepared module with 66,000 globals executes in Lean but fails pinned Wasmtime's pooling
instance-size restriction; nearcore turns `LoadingError` into a zero-gas failed function call, not a
chunk rejection. The workplan explicitly warns against equating the observed global-count threshold
with a general formula — other instance-layout components must be accounted for. Needs the pinned
layout predicate, not a magic number.

### W05/W06 (L3) — split arithmetic from integration
13 missing curve hosts (3 BN128 + 9 BLS + 1 wasm-exec row) plus 2 partial. The workplan separates
W05 (curve hosts) from W06 (transaction/delegate keys) and notes W06 may reuse W05's secp arithmetic
but does not depend on BN128/BLS. Two substreams, separate owners, shared codec owner per curve.

### W09/W11 (L5/L6) — the shared trie-accounting interface
W09 replaces the conservative `baseBytes + 2000 * removals ≤ 4,000,000` guard with a real recorder;
W11 needs retention for left/right children, child-shard congestion, buffers. They share the recorder
interface and must agree in W00. W11 also must settle mixed-protocol segment reachability (UQ-009).

### W13 (L7) — acquisition can start now
Witness capture/provenance tooling does not need W12; only final execution does. The workplan requires
**≥1,000 consecutive blocks across all shards** with complete provenance — metadata-only rows do not
count. This is likely the longest-lead item after curve arithmetic.

### W10 (L6) — narrow and well-specified
Preserve the `checkD2CoreG` delegation; prove the non-genesis overlap (including the shared prefix
before delegation — currently argued, not proved); add `txValid.all` coverage, which no recorded
genesis case exercises. This is the most tractable proof obligation in the set.

## 6. What I would not parallelize yet

* **W07/W08** — L4 is mid-flight on the successor hook and its branch is 15 commits behind main. A
  second agent on `D3/GlobalContract*` would conflict. Wait for L4's integration, then rebase.
* **W12** — it consumes accepted increments. Starting it now would mean guessing W00's API.
* **W16** — release work with no frozen relation is documentation only.
* **RIPEMD/Keccak `round_agrees`** (the PQ track's hashes/receipts gap) is *not* in this workplan's
  W-list; it belongs to the PQ proof track. Do not assign it to a Lean-chunk agent.

## 7. First three prompts to issue

Short, in dependency order. Each names its package, worktree, forbidden files and acceptance contract.

1. **W00** — "Publish the successor API in `spec/lean/v3/NearSpecV3/`: signatures for the canonical
   checker + tiers, host dispatch, actions/receipts, contract resolution, trie recorder, boundary
   facts and differential result. Make it compile with the existing float/gas/genesis adapters. Do
   not extend `checkD3`. Deliver the owner map for the 28 missing/partial rows and 17 UQs. Worktree
   `lean-chunk-L0`."
2. **W01** — "Fix the `difftest-gates` CI job so it does not require `/data/…/corpora` (it is red on
   hosted runners today: `corpus_manifest.py` hardcodes the corpora path and exits 1). Then make
   `difftest_d3.py`'s 1,259 never-compared out-of-domain verdicts explicit, each with an asserted
   reason/classification — L7's §4.4b accounting reproduces exactly, so use it as the denominator
   and do not relax comparisons to make counts agree. Worktree `lean-chunk-L7`."
3. **W15** — "Audit the existing signed D3α admission reports for the exact restricted reference:
   hashes, formal checks, artifact binding, kernel rechecks, conformance/adversarial/resource gates,
   and whether a signed live ADMITTED-at-formal-tier report exists. Report what is absent rather than
   assuming deployment equals admission. Worktree `lean-chunk-L8`."

Then, once W00's interfaces compile: W02 (L1), W03+W04 (L2), W06+W05-secp (L3), W09 (L5), W10 (L6),
W13-capture (L7). W11 after W00's trie interface and UQ-009. W05-BN128/BLS and W07/W08 as capacity and
L4's branch allow.

## 8. Open decisions for the user

1. **CI corpora**: provision content-addressed corpora for hosted runners (costs storage/bandwidth) or
   split the job into a lightweight schema test plus a corpus-gated check? I recommend the split —
   it makes the red check green immediately and keeps the real content check honest and distinct.
2. **Agent count**: 3 first (W00/W01/W15) then 4–5? Or start wider despite the disk margin?
3. **L4 sequencing**: wait for its current 3 commits to be rebased and integrated before dispatching
   W07/W08, or dispatch W07 on a separate branch and reconcile later? I recommend waiting — W07 is the
   single largest row cluster (95 L4 rows) and duplicating dispatch logic is the exact failure the
   workplan warns about.
