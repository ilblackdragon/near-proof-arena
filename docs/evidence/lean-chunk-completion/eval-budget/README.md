# W02/W16 evaluator speed, memory and the per-chunk budget (workplan item 2)

Target: nearcore 2.13.4 (`44f7ae6c`), PV86, `nearspec-v3-check-successor --tier allFeatures` (and
`signed` for verdict identity). Worktree base `4f07a7fdf`. Three compiled-code changes, no
definition of any relation changes:

| change | commit | what |
|---|---|---|
| zstd byte reads | `ce80c592a` | `getB` + `@[csimp] getB_eq` (`Successor/Zstd.lean`) |
| label memo | `7cc36bfdb` | `runMemo`, `runMemo_eq_runFast` (`Wasm/Arcs.lean`) |
| fast SHA-256 in scope | `29308d20d` | `import ArenaCore.SHA256Fast` in the four NearSpecV3 roots that reach `NearSpec`/`ArenaCore` hashing |

Checkers: **before** `a1627ea3…` (base), **after** `584976cf…` (all three). `check-mid`
(`65d28207…`) is zstd + SHA without the memo, used only to attribute the witness-path gain.
Wall times are on a shared 32-core host (load average 30–170 during the runs, recorded per case
in the JSON files); CPU seconds (user + sys) are given next to them and are the better measure.

## 1. What was slow, and why

* **zstd (~90–145 s per MB).** Every byte read went through `data.data.getD i 0`. In compiled code
  `ByteArray.data` converts the whole byte array to a boxed `Array UInt8`, so each read cost
  O(input size) — the decoder was quadratic, not "slow per symbol". The poor-man's profiler
  (gdb samples) showed `lean_byte_array_data` + `lean_dec_ref_cold` under every hot frame.
  `getB` is defined by the same expression; `getB_eq : @getB = @getBFast` (kernel-checked, allowed
  axioms) lets compiled code read `data[i]` directly. Definitions seen by the kernel are unchanged.
* **Label-keeping loops (~3–5 h per 300 Tgas).** `St` keeps labels as `List Label`. An arc that
  keeps the labels it pushes (push-then-pop across a charged group) had to materialize them, and an
  unfused branch (`br_if`/`br_table` back-edge) ran `doBr`, which walks the list three times
  (`length`, `[l]?`, `drop`). Both are O(label depth) = O(5,000) per iteration.
  `runMemo` keeps, per pc, the label work of the last execution (the arc's result, or `doBr`'s target
  and remaining labels) keyed by the input label list, the stack height (arcs) or branch depth.
  A hit requires the input labels to *equal* the cached ones; `labsEq` decides that with a
  pointer-equality shortcut at every cell (`withPtrEq`, whose contract is that the shortcut may only
  answer `true` where the full comparison would), so a loop that comes back to the same list object
  hits in O(1). `doBr`'s label work is also O(`l`) now (`lenGe` instead of `length`). The memo is a
  256-slot direct-mapped array (bounded retention); label work under 16 cells is recomputed.
  Proved: `runMemo_eq_runFast` (for every fuel and state, given `MemoOK`), `memoOK_empty`; the four
  `@[csimp]` lemmas (`callEntry`, `runCall`, `runCallWithLimits`, `outcome`) are re-proved through
  it. `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`.
* **SHA-256 on the witness path.** `ArenaCore.SHA256Fast` (`@[csimp] sha256_eq_sha256Fast`) existed
  but was not imported by the NearSpecV3 modules that hash (`merklizeBorsh`, `mkHStore`, …), so
  they ran the `Nat`/bignum spec SHA (profile: `lean_cstr_to_nat`, `__gmpz_*` under
  `SHA256_round`). It is now imported in `Wire`, `TrieBuild`, `Wasm/Crypto`, `Logged/Store` (every
  NearSpecV3 module that can see a hash imports one of them). Pinned `NearSpec` files are untouched;
  hashing compiled inside `NearSpec` itself still uses the spec SHA.

## 2. Deliberate-breakage control (label memo)

`research/lean-arcs/ArcProbeBroken.lean` copies `runMemo` with one change: a branch-memo hit no
longer checks `labsEq L inp`. `gen_wasm.py` writes `memoctl.wasm`, where the same `br 20` runs in
two calls of one function at value-stack heights 0 and 2 (same pc, labels differing only in their
heights). At 300 Tgas:

```
committed: ok burnt=29619216
broken:    abort WasmTrap(Unreachable) burnt=30441972
```

The committed path (`callEntry`, compiled to the memo through `@[csimp]`) agrees with
`outcome` (`arcprobe`: `ok 207762824 …`, the same contract result); the broken copy reuses the
first call's labels, truncates the value stack and traps. (A broken memo also makes
`runMemo_eq_runFast` unprovable: `MemoOK` fails for the stale entry.)

## 3. Loop fixtures (pinned nearcore, `eval-loops` scenario)

`NEAR_SUCCESSOR_SCENARIO=eval-loops gen --domain d3 --seed 2028 --chains 1 --blocks 36 --p-missing 0
--mutate-every 0 --code-mutant-p 0 --ood-cap 100000`: 144 honest chunks, all `cold_ok`;
`manifest-el2028.json` (via `collect_fuel_stress.py`, 0 problems; nearcore reports every call as
out of gas). `eval-loops/cases.tar.gz` holds the 10 cases that apply the calls. Contract `evalc2`
(`scenarios::eval2_wat`).

| call | nearcore | before (3 Tgas) | after (3 Tgas) | after (**300 Tgas**) |
|---|---|---|---|---|
| `pushpop4999` (push 4,999 labels, charged group, pop) | out of gas | accept, 142 s CPU | accept, 0.72 s | **accept, 43 s CPU**, 79 MiB |
| `brif4999` (`br_if` back-edge over 4,999 labels) | out of gas | accept, 196 s | accept, 0.90 s | **accept, 63 s**, 78 MiB |
| `brtable4999` (`br_table` back-edge) | out of gas | accept, 179 s | accept, 0.85 s | **accept, 56 s**, 79 MiB |
| `deepbrif4998` (shallow `br_if` under 4,998 blocks) | out of gas | accept, 7.8 s | accept, 0.75 s | **accept, 48 s**, 78 MiB |
| `brtablealt4997` (`br_table` alternating two depths) | out of gas | accept, 82 s | accept, 0.78 s | **accept, 44 s**, 78 MiB |

"Before" at 300 Tgas scales linearly from the 3 Tgas column (×100): 4–5.5 h for the first three
shapes (the previous workplan figure, 3–4 h, was measured on an idle host). After: under 65 s CPU
each. Probe (`arcprobe`, same modules as the eval-time README): `pushpop4999` 0.3 Tgas 14,759 ms →
67 ms, `brif4999` 17,079 → 103 ms; at 300 Tgas 62 s / 77 s wall. Loops without label work are
unchanged within noise (300 Tgas: `b4999` 50.9 s, `spin` 30.7 s, `nops` 10.5 s, `mixed` 2.9 s,
against 40.4 / 28.8 / 7.7 / 2.6 s in the eval-time README on a less loaded host).

## 4. zstd

| input | before | after |
|---|---|---|
| real 0.87 MB `state_witness` (zstd-1, 4 workers) | 261.6 s (128 s on an idler host) | **0.03 s** |
| 1 MB of concatenated real witnesses | 90.5 s | 0.03–0.06 s |
| 8 MB of real witnesses (3.2 MB encoded) | — | 0.22 s, 34 MiB |
| 64 MiB of real witnesses (26.7 MB encoded) | (≈ 1.6 h projected) | **2.1 s, 235 MiB** |
| 48 MiB padded compressed witness (whole chunk, §5) | 650–990 s | **2.1 s** |

The size-limits batteries rerun on the new decoder (`zstd/`): 720/720 roundtrips, 3,600/3,600 real
witness encodings, 19/20 synthetic (the same Lean-stricter corrupt frame as before), 13/13
breakage controls detected, the four boundary frames unchanged.

## 5. The per-chunk budget

**Budget (this host, one checker process, `allFeatures`): ≤ 15 min CPU and ≤ 16 GB resident per
chunk.** Every worst-case fixture below meets it with a wide margin; the largest measured values
are 105 s CPU (64 MiB of cold-fetched code) and 2.2 GB (same case).

| fixture (pinned nearcore, whole chunk) | nearcore | Lean after | CPU s | max RSS |
|---|---|---|---|---|
| `code-response` at 64 MiB: 17 contracts, 67,108,864 B of cold-fetched code (`../size-limit-fixtures`) | accept | accept | 100.5 | 2,245 MiB |
| `code-response` 1 B over 64 MiB | (cache-dependent) | out of domain `w.code_response_size` | 1.8 | 2,179 MiB |
| 48 MiB − 1 / 48 MiB / 48 MiB + 1 padded compressed witness (`../size-limit-fixtures`) | accept / accept / reject | same | 2.2 / 2.1 / 1.0 | 1.9–2.0 GB |
| gate-b `wsize.above`: 9.46 MB witness (large transactions) | accept | accept | 43.7 | 981 MiB |
| gate-b `gas.above`: 1.8 Pgas in one chunk (2 × 900 Tgas `memory.fill`) | accept | accept | 61.4 | 131 MiB |
| eval-loops 300 Tgas (5 shapes, §3) | accept | accept | 43–63 | 79 MiB |
| eval-time 300 Tgas (`blocks4999`, `deep4999`, `midrun4998`) | accept | accept | 46–73 | 77 MiB |
| fuel-termination 300 Tgas (14 cases: `spin`, `nops`, three `nops` in one chunk, `count`, `memmax`, …) | accept | accept | 0.1–33 | ≤ 394 MiB |

Composition. A chunk carries at most 1 Pgas of function-call gas (the gate-b 1.8 Pgas fixture
exceeds the real chunk limit and still takes 61 s). The slowest measured gas is the `br_if`
back-edge at 63 s CPU per 300 Tgas, so 1 Pgas of the worst measured shape is ≈ 3.5 min. The
witness side scales with bytes: ≈ 4.6 s CPU and ≈ 104 B resident per byte of transaction-heavy
witness (gate-b 6.7 MB → 641 MiB, 9.46 MB → 981 MiB); a 64 MiB decoded witness projects to
≈ 5 min and ≈ 7 GB. 64 MiB of cold-fetched code adds ≈ 100 s and ≈ 2.2 GB (measured). The
projected worst chunk (64 MiB witness + 64 MiB code + 1 Pgas of the slowest loop) is therefore
≈ 10 min and ≈ 9–10 GB, inside the budget; the host (125 GB, `zkbuild.slice` capped at 48 GB)
runs four such checks concurrently.

What is measured and what is projected: every row of the table is measured on this host. The
64 MiB-decoded-witness line is a linear projection from the 6.7 / 9.46 MB fixtures: nearcore's
producer limits keep generated witnesses far below 48 MiB encoded (see
`../size-limit-fixtures/README.md` §2), and the 48 MiB fixtures reach the cap with a skippable
frame, so their decoded witness is small.

## 6. Memory (~106 B per witness byte): not reduced

Measured after: 641 MiB at 6.7 MB and 981 MiB at 9.46 MB, i.e. ≈ 104 B per witness byte —
unchanged (before: 642 / 982 MiB). The cost is structural: `Bytes` is `List UInt8` (24 B per byte
per live copy) and the borsh parsers copy sub-lists (`takeT`), so a witness is held two to four
times over, plus the Reed–Solomon parts of the chunk encoding. Reducing it needs either a byte
representation change in the spec or proved `@[csimp]` array-based parsers for the witness path;
neither is in this change. The budget above holds with the current representation.

## 7. Verdict identity (before → after)

`tools/d3/verdict_identity.py`, checker `a1627ea3…` → `584976cf…`, verdict **and** reason compared
per case (`verdict-identity.json`):

| population | tier | cases | identical verdict and reason | verdicts (both) | wall before → after (2 workers) |
|---|---|---|---|---|---|
| every committed fixture case (931 dirs under `lean-chunk-completion/`, tarballs extracted) | signed | 931 | **931** | 179 A / 298 R / 454 O | 732 → 733 s |
| same | allFeatures | 931 | **931** | 574 A / 357 R | 969 → 921 s |
| gap census (`d3c7`–`d3c10`, `nearcore == ok ∧ ¬expected_rel_d3`) | signed | 3,138 | **3,138** | 735 A / 2,403 O | 1,309 → 1,333 s |
| same | allFeatures | 3,138 | **3,138** | 3,138 A | 1,836 → 2,110 s |
| corpus, deterministic 1-in-8 sample of d1run, d2corpus.v2, d3c7–d3c10 | allFeatures | 29,465 | **29,465** | 9,585 A / 19,870 R / 10 O | 3,287 → 2,287 s |

No verdict and no reason moved; no errors or timeouts. The corpus was sampled (every 8th case of the
sorted list) because the shared host was capped at four checker processes; the full 235,716-case
corpus is left to the integrator's run. Wall times are dominated by load, not by the change.

Blind replay (`tools/mainnet-replay/blind_corpus.py`, `blind-report.json`): the 10 eval-loops cases
and the 64 MiB code-response chunk, 11/11 `match` (every header output computed from the
witness equals nearcore's).

## Reproduce

```
cd spec/lean/v3 && lake build nearspec-v3-check-successor nearspec-v3-zstd-decode
cd research/lean-arcs && lake build arcprobe arcprobe-broken && python3 gen_wasm.py MODS
arcprobe-broken --run 300000000000000 MODS/memoctl.wasm
NEAR_SUCCESSOR_SCENARIO=eval-loops $GEN gen --domain d3 --seed 2028 --chains 1 --blocks 36 \
  --p-missing 0 --mutate-every 0 --code-mutant-p 0 --ood-cap 100000 --out RUN
python3 tools/d3/collect_fuel_stress.py --source RUN --out manifest.json
python3 tools/d3/time_cases.py --checker CHECKER --cases-file LIST --out OUT.json
python3 tools/d3/verdict_identity.py run --checker CHECKER --tier allFeatures --cases-file LIST --out RES.jsonl --jobs 2
python3 tools/d3/verdict_identity.py diff BEFORE.jsonl AFTER.jsonl
ZSTD_LEAN=... ZSTD_ZREF=... ZSTD_WORK=... python3 docs/evidence/lean-chunk-completion/size-limits/difftest_real.py
```
