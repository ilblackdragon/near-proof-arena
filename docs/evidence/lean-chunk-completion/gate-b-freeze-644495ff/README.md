# Gate-B freeze replay on checker `644495ff…` (2026-11-03)

The frozen package is main at `ca08fdf37`. The checker is `nearspec-v3-check-successor`, sha256
`644495ff5e04801f6ba206abb5d3f608bcfe0f10499767a8203464d4b10a9ae3`. That build includes:
- the G3 per-call race fix;
- the removed fuel guard;
- the gas-key method-name UTF-8 fix;
- the item-6 (UQ-010) signed hand-over.

Each case ran cold through `tools/d3/replay_successor.py` (`run.sh` here). The comparison was
against pinned nearcore 2.13.4 via `oracle/v3-d3/tools/difftest_d3.py compare` and the independent
domain classifier `oracle/tools/independent_domain.py`. This is the harness reconciled in
[gate-b-freeze-rescore](../gate-b-freeze-rescore/README.md). No rescoring was needed: every run
passed as executed.

The runs are in `/data/illia/nearproof-deps/gateb-freeze-ca08fdf37/`. `summary.json` here records
the following, each with its sha256:
- the partitions;
- every report and result file;
- the four input case lists.

## Result: 0 disagreements on every run

| run | cases | accept | reject | out of domain | status |
|---|---|---|---|---|---|
| fixtures-final, allFeatures | 1,364 | 827 | 533 | 4 | pass |
| fixtures-final, signed | 1,364 | 434 | 421 | 509 | pass (200 accepts above G_α, all nearcore-valid) |
| gap census, allFeatures | 3,138 | 3,138 | 0 | 0 | pass |
| gap census, signed | 3,138 | 735 | 0 | 2,403 | pass (all exclusions oracle-asserted) |
| full corpus, allFeatures | 235,716 | 76,431 | 159,191 | 94 | pass |
| full corpus, signed | 235,716 | 73,783 | 159,175 | 2,758 | pass (2,513 oracle-asserted, 245 independently asserted) |
| mainnet shard 13, allFeatures | 1,223 | 1,223 | 0 | 0 | raw checker output, all valid mainnet chunks accepted |
| mainnet shard 13, signed | 1,223 | 944 | 0 | 279 | all 279 `e.wasm-α` (float in a function body) |

Compared with the pre-freeze replay (checker `197e28fe…`), the full corpus on `allFeatures`
changed in two ways:
- **One more reject, one fewer out of domain** (94 out of domain, down from 95). This is the G3
  per-call race fix: the case is now decided, and nearcore also rejects it.
- **No new exclusions.** The independent classifier asserts every signed-tier exclusion the
  oracle does not.

## What this closes, and what it does not

- **Closed: Gate B's replay half** (workplan item 13) for everything this host can run.
- **Still needs the sponsor machine:** W13 (the 1,000-block all-shard mainnet capture).
- **Not part of Gate B:** Gates A and C need signed admissions by the owner.
- **The v3.1 draft** (`challenges/drafts/near-chunk-v3-1.draft.json`) has had its
  `formal_spec.tree_digest` regenerated against the frozen tree `ca08fdf37`:
  `sha256:9923436b975d011d4def3d8332d8ede2e6f598c2f36db6c390afd73834924ab9`.
  - It was regenerated against `ca08fdf37`, not HEAD, because HEAD adds only the research E2E
    modules (`spec/lean/v3/NearSpecV3/E2E/`, plus one `defaultTargets` line). Those keep changing
    and do not affect the checker.
  - The draft is unsigned and unpublished.
