# L0 — boundary and coverage inventory

Owner: L0 lane. Worktree `/data/illia/nearproof-wt/lean-chunk-L0`, branch `lane/lean-chunk-L0`,
base commit `34e5cddf4` (main after the plan landed). Status: **partial** — the inventory tool and
artifact exist; the boundary questions §4 L0 also owns are not settled.

## What landed

| artifact | purpose |
|---|---|
| `tools/d3/lean_chunk_coverage.py` | fail-closed generator; reconciles pinned nearcore git objects against Lean dispatch tables |
| `docs/research/lean-chunk-coverage.json` | the inventory, 114 rows |
| `docs/research/lean-chunk-coverage.md` | readable summary and the honest limits |

`--check` returns 1 on drift. Regenerate with `--output` only after reviewing the diff.

## Inventory shape

114 rows: 91 `implemented`, 20 `missing`, 3 `impossible-at-boundary`.

| family | implemented | missing | impossible |
|---|---|---|---|
| action | 12 | 3 | 0 |
| host | 75 | 14 | 3 |
| instruction | 1 | 1 | 0 |
| domain_guard | 3 | 1 | 0 |
| boundary | 0 | 1 | 0 |

The 20 missing rows are concentrated in exactly three places: **L2 floats** (2), **L3 curve hosts**
(14), **L4 action decoder** (3), plus **L6 resharding** (1). That concentration is the useful output —
it says the semantic gap is not diffuse across the validator.

## Extractor trust

The host-import extractor reproduces all 92 `env` imports from `imports.rs` with **zero set
difference** against the pre-existing `near-wasm-boundary-inventory.json`. Two independent parsers
agreeing on the row set is why the row set is trustworthy; it says nothing about behaviour.

Three parser bugs were found and fixed while building this, each of which had produced a wrong row:

1. **Delegate actions mislabelled as missing.** Tags 8/14 decode through `pAct`, not `pBase`. Reading
   only `pBase` marked both as out-of-domain. Fixed by checking the `pAct` delegate branch.
2. **Out-of-domain tags counted as decoded.** Tags 9/10/11 match `| 9 =>` in `pBase` and also
   `=> throw oodX`; a naive scan counted them as implemented. Fixed by excluding throwing tags.
3. **16 `promise_*` imports silently dropped.** Those entries span lines (name, then `<[`, args,
   `>,`), so a per-line parser saw the name without `<[` and skipped them. That made the import count
   read 76 instead of 92 and invented a phantom "missing" host (`gas_seen_from_wasm`, which is really
   the `@as gas:` alias and is implemented). Fixed by splitting on the terminating `>,`.

A fourth subtlety: `gas_seen_from_wasm` is `@as gas:` in the source. The Wasm-visible import name is
`gas`, and Lean implements `gas`. Using the Rust function name would have created a false gap.

## What this does NOT establish

* No execution, differential testing or proof. `implemented` means "a dispatch arm exists".
* The 134-opcode count is syntactic, not semantic-branch coverage.
* Domain guards are recorded as present, not re-derived as complete.
* Genesis, chain-segment, scheduler and cache assumptions are **not** settled. Plan §4 L0 owns those,
  and Gate B cannot pass with one unresolved. This is why the lane is `partial`, not `complete`.

## Next executable step

Settle the boundary questions against `docs/research/chunk-validation-boundary.md`: genesis
(`sharding.rs:491-494`), segment/layout restrictions, scheduler assumptions (bandwidth scheduler RNG
seeding from `prev_block_hash`), cache dependence and claim facts. Each unresolved item must be mapped
to a lane or a newly named lane. That work is reading and judgement, not code.

## Files safe for the next agent to edit

`tools/d3/lean_chunk_coverage.py`, `docs/research/lean-chunk-coverage.{json,md}`, this log. Nothing
shared with L1–L8 is touched by this lane.
