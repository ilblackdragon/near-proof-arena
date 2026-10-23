# Lean chunk-transition coverage inventory (L0)

Readable summary of [`lean-chunk-coverage.json`](lean-chunk-coverage.json), the L0 deliverable in
[`../requirements/LEAN_CHUNK_TRANSITION_PLAN.md`](../requirements/LEAN_CHUNK_TRANSITION_PLAN.md) §4.

**What this is.** A static reconciliation of the *pinned* nearcore surface against the Lean
specification's actual dispatch tables. It is **not** execution evidence, a differential test or a
proof. A row marked `implemented` means "the Lean spec has a dispatch arm for this name"; it does not
mean the behaviour was tested against nearcore.

Regenerate or verify with:

```
python3 tools/d3/lean_chunk_coverage.py --repo . \
    --nearcore <pinned-nearcore> --check docs/research/lean-chunk-coverage.json
```

Exit status 1 means the inventory drifted from source. Review the diff before regenerating.

## Pins and provenance

| | |
|---|---|
| nearcore commit | `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4) |
| protocol version | 86 |
| source extraction | git objects only, never a dirty checkout |
| Lean side | `spec/lean/v3/NearSpecV3`, hash of each file in `source_sha256` |

The host-import extractor was cross-validated against the pre-existing
[`near-wasm-boundary-inventory.json`](near-wasm-boundary-inventory.json): both independently yield
the same 92 `env` imports with no set difference. That agreement is the reason to trust the row set;
it is not evidence about behaviour.

## Headline numbers

| | count |
|---|---|
| inventory rows | 114 |
| implemented | 91 |
| missing | 20 |
| impossible-at-boundary | 3 |
| nearcore `env` imports | 92 |
| Lean host dispatch arms | 75 |
| nearcore action tags | 15 |
| Lean-decoded action tags | 10 (+3 delegate via `pAct`) |
| Lean numeric opcode bytes | 134 |

## By family

| family | implemented | missing | impossible-at-boundary |
|---|---|---|---|
| action | 12 | 3 | 0 |
| host | 75 | 14 | 3 |
| instruction | 1 | 1 | 0 |
| domain_guard | 3 | 1 | 0 |
| boundary | 0 | 1 | 0 |

## The 20 missing rows, by owner

### L2 — floating point (2 rows)

* `L0-instr-float` — every f32/f64 opcode. The decoder parses them only to reject them; `Exec.lean`
  returns `.unmodeled "float (out of domain)"`. **This is L2's entire deliverable**, and it is the
  largest single semantic gap in the inventory.
* `L0-guard-floatOutOfDomain` — the guard that performs the exclusion. It closes only when L2 lands
  real semantics; the guard's own row cannot be "fixed" without that.

### L3 — curve hosts (14 rows)

All 14 are production-enabled at PV86 (verified in `parameters`: `p256_verify_host_fn = true`,
`wasm_alt_bn128_g1_multiexp_base = 71300`, and so on), so they are reachable and cannot be dismissed
as boundary exclusions. The Lean spec reports them out-of-domain via `curveHosts` and has no curve
arithmetic at all:

`alt_bn128_{g1_multiexp,g1_sum,pairing_check}`, `bls12381_{g1_multiexp,g2_multiexp,map_fp_to_g1,map_fp2_to_g2,p1_decompress,p2_decompress,p1_sum,p2_sum,pairing_check}`, `ecrecover`, `p256_verify`.

Note this is *dispatch* absence, not a stub returning a fixed value: there is no Lean field to fill
in. L3's acceptance bar (positive/negative vectors, noncanonical scalars, subgroup/infinity cases,
exact host gas) needs real field arithmetic for each curve family.

### L4 — actions and one host (4 rows)

* `L0-action-09/10/11` — global-contract deploy, global-contract use, deterministic state init. The
  *host* functions for these exist and are implemented (`Host.lean`); the **action decoder** rejects
  the tags as out-of-domain. So L4 here is codec plus execution wiring, not new host semantics.
* `L0-host-*` — none remaining; all 75 non-curve hosts have arms.

### L6 — resharding (1 row)

`L0-resharding` — `DomainD3.noResharding` excludes every layout change and split gate. L6 owns
removal, and needs validator fixtures crossing a real layout boundary.

### Not real gaps (3 rows)

`sandbox_debug_log`, `sleep_nanos`, `burn_gas` are gated by `sandbox` / `test_features` and are not
importable in production features, so they are `impossible-at-boundary`, not missing. Merging them
would be wrong: a production chunk cannot reach them.

## What this inventory does NOT establish

* It does not show that an `implemented` row behaves like nearcore. That needs the directed and
  generated comparisons in plan §5.
* The opcode count (134) is *syntactic*: it counts bytes the decoder accepts, not instruction
  families or semantic branches. L2's real coverage question is per-opcode behaviour.
* Domain guards are recorded as present, not re-derived as complete. Whether a guard rejects exactly
  the excluded set and nothing else is a separate obligation (`L0-guard-*` rows).
* Genesis, chain-segment and scheduler assumptions are **not** settled here. The plan's Gate B
  requires them; this inventory only records the guards that exist today.

## Next step for L0

Settle the boundary questions this inventory leaves open: genesis, segment/layout restrictions,
scheduler assumptions, cache dependence and claim facts. Every unresolved item must map to a lane or
to a newly named lane. Gate B cannot pass with one unresolved — see the plan's §6 ordering, where L0
completes before L1's successor API is frozen.
