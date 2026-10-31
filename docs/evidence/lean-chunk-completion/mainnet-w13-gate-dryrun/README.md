# W13 gate dry run: cold adapter + blind replay on the shard-13 pilot (2026-10-28)

This is `make w13-gate` end to end, on everything except the all-shard capture. The window is the
1,223 heights of the shard-13 pilot (221489407–221490629). The block denominator covers all ten
shards. Only shard 13 has witnesses, so this run **fails**, as it must.

## Result (`summary.json`)

```
W13 FAIL: mismatch=0.0000%; coverage=9.9836%; verified=9.9836%; compared=1221/12230;
          {'missing_witness': 11007, 'match': 1221, 'error': 2}
```

| | value |
|---|---|
| Captured blocks | 1,223 / 1,223 (100%), consecutive; 0 acquisition errors; 0 missed chunk slots |
| Expected new chunks | 12,230 (10 shards × 1,223) |
| Compared | 1,221 |
| Match | 1,221 (shard 13). Each one passed all of the below. |
| Mismatch (verdict / output / blind leak) | 0 / 0 / 0. Mismatch % = 0.0 over 1,221 comparisons. |
| Unsupported | 0 |
| Native reject | 0 |
| Missing witness | 11,007: shards 1, 4, 6, 7, 8, 9, 10, 11, 12 × 1,223 |
| Errors | 2: h221490628-s13 and h221490629-s13. Both are above the pilot store's final head (221490627), so the adapter refuses to admit them (`final: false`); their claims did match. |
| Replay coverage / verified match | 9.9836% / 9.9836% |

Each match means all of the following held:

- the claim is anchored to the archive (chunk hash, epoch, every segment block hash);
- the cold adapter accepted, with `facts_verified` (claim recomputed from the store, byte-equal),
  a canonical **final** including block whose hash equals the archive's, and an empty compiled
  cache at start;
- Lean `--blind` accepted, and its 11 outputs equal the endorsed header;
- the blinded-input control did not accept.

Cold execution was real: 279 of the 1,221 cases compiled contracts into the fresh cache
(`entries_after > 0`). Those 279 are exactly the cases that carry code. Native validation took a
median of 0.0012 s and at most 0.22 s per chunk; the store open dominates each ~2 s adapter call.

## Deliberate-breakage controls on the adapter (`cold-controls.json`)

372 cases: all 279 code-carrying cases plus every 10th case. 0 unexpected outcomes.

| control | outcome |
|---|---|
| honest | accept 372 |
| `no_code` (contract code stripped from `witness.bin`) | **reject 279/279**. The warm diagnostic (`replay-export`, node cache) accepted all of them, so the adapter does not use a warm cache. |
| `claim_epoch` (one byte of T1 flipped) | facts rejected 372 |
| `claim_tail` (T14 tag flipped) | facts rejected 372 |
| `post_root` (main post state root zeroed) | reject 372 |

## Inputs and identities

- Archive: `jsonrpc+https://archival-rpc.mainnet.fastnear.com`. Capture `manifest.json` sha256
  `bdc5b6fb…7488a`. NEAR Data rate-limited this box (HTTP 429, `Retry-After: 0`) after 13 blocks.
- Cases: the pilot's `replay-cases/` (exported by `replay-export` from the pilot store), attached
  read-only with `gate.py attach-all`: 1,223 attached, 0 failed.
- Adapter: `neard … view-state state-witness cold-validate`, sha256 `6a1a967d…5bd00`. Built from a
  clean copy of `44f7ae6c` + `export.patch` + `native/replay-export.patch` + `native/w13_*.rs`
  (Rust 1.93.0, `json_rpc,shadow_chunk_validation`).
- Adapter store: a hard-link view of the stopped pilot node's database. The SST files are
  hard-linked; manifest, WAL and options are copied; `contract.cache` and `state_snapshot` are
  left out. The pilot directory itself was never opened by RocksDB.
- Lean: `nearspec-v3-check-successor --tier allFeatures`, sha256 `a1627ea3…45475`.
- Harness: `gate.py` `902e954c…8b45e`, `blind_inputs.py` `8464ecd8…c590`.
- Run inside `systemd-run --user --scope -p MemoryMax=16G`, `W13_JOBS=8`, about 15 minutes. A first
  attempt inside the shared session cgroup, which was memory-throttled by other jobs, timed out on
  every adapter call (600 s). Those timeouts were reported as errors, never as matches.

`shard13-results.jsonl` lists one line per shard-13 slot: status, native verdict, facts, finality,
cold-cache use, blind verdict, control verdict and output diffs.

## What this does not show

- Any shard other than 13, and any busy shard. That needs the all-shard capture
  ([runbook](../../../../tools/mainnet-replay/ALL_SHARDS_RUNBOOK.md)).
- Independent finality. The including block's finality is the pilot node's doomslug view, matched
  against the archive hash. There is no light-client proof.
- An independent check of `build_claim`. The adapter reuses the oracle's claim builder; byte
  equality proves the supplied claim is what that builder produces from the node store.
