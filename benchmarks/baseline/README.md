# Baseline measurement (reference candidate)

How a challenge's `workload_suite.baseline_submission` / `baseline_ns` are
produced (docs/BENCHMARK_SPEC.md §6.2, §8, §11; docs/PROTOCOL_UPGRADES.md §6).

```sh
cargo build -j 8 -p arena-cli -p arena-admin
(cd oracle && ./scripts/link-nearcore.sh && cargo build -j 8)
python3 benchmarks/baseline/run_baseline.py \
  --challenge challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json \
  --package examples/reexec-witness \
  --oracle oracle/target/debug/near-arena-oracle \
  --out benchmarks/results/<session-name> --cpus 8-15
python3 benchmarks/baseline/pin_baseline.py \
  --old challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json \
  --summary benchmarks/results/<session-name>/summary.json \
  --name near-transfer-receipt-v1.1 --created-at <RFC 3339, later than the old one> \
  --out challenges/drafts/near-transfer-receipt-v1.1.draft.json
target/debug/arena-admin supersede --old challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json \
  --draft challenges/drafts/near-transfer-receipt-v1.1.draft.json \
  --key /data/illia/nearproof-deps/keys/governance-local.key --pubkey challenges/governance-local.pub
```

`run_baseline.py`:

1. packs the **committed** package (`git archive HEAD`) with `arena pack`
   (package digest = sha256 of the deterministic archive) and builds it with its
   own `build-recipe/build.sh` in a fresh `HOME`;
2. collects the host profile (`arena_bench host-profile`, non-governed);
3. draws a fresh 32-byte sampling secret, records its commitment **and reveals
   it** (a baseline is public: anyone can regenerate the inputs) and derives the
   per-class seeds of §11.1 (`<class>` and `<class>#fresh`);
4. checks each generator spec's JCS digest against the challenge's
   `workload_suite.classes[].generator`, then generates every batch with the
   pinned oracle (`near-arena-oracle gen --challenge …`, which itself refuses a
   challenge of another nearcore commit / protocol version / chain);
5. runs the session with `cargo run -p arena-worker --example bench_session`:
   the worker's real `BENCHMARK` stage on the **Firecracker** backend
   (judge-run `prepare`; cold, warm-up, measured, fresh-confirm rounds in a
   seeded random order; every proof claim-checked and verified; the request pin
   checked on every request), with calibration runs before and after;
6. writes `host-profile.json`, `build.log`, `session.json` (every raw run,
   the schedule, job output, calibration, load averages) and `summary.json`.

## Limitations (read before using a number)

* **Dev host.** The shared development box is not a governed host (§4.1):
  SMT on, `powersave` governor, boost on, no `isolcpus`, other tenants'
  load (load average recorded in `session.json`). Numbers are labelled
  `dev-host` everywhere and are not official.
* **Calibration stand-in.** There is no governed calibration binary yet; the
  session runs `sha256` over 256 MiB of zeros in the same sandbox and cpu set
  and applies `arena_bench.calibration.check_drift` without a reference
  median. On this host the drift/noise checks are expected to fail; the
  verdict is recorded, not acted on.
* **One VM per invocation.** The Firecracker backend boots a fresh microVM
  for every `prove`/`verify`, so "steady state" (§4.3) has warm *host* caches
  but a cold guest page cache: each prove pays guest-side binary loading.
  Medians are therefore dominated by sandbox-level process start, which is
  part of what every candidate is charged under this backend.
* The session's own score uses `baseline_ns = 1` (no baseline exists yet) and
  is meaningless; against the pinned medians the reference scores 100.000.
