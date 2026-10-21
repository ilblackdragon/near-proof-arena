# D0a proving performance pass, 2026-10-21

No tested runtime optimization was promoted. The default remains eight threads.
Full proving measured **52m 24s**, independent verification **2.08s**, and the
packet remained **299,967 bytes**, excluding pinned setup.

The buffer/copy candidate was not faster (final phase 524.521s vs 521.749s).
SIMD padding was slower in matched kernel trials. The sixteen-thread proof
trial was interrupted by external contention and is excluded from latency
comparisons. No full proof with padding enabled is claimed.

See [method, limitations, and reproduction](../../native/pq-chunk-e2e/PERFORMANCE.md)
and [machine-readable results](RESULTS.json). The original packet is in
[the D0a result](../pq-chunk-e2e/d0a-h10004-s3/README.md). Both completed replay
packets and setup were byte-identical to it, verified with the original binary,
and passed tampering tests.

`baseline/` preserves the successful verifier timing and the helper-launch
failure that preceded it. The helper was restored from a hash-checked profiler
snapshot; this was not a proof rejection. Executable snapshots are now part of
the runners so cleanup/rebuilds cannot invalidate a long run's helper paths.

Raw profiles/counters and binary snapshots remain in the paths recorded in
`RESULTS.json`. The logs here cover 720 leaf-hash cases, eight streamed-proof
configurations, and 16 reference-DFT cases per padding setting. Kernel timing
uses a different CPU set from proof replay; only comparisons within each group
are meaningful. `MANIFEST.json` hashes the compact evidence files.
