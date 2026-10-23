# D0a chunk → bound recursion → verified final packet

Measured on 2026-10-21, fixture `public-d0a/d0/00-h10004-s3`.

| Artifact | Bytes |
|---|---:|
| Raw final proof | 299,935 |
| Hint | 16 |
| Packet framing | 16 |
| **Complete transmitted packet** | **299,967** |
| Trusted setup, uncompressed (excluded from packet) | 3,711,888 |

**33 bytes below 300,000.** This is a single measured fixture result, not a
worst-case bound or a guaranteed margin for another proof/shape. The setup is
pinned and run-specific; reuse across arbitrary chunks has not been established.
This is the D0a research protocol, not the D3 state/Wasm join. Witness masking and
the outstanding cryptographic soundness proofs are not established.

Base proof: 459,984 bytes. Recursive proofs L1–L5: 374,105 / 374,563 / 372,001 /
373,177 / 374,521 bytes. L5 binds to the converged program (137,196 rows), anchor
M=3. FINAL is level 6. The separate verifier re-derives the public values and TAPE
commitment from claim + hint and checks the pinned program. Changed TAPE root,
changed program, corrupted proof, trailing bytes, truncated hint, and untrusted
setup pin are rejected. See `verify.log`, `negative-packet.log`, and `RESULT.json`.

## Verify this artifact

Build `research/near-compression/native/pq-chunk-e2e/build.sh` after its setup.
Decompress `SETUP.json.gz` into a temporary directory and invoke the driver's
`verify AIR CLAIM STATEPUBLIC SETUP TRUSTED_SHA256 FINAL.bundle` command described
in the driver README. The trusted setup hash for this reviewed fixture run is
`b373c618279055625c9124d7c3d80e303f5d0abad7f8b59928f5c251b8812623`.
A receiver must provision the setup pin independently, not accept a sender's pin.
`MANIFEST.json` fingerprints the committed artifacts and identifies the fixture.

## Profiling

Profiling attached during L2: it covers the rest of L2, L3–L5 and FINAL, excluding
base/L1/early L2. Captured about 346,000 user-cycle samples with no lost samples;
peak process RSS was 14.34 GiB. Correctly symbolized samples attribute 28.31% to
`fast_dft::dif_rows`, 20.08% to `memmove`, and 22.76% to the two SHA-384 batch
routines. These are CPU-cycle shares, not promised whole-run speedups.

Raw data, preserved executable, counters, resource histories, and full logs remain
at `/data/illia/nearproof-deps/pq-chunk-e2e/runs/d0a-compact`. Use
`profile-chain/perf-symbols.data` for analysis: its build-ID metadata was corrected
against the preserved executable after the original binary path was rebuilt.
The original sample stream is retained. Brief compilation overlapped the run,
so timings are diagnostic; optimization comparisons need a controlled rerun.

Future `run.sh` executions profile every stage by default and record build IDs in
mapping events to preserve symbol attribution across rebuilds.
