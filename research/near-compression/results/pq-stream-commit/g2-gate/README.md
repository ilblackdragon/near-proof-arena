# G2 gate — real-settings chain + FINAL + V_d

Lane `lane/pq-stream-commit`. Circuit `lane/pq-recursion-sha384` @ `9159123be`; fast CPU prover
`lane/pq-cpu-prover` @ `6134476fc`; streamed commitments from this lane's overlay.

Run: 2026-10-19 15:01–15:47 UTC, 24 threads, peak RSS 17.15 GB. Log: `run.log`. Proofs:
`L1..L5.proof`, `FINAL.proof`. Hashes and gate markers: `MANIFEST.json`.

## Gate criteria (user-defined 2026-10-19)

| # | criterion | result |
|---|---|---|
| 1 | real-settings FINAL bytes ≤ ~296 KB | **293,077 B** — PASS (+6,923 B under 300 KB) |
| 2 | V_d accepts the FINAL under the pinned program | PASS (level 6, program 125,550 rows) |
| 3 | forged verify-nothing FINAL rejected with the program check (and accepted without it) | PASS, control live |
| 4 | the chain reproduces on a clean deps setup with identical proof sha256s | **PASS** — all six hashes and required controls match; `REPLAY-2026-10-21.json` |

## Settings

* Parameter-selection target: 268 bits = 236 query bits + z = 32 wide-PoW; 42-byte digests; coset leaves; ×15; every
  lever; `m = 64` with kernel-proved O-2 certificates only (`NEARPROOF_DKT_EXCLUDE`).
* Parent (penultimate) shape: `n_stack 18`, `k 4`, `log_blowup 7`, `k1 2`, `log_final 6`,
  queries `[44, 35, 27, 23]`.
* FINAL shape: `n_stack 18`, `k 4`, `log_blowup 7`, `k1 1`, `log_final 7`, queries `[41, 38, 29, 23]`.
* NvAir: 72 columns, 48 interactions/row, degree 9, committed heights
  `[262144, 1048576, 128, 65536]`.

## Chain and convergence

```
L1_PROOF_BYTES total=288297   program_rows=7634
NV_G2_ANCHOR L2: anchor level M = 1 (child bound by its root = C_M)
L2_PROOF_BYTES total=357805   program_rows=112994
NV_G2_ANCHOR L3: anchor level M = 2 (child bound by its root = C_M)
L3_PROOF_BYTES total=364283   program_rows=129966
NV_G2_ANCHOR L4: anchor level M = 3 (child bound by its root = C_M)
L4_PROOF_BYTES total=362939   program_rows=125550
NV_G2_ANCHOR L5: anchor level M = 3 (child bound by BIND)
L5_PROOF_BYTES total=364577   program_rows=125550
NV_G2 converged: 5 levels, 1 bound by BIND, anchor M = 3
```

The tight-height floor did its job: L2 and L3 were raised (`natural -> floor`), L4 and L5 fit the
same floor, so the program converged at 125,550 rows and L5 switched from anchor to BIND. Only the
FINAL proof is transmitted (293,077 B); L1–L5 are intermediate.

## FINAL

```
FINAL_SUMMARY cols=173 opened=291 interactions=30474496 L=25 cells=107283584
FINAL_PROOF_BYTES total=293077 gkr=32408 relations=24292 stacking=6832 whir=229346
FINAL_SOUNDNESS total=268.2 logup=323.4 proximity=281.6 query=268.2
FINAL_VK_REGIMES rounds all O2, q=[41,38,29,23]
FINAL_RESOURCES wall_s=441.4 peak_rss_gb=13.98 program_rows=125550
```

## V_d

```
NV_VD final accepted: level 6, pinned program 125550 rows
NV_VD claimed statement digest [17732126303648949035, ...] (app public values [[0, 1, 2178309]])
NV_VD wrong claim rejected: statement digest differs from the claim
NV_VD wrong level (5) rejected: level 6 != pinned 5
NV_VD check_final_program accepts the honest final
NV_VD forged final (776 rows) accepted without the program check, rejected with it:
      final program openings differ from the pinned program
```

## What this does and does not establish

**Establishes:** chain generation and verification at the recorded parameters, with cached
program commitments, anchors while heights change, BIND once converged, a single-commitment FINAL
pinned by V_d, and a live forgery control. The independent replay reproduces all six proof files
byte-for-byte. FINAL is a measured 293,077 bytes.

**Does not establish:**
* 1 Pgas or a NEAR chunk. The app is the fib fixture; this measures the recursion tail only.
* The interaction-count path: `max_interaction_count` stays 2^28 here, and the NV circuit's own
  AIRs fit it. The D1-class base needs 2^30 (see `tools/d1-pq-envelope`).
* A completed security theorem. `FINAL_SOUNDNESS` is calculator output under proof premises;
  the family-QROM instantiation, full WHIR transfer, NV faithfulness and recursive hash model
  remain open. See the paper Appendix C and `final-soundness/PROOF.md`.

## Known risks

1. **The NvAir 2^18 margin is thin and real.** This run needed 125,550 program rows; a paired
   run (`pq-cpu2/ckpt/chainA`) failed with `NvAir: 262572 rows exceed 2^18`. The model predicted
   256,031 with 2.3 % headroom, so model-vs-measured is ~2.5 %, not the 0.2 % previously claimed.
   Any added program rows (a wider app table, extra checks) can push it over and cost L 24 -> 25.
2. **293,077 B is 5,600 B above the earlier 287,477 B** provisional measurement (that one ran with
   `bind = false`). The margin to 300 KB is 6,923 B, i.e. 2.3 %.
3. **Historical cost:** the original chain took 46 min wall on 24 threads; its FINAL alone
   took 441 s and 14 GB. The independent replay below uses different thread settings.

## Independent replay (2026-10-21)

`REPLAY-2026-10-21.json` records all six matching proof hashes, every required log
marker, the rebuilt binary, lockfile, compiled test-source hash and source inputs.
`replay-2026-10-21.log` is the complete run. The original `MANIFEST.json` is kept
as historical evidence; its pending criterion 4 is closed by this supplemental
record. Reproduction is an implementation check, not a proof of soundness.

The fresh dependency setup exposed two setup issues (textual comparison of
successive patch hunks and an obsolete statement-encoding overlay) and missing
test instrumentation. The fixes preserve source-content checking.
`gate-harness.patch` only saves L1–L5 and exercises wrong-claim, wrong-level and
forged-final controls in the chain test. `reproduce.sh` applies it for the build
and restores the checked source afterward. All resulting proof bytes match the
historical manifest.

The replay used 16 threads on CPUs 8–15 and 24–31, with a 32 GB memory cap,
from dedicated dependencies and a dedicated build directory. The first clean
build reproduced FINAL; the subsequent test-instrumented build reused those
independently built dependencies and completed the full gate.

## Reproduce

```sh
research/near-compression/results/pq-stream-commit/g2-gate/reproduce.sh <fresh-deps-dir>
```

Needs network for the pinned upstreams and the repository DKT certificate files (or
`CERTS=`/`EXCL=` copies with the recorded hashes). Defaults to 16 threads and the
non-benchmark CPU set above; build memory defaults to 32 GB and chain memory to
60 GB (`HEAVY_MEM=32G` was sufficient for this replay). It sets up the checked trees,
builds with `--locked`, selects Cargo's reported test executable, runs the chain,
and compares every proof SHA-256 and required log line against `MANIFEST.json`.
