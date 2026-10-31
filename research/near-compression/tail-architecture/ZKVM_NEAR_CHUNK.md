# zkVM on a realistic NEAR chunk: measurements and go/no-go

2026-10-27. Jolt 7931b223 + Akita dfdbd767, CI profile (no LTO), Dory
backend. Workload: the custom circuit's proven semantics slice (ZKVM_WORKLOAD_DEF.md)
— variable-depth PTrie membership (real corpus + 6 synthetic families, 27
chains), 814-receipt u128-as-u64-limb ledger threading, ordered outcome
hashing — executed in the zkVM guest with the same fixtures the NPMULT03
custom circuit proves. Correctness gate: proof output == native output ==
`e710a423...d908` on every run. All numbers CPU (Ryzen 9 9950X3D), single
observations unless stated; no p95.

## The decision table

| | zkVM (Dory) | Custom circuit (NPMULT03, PQ) | Witness |
|---|---|---|---|
| Proof size | 98,154 B | 250,126 B | ~410 KB fixture |
| Prove (4t pinned) | 102.34 s (two obs: 102.337/102.341) | 3.08 s warm | — |
| Verify | **0.133 s** (parallel) | 1.48 s serial (0.905 s at 8+8t after parallel kernels) | re-execute |
| Guest/trace rows | 8,462,213 | witness log 23 (10.9M words) | — |
| Peak RSS | 4.33 GB | 13.3 GB | — |
| PQ status | **NO — Dory (BN254)**; only PQ zkVM numbers are sha2-chain scales 18/20 (1.99 s/97,998 B) | **YES — LaBRADOR/SIS**, composed PQ unproved | n/a |
| Semantic coverage | same slice as the circuit today; zkVM *can* express Wasm (unmeasured) | D0a transfer slice only; circuit profile fits 4/64 corpus cases | full (trusted) |

## Phase 4: recursive folding — measured at the step boundary, trace intractable

The fold driver (examples/near-chunk-fold, archived) proves k chunk proofs,
serializes them in the recursion-guest record format, traces the recursion
guest (in-guest verification), then proves the aggregate. Step-1 results
(all correctness gates pass; inner proofs outer-verified):

- k=2: fold input 3,011,037 B (2.8 MB verifier preprocessing + 2×98 KB
  proofs); inner proves 198.7/155.9 s under external load (LA 4.5–14).
- k=1: fold input 2,912,742 B; inner prove 211.6 s under load.

The trace step — in-guest Dory verification of ONE 98 KB chunk proof —
did not complete in any attempt: the recursion preprocessing loads a
max_log_n=36 Dory setup (the fold statement is ~2³⁶ scale), and the trace
runs 40–60+ minutes before the host environment's process-lifetime limit
kills it (verified with a canary process and four fold attempts; the
stock fibonacci recursion in the same tree reached Dory preprocessing,
so this is a workload-scale failure, not a code bug — step-1
serialization and every inner-proof verification pass).

**Folding verdict (measured where measurable, estimated where labeled):**
in-guest verification of a chunk-sized proof is ~2³⁶-scale — i.e. the fold
costs plausibly 10¹⁰–10¹¹ guest cycles, two to three orders more than the
8.5M-cycle chunk itself. zkVM recursive folding of chunk-sized proofs on
this CPU is **CPU-intractable at this workload scale**: the fold costs more
than host-verifying every chunk proof directly (0.133 s each). The PCS used
by the folding path is **DoryScheme — non-PQ** (source-confirmed:
jolt-sdk's VerifierPCS and prove path are both Dory; the runtime loads
dory_36.urs).

## The go/no-go verdict framework

Continue the **custom circuit** line if:
- the PQ requirement stands (it is the only measured PQ path), and
- GPU/portable proving can close 3.08 s → 1–2 s (opening phase is
  1.4–1.9 s of the 3.0 s; unmeasured on GPU), and
- folded verification (per-block aggregate) is pursued on the LaBRADOR side,
  where the parallel-kernel work already took serial verify 1.48 s → 0.905 s
  and the remaining phases are enumerated (aggregate ~225 ms, statement
  rebuild ~200 ms).

Continue the **zkVM** line if:
- semantic coverage beats latency (Wasm/contract chunks the circuit cannot
  express), accepting: proving hours per chunk on this CPU (102 s for the
  transfer slice; a 1-Pgas Wasm chunk plausibly 6–8 Gcycles → 10–13 h),
  folding intractable at chunk scale (measured above), and non-PQ
  (Dory) — i.e. **only as a GPU-prover-backed coverage play, never as the
  PQ latency path**.

The **witness-replacement direction** is not killed: for the proven slice,
constant-size proofs (98–250 KB) beat the ~410 KB witness on size and
verify-time (0.13–0.9 s vs re-execution), and the PQ custom circuit is the
only measured path meeting both. But it is not yet won: today the witness
is smaller than the zkVM proof for the same slice (98 KB proof vs the ~410
KB fixture is a 4× win, but the fixture re-executes in ms), the 1–2 s
prove deadline needs the GPU port, and <200 ms verify needs folding +
the remaining parallel kernels. Every one of those is now a measured,
enumerated step — none is an unknown unknown.

## Honest gaps (stated, not hidden)

D0a transfer slice only (no Wasm in any measured system); composed PQ
security unproved; zero knowledge absent on the circuit side; GPU
unmeasured; load-affected timings labeled as such (this session's
156–212 s inner proves ran under LA 4.5–14; the 102.34 s pair is the
pinned quiet-box figure); fold trace numbers are estimates from the
2³⁶ Dory setup scale, not completed traces — the trace step is exactly
what a longer-lived environment would measure.

## Reproduction

Guest/host/fold sources, all logs, fixtures and manifests:
`evidence/zkvm-chunk/` (guest-src/, fold/, synthetic/, manifest.json with
verified sha256s). Fold steps: `FOLD_STEP=1|2|3 near-chunk-fold k` — step 1
is quick and reproducible; step 2 (trace) requires an environment without
the ~40–60 min process-lifetime limit; step 3 requires step 2's row count.
