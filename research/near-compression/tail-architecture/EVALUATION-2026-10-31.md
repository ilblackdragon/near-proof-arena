# PQ tail architecture — integrator evaluation (2026-10-31)

**Status: research direction, NOT proven. Nothing in this directory is a qualified
NEAR chunk proof, a PQ128 security claim, or an arena submission.** The lane was merged
into `main` (`7838aef7b`) only so the work and its evidence are not lost. Every
number below is the lane's own measurement unless marked otherwise; none was
re-measured for this evaluation.

## What the lane measured

Custom circuit on a lattice backend (LaBRADOR / LaBinius, Module-SIS), not the main
stack's SHA384/WHIR STARK.

| Result | Number | Source |
|---|---|---|
| Receipt relation + in-circuit state-trie authentication (NPMULT03), 814 / 711 real receipts | 250,126 B packet, ~3.0 s warm prove (4 CPU cores), ~1.5 s verify | `ACCOUNT_LEDGER_HANDOFF.md` |
| Wasm vertical slice (NPMWASM02): stack, locals, memory, 42 integer ops | ~1,452 AND/step, 0.30× the D0a receipt slot | `WASM_LADDER.md` |
| Wasm ladder 8 → 2,048 steps | packets 157–209 KB, flat in steps; prove 0.26 → 2.0 s | `WASM_LADDER.md` |
| Receipt + Wasm on one commitment (NPMULT04, 64 Wasm steps) | 250,226 B, 7.2 s prove, 2.1–2.5 s verify | `WASM_EXEC.md` |
| zkVM comparison (Jolt + Dory) | 98,154 B, 102 s prove; non-PQ; folding chunk-sized proofs intractable on CPU | `ZKVM_NEAR_CHUNK.md` |

## Why it is worth keeping

The main stack's open problem is proof size: depth-2/3 production aggregation nodes are
315,913 / 322,027 B, over the 300,000 B cap
(`../results/pq-agg-depth-law/EXTRAPOLATION-1PGAS.md`). This lane is the only measured
path whose packets sit well under the cap (150–250 KB) and do not grow with circuit
size. That is the property a terminal compressor or accumulator needs.

## Why it is not a proven direction

1. **Security is probably below 128 bits on the headline packets.**
   - `OUTER_SECURITY.md` models the ring-648 main commitment with moduli {3889, 2917, 4861}
     at **79.2 bits**, and 125.6 bits with 9721 added. The bridge keys Y/u/R model at
     96–120 bits under the existing 168× factor.
   - The stronger policy that clears 128 bits (minimum 140.45, `SIS_POLICY_EXPERIMENT.md`)
     was applied to the hash-template component only.
   - The NPMULT03/04 packets run on the suite that uses the 4861 moduli set (`WASM_LADDER.md`
     "sizel"). This evaluation infers from that, without re-measuring, that those packets are
     not 128-bit.
   - Not analysed: outer PCS, the 16-byte backend transcript (SHAKE128/AES128),
     structured-lattice attacks, Fiat–Shamir/QROM losses, composition.
     `security_established = false`.
2. **No accumulation or folding.**
   - A single circuit stops at the 2,048-step dense-build wall. A 1 Pgas chunk is around
     10⁹ Wasm steps, about 500–2,900× the largest rung measured.
   - The committed accumulator (README "Experiments", item 4) is specified but not implemented.
3. **Latency.** The target is 1–2 s, including trace generation; NPMULT04 at 64 Wasm steps takes
   7.2 s. No GPU was measured: `GPU_ESTIMATE.md` is a hypothesis.
4. **Coverage.**
   - The circuits cover the D0a transfer slice and a Wasm subset: no host calls, no division.
   - Opcode bytes are bound to the code digest only by a host audit, which is a soundness gap.
   - The default receipt profile fits 4 of 64 corpus cases; the largest D0a witness
     (156.6 M cells) does not fit.
5. **Not linked to the Lean statement.** The circuits prove their own NPM relations, not
   `RelD3` / `Tier.rel .allFeatures`. There is no join theorem.
6. **Nondeterministic packet size.** One run gave 295,038 B instead of 250,126 B.
7. **Changes the assumption base.** Module-SIS / lattice assumptions are a departure from
   the SHA384-only baseline that the arena's security claims assume. The owner has not
   decided to accept this.

## Go / no-go gates, in order

1. **Security.** Regenerate the receipt+Wasm packet under the stronger SIS policy, with every
   commitment ≥ 128 bits in the scalar model, and re-measure size and time. If the packet
   no longer fits comfortably under 300,000 B, stop the lane.
2. **Accumulation.** Implement the committed accumulator over 1/2/4/8 segments. Terminal size
   must be sublinear in history, and verification must not need historical witnesses.
3. **Scale.** Prove blocks past the 2,048-step wall and fold two blocks at that scale.
4. **Wasm soundness.** Bind opcode bytes to the code digest in-circuit.
5. **GPU.** Benchmark one commitment/opening kernel on an H200 before quoting any 1–2 s figure.

Owner decision needed before step 1 starts: whether a lattice assumption is acceptable for
the final proof layer.

## Housekeeping

The lane worktree (`/data/illia/nearproof-wt/pq-tail-architecture`) has about 780 tracked
`research/near-compression/native/wasm-base/target/` build files deleted locally. Those
build outputs should be untracked and ignored, not restored.
