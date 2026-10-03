# reexec-witness-fast: prover-only child of `reexec-witness`

This is a child of the reference candidate `examples/reexec-witness`. Submit it
with `--parent <reference submission id>`. It changes **only the prover**.

| artifact | vs. parent |
|---|---|
| `formal/` (certificate, verifier model, proof codec) | byte-identical (same formal tree digest, same certificate decl) |
| `out/verify` (Lean model compiled in the judge's native-lean layout) | byte-identical (built from the identical `formal/` and `source/lean-vendor/`) |
| `out/prepare` / `public.bin` | byte-identical (`prepare` is std-only and built with the parent's exact flags) |
| `out/prove` | different |

The judge should therefore classify the child `PROVER_ONLY` and reuse the
parent's formal gate results. Build, conformance, adversarial, reliability,
limits and benchmark gates still re-run.

## Prover changes (`source/src/{trie,engine}.rs`, `build-recipe/build.sh`)

1. **Statically linked `prove`** (`cargo rustc --bin prove -- -C
   target-feature=+crt-static`). The judge starts one process per request, and
   for these workloads dynamic loading costs about as much as the computation.
   Only the `prove` crate gets the flag, so `prepare` stays bit-identical to
   the parent's.
2. **Trie reveal by sorted key ranges.** The receiver keys are sorted and
   deduplicated once, and every subtree takes a contiguous sub-slice. The
   parent instead re-filtered the full key list into fresh vectors at every
   node, 16 times per branch.
3. **Locate each receiver once.** A receiver → value-node cache marks the path
   dirty once, which helps on the `repeat` profile with its hot receivers.
4. **Identity hashing for the witness store.** The store keys are SHA-256
   digests, so their first 8 bytes are used directly instead of SipHash.
5. The application loop no longer interleaves hashing. Outcome and refund
   commitments are computed after all state updates. A two-thread variant
   (trie root ∥ outcomes) was tried and dropped: on a loaded host it was
   slower, because thread start-up and scheduling noise outweigh about 100 µs
   of hashing.

Output is unchanged. Claims **and proofs** are byte-identical to the parent's
on the 20 public fixtures and the 740 generated cases (seed 777, 600 in-domain
and 140 out-of-domain refused).

See the parent's README for the proof system, formal certificate and
limitations.

## Local measurements (informational; the judge measures)

These numbers come from `examples/bench/measure_provers.py` on the challenge's
workload classes (`near-arena-oracle gen --receipts {1,16,256}`, seed 9001,
8 requests per batch, matching `batch_size`). Each request runs in a fresh
process. The provers were interleaved over 31 timed rounds. The host was a
shared 32-core machine at load average 40–55, so the medians are noisy.

| class (weight) | reference median / min batch | fast median / min batch | spawn floor (`/bin/true`) |
|---|---|---|---|
| batch-1 (20 %) | 3.53 / 2.25 ms | 2.26 / 1.38 ms | 1.97 / 1.23 ms |
| batch-16 (30 %) | 3.49 / 2.46 ms | 2.19 / 1.57 ms | 1.77 / 1.25 ms |
| batch-256 (50 %) | 4.44 / 4.17 ms | 3.68 / 3.30 ms | 1.39 / 1.30 ms |

Plugging the medians into the challenge's score formula, with the reference
as the baseline (100), gives about **138** for this child. In-process
`engine::prove` (`source/examples/inproc.rs`, minimum over 300 repetitions)
takes 3.4 / 21.6 / 198.5 µs per request for the reference and
3.2 / 20.8 / 159.7 µs for the child. Most of the gain on small batches comes
from avoiding the dynamic loader at process start.
