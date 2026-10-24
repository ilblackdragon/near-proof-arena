# Parallel commitment: 804 receipts in 3.13–3.30 seconds

2026-10-24. **244,814-byte packet**, using four CPU cores and the existing
source-byte-limited source/outcome relation. Fresh verification with the older
serial-backend binary passes. The **1–2 s deadline is still unmet**, and this
is not full NEAR validity or PQ128 history recursion.

## Measured bottleneck and change

Opening substage timings identify LaBRADOR as the dominant remaining cost:
1.391 s of a 1.734 s opening. Rust fold/encoding are 74/53 ms, masks49 ms,
statement118 ms, and the other substages are smaller. Row evaluation and the
left commitment account for the small remainder outside these substage timers.

The independent Ajtai commitment column groups now run in scoped Rust worker
threads. Workers read immutable key/witness data, own disjoint retained-transform
slices and private scratch/output buffers, and return results in original column
order. No transcript operation or C backend call runs concurrently. Serial
behavior remains the default; `LABINIUS_COMMIT_THREADS=4` opts into four workers.
Values outside 1..32 reject. Small column counts fall back to the serial kernel.

## Validation and timings

**210 exact parity cases** compare serial/parallel commitment matrices, every
raw residue and every retained-transform coefficient and representation. They
cover two key lengths, seven column counts, zero/full/random witnesses, five
modulus limbs, worker counts1/2/3/4/8 and workspace reuse. Uneven worker partitions
are included. This checks the intermediate data later consumed by folding, not
just the final commitment digest.

| Stage | Serial commitment, Rayon4 | Parallel commitment, Rayon4 |
|---|---:|---:|
| Commitment | 641 ms | 248 / 218 ms |
| LaBRADOR opening backend | 1,391 ms | 1,400 / 1,391 ms |
| Total opening | 1,734 ms | 1,738 / 1,723 ms |
| Total prover | 3,708 ms | 3,244 / 3,075 ms |
| Read/fill/prove/export | 3,765 ms | **3,299 / 3,130 ms** |

All runs use CPUs8–11, four distinct physical cores, with `RAYON_NUM_THREADS=4`.
The same original 804-receipt list and circuit are used. These are limited warm
observations, not p95 or an isolated-host speedup guarantee. Cold construction/
setup and original claim/witness preprocessing are excluded. Two-run parallel
process peak RSS is 12,590,880 KiB under the same 16 GiB virtual memory cap.

Both proof runs pass seven public-input mutation checks. The final packet's
public bytes independently match the original fixture. Fresh CPU8 verification
uses the **unchanged source-byte-budget checkpoint binary** (hash checked against
its manifest), no receipt witnesses, and takes **1.442 s**. Backend bytes roundtrip;
profile/root/tape mutations reject. Packet format, parameters, security policy
and statement are unchanged.

## Remaining work

LaBRADOR alone is still about 1.39 s; the complete opening is about1.73 s.
Investigate that backend's arithmetic/work breakdown next. Further Rayon worker
sweeps do not directly address it. Any backend optimization must preserve exact
protocol/transcript/norm behavior and avoid shared randomness/workspace races.
Do not reduce security policy to meet the latency target.

The current relation still omits source inclusion in the chunk claim,
authenticated accounts/state/context, other lists in the chunk, full runtime,
complete outcome-root integration and bounded history. Composed PQ128 remains
unestablished; C decoding is for trusted local exports. The source-byte-limited
profile remains an explicit restriction with the full profile available.

## Reproduction

Apply `evidence/parallel-commit/parallel-commit.patch` to the prior isolated
LaBinius checkpoint, add the archived test and `near-receipt-list-stages` driver,
and retain prior support modules and stronger-policy backend. Build using the
explicit native RUSTFLAGS and target directory documented in earlier checkpoints.

```
cargo test --release -p labinius --test commit_parallel -- --nocapture
LABINIUS_COMMIT_THREADS=4 RAYON_NUM_THREADS=4 NEAR_EXPORT_DIR=EXPORT_DIR \
  taskset -c 8-11 near-receipt-list-stages 1024 compact ORIGINAL_LIST
RAYON_NUM_THREADS=1 NEAR_VERIFY_EXPORT=PACKET NEAR_EXPECTED_PUBLIC=PUBLIC \
  taskset -c 8 near-receipt-list-budget 1024 compact
```

The last command intentionally uses the older verifier binary. Evidence retains
source, narrow patch, parity log, baseline substage timings, final timings and
source/binary/packet hashes.
