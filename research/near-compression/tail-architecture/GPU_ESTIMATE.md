# Conditional GPU latency estimate

User deadline: final proof within 1–2 s of chunk, including trace generation.
These are engineering hypotheses for the three small D0a fixtures, **not GPU
measurements**. No GPU implementation was run. Current code remains CPU-only.

| Implementation scope | RTX 5090 | H200 |
|---|---:|---:|
| Tuned port of bulk prover work; much CPU orchestration retained | 4–7 s | 3–6 s |
| Aggressive whole-path optimization, GPU-resident buffers and faster trace generation | 1–3 s | roughly 1–3 s |

Basis: smallest measured live case is 2.28 s trace + 14.98 s proving. Internal
frontend/stacking and shared-opening stages account for about 13.23 s; remaining
prover work about 1.6 s. For a first port, assume 5–12x speedup of bulk stages on
5090 or 8–20x on H200, plus roughly 2–4 s remaining host/transfer work. These
speedup factors are assumptions to benchmark, not derived from peak specs.
The aggressive scenario must additionally reduce host work/trace generation
below ~0.5–1 s and bulk proving to ~0.5–2 s. It has substantial implementation
and measurement risk. The host was concurrently loaded during these observations.

5090 has 32 GB and 1.792 TB/s memory bandwidth; H200 has 141 GB and 4.8 TB/s.
Sources: [NVIDIA 5090](https://www.nvidia.com/en-us/geforce/graphics-cards/50-series/rtx-5090/),
[NVIDIA H200](https://www.nvidia.com/en-in/data-center/h200/).
H200's 2.68x peak bandwidth advantage does not imply 2.68x total speedup. SHA384,
field arithmetic, NTT/sumcheck reductions and transfers require separate profiling;
AI tensor throughput is not the relevant performance metric. The 5090 may be
competitive on compute-heavy integer kernels; neither ordering is benchmarked.

Largest screened D0a fixture: 156.6M cells, ~124x smallest, current profile rejects.
There is no supported whole-chunk GPU latency estimate for this case, D3 or a
recursive tail. A linear extrapolation of small-case GPU timings would be highly
uncertain and would not support a 1–2 s claim. H200 memory provides more room for
larger domains, but does not remove work. Optimized kernels preserve proof bytes
only if protocol, statement, arithmetic and parameters remain unchanged.

Next useful experiment: exact GPU kernels for retained commitment/WHIR and a
full trace-generation path, with canonical CPU/GPU proof verification and device
memory/transfer accounting. Then benchmark direct receipt/hash representations
against the 156.6M-cell workload. Do not count throughput as single-chunk latency,
or silently omit recursion, setup/profile security, or full NEAR semantics.
