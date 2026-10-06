# near-chunk-validation-d0-2 — superseded by plan (2026-10-06), never signed

`near-chunk-validation-d0-2.measure.json` (bench-spec-v1.4 cost_v1 successor of
`near-chunk-validation-d0-1`) is **dropped**. It will not be signed or registered.

* Plan change: one unified challenge, **near-chunk-v3** (statement `Rel_D3α`). Candidates
  declare the domain they cover and abstain outside it. Ranking is by coverage tier, then
  cost_v1. The design and draft are owned by the D3 lane. The separate D0–D3 cost challenges
  are no longer planned.
* Its reference measurements (`benchmarks/results/baseline-near-chunk-validation-d0-2-*`,
  4 attempts, none pinnable: BENCHMARK_SPEC §14.8) stay as data. They showed why
  near-chunk-v3 needs the paired baseline control and a real calibration binary (§6.1, §6.2).
* `near-chunk-validation-d0-1` (`chl_4b431651…`) stays the live, speed-scored D0 challenge
  until near-chunk-v3 supersedes it.
