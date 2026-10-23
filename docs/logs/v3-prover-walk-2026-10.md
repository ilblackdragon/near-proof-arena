# lane/v3-prover-walk — scheduler-side witness→entries dumper (2026-10-13)

## Goal
The receipt (`lane/v3-prover-rcptfam`) and trie (`lane/v3-prover-trie`) lanes cover
the witness→entries dumpers for tables 16–20/22–24 and 2–7/21 respectively.
This lane adds the remaining **scheduler-side** dumper: tables 11–15 (`codec`,
`scandist`, `proc`, `mem`, `cmp`) and the ChaCha lane 8–10 (`chacha`, `rng`,
`shuf`) from a real D0a witness.

## Deliverable
* `examples/np-udr-stark-v2/conformance/SchedEntriesV3.lean` →
  `np-lean-sched-v3 <case_dir> [<out_dir>]`. Reads `claim.bin`/`witness.bin`,
  requires `checkD0a B0 = .ok ()`, re-runs the native execution (walk, main
  `applyNewChunk`, implicit `applyMissingChunk` steps via `traceImplicit`),
  reconstructs each applied block's `SchedIn` from
  `ActualRun.run (ProcPreparedSequence.input sp prev) τ` and `distRows`
  (`gb`, `a0 = a0Canon n prev`, `present`, `prev_hash = prev.sanityHash`), and
  emits `sched.json` (Rust `sched::SchedIn` list) plus `chacha.json` /
  `rng.json` / `shuf.json` (`ChachaLane.laneReqs`/`laneCalls`/`laneInsts`).
* `examples/np-udr-stark-v2/conformance/SchedJson.lean` — the shared `NpSched`
  JSON mirrors, extracted from `RenderV3Sched.lean` so both modules import it
  (the exe root `main` no longer clashes).
* `examples/np-udr-stark-v2/conformance/run-v2.d/schedentries.sh` — differential.

## Validation
* `np-lean-sched-v3` runs on real `public-d0a/d0` fixtures.
* Rendering the dumped `sched.json` with `np-lean-render-v3-sched` and with
  `npudr v3render` is **byte-identical** for `codec`, `scandist`, `proc`, `mem`,
  `cmp` (Lean's `maxRows` prefix vs the Rust full 2^22 table; the common prefix
  matches on every tested fixture). `npudr v3check … cmp` accepts.
* The D0a fixtures carry no bandwidth requests, so `gb`/`raw` are empty and the
  ChaCha lanes are empty; a fixture with requests would exercise the nonempty
  ChaCha path (the seeded sampler in `RenderV3Sched` already covers it).

## Note
`npudr v3render <table> <sched.json>` is the Rust consumer; no separate Rust
command is needed (the existing `sched.rs` reader parses the same `SchedIn`).
