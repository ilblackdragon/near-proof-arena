# W08 warm-cache coherence and UQ-001 — 2026-10-29/30

Lane: workplan item 7 (W08) and UQ-001 of item 8. Worktree branch
`worktree-agent-abdc02168951d8fa3`, base main `4f07a7fdf`. Evidence:
[w08-warm-cache](../evidence/lean-chunk-completion/w08-warm-cache/README.md).

## Commits

| commit | what |
|---|---|
| `7777cb831` | cherry-pick of `c8b2aeccd` (unmerged branch `worktree-agent-a103b9b4017fa3668`): the 224 `d2corpus.v2` witnesses re-captured cold with code; the shared corpus on disk already had them, so main's manifest did not match the disk |
| `1d1a8ab47` | complete-code policy resolves deploy-served code as the cold validator; race exclusion named `e.code_prep_race`; harness and pair check updated |
| `9ddd6e68c` | generator: `src/cachejudge.rs` (forced eager/lazy schedules, warm and poisoned caches), labels `e.code_prep_race` / `e.code_deploy_served`, scenario `code-cache`; `tools/d3/check_cache_independence.py` |
| `416bc8bd2` | drop the draft recorded-race reject: the complete policy is the cold resolution on authenticated bytes (`complete_eq_cold`) |
| (this) | evidence (`docs/evidence/lean-chunk-completion/w08-warm-cache`), 24 portable cases, fixture selector, log |

## Measured on this host

* Lean `CodeResolution` laws build with `propext`, `Classical.choice`, `Quot.sound` only; 31 `#guard`s.
* STRAT (18,553), pre-change `completeCodeGlobal`: 886 `w.code_complete` rejects, 178 on
  nearcore-accepted chunks (identities and composition in the evidence README).
* W08 population (103), final binary: the 8 nearcore accepts accept; the 95 races are
  `out of domain (e.code_prep_race)` (were `w.code_complete` rejects in `completeCodeGlobal` and
  `e.wasm-α` exclusions in `allFeatures`).
* `code-cache` family, 3,934 cases over 5 seeds: no Lean accept of a nearcore reject on either tier;
  UQ-001 check 0 violations.
* `check_code_witness_policy.py` (5 pairs): pass with the new binary, fails with the old one.
* `make pin-check`: all ok. `python3 -m unittest oracle/tools/test_code_witness_policy.py`: 11 ok.

## Not done / carried over

* `tools/d3/smoke_successor.py` passed its 13 tier comparisons (completeCodeGlobal now compared on
  all 7 smoke cases) and then hit its fixed 120 s subprocess timeout in the unrelated V2 parent-map
  section under host load ~170; not rerun.
* No full 13-tier census and no full-corpus (235,716) rerun: host oversubscribed, coordinator capped
  this lane at 4 checker processes. `allFeatures` and the other cold-policy tiers change only the
  race reason string by construction.
* Generation runs 801–804 were stopped early (758–897 cases each) to free the host.
