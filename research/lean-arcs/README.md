# Lean Wasm arcs: bulk-skipping zero-fee control runs (W02 evaluation-time)

Status: **validated prototype** (perf evidence only — the equivalence theorem is *not* proved yet;
nothing here is wired into the successor checker). Repo-relative, builds against the pinned
`NearSpecV3` package (`lake build`; toolchain v4.34.1).

## The problem (measured, `docs/evidence/lean-chunk-completion/fuel-termination/`)

After W02 raised the step budget to `wasmFuel` (= `(gas/regular + 2)·10,002 + 10⁶` at PV86),
fuel no longer rejects valid runs — but *evaluation time* replaces it as the binding limit.
`nearspec-v3-fuel-probe` on the worst contract (`blocks4999`, a loop of 4,999 zero-fee
`block`s + one `br`):

* 0.3 Tgas: t = 1,715,538,431 steps, 440 s on the loaded evidence host (3.9 M steps/s) →
  300 Tgas ≈ 1.7·10¹² steps ≈ **55 h** at 8–9 M steps/s (the evidence README's figure;
  re-measured 48.3 s for the packaged 0.3 Tgas case on an idle 32-core host → ≈ 13 h there:
  the figure is honest for its stated host).
* Root cause: finite-wasm *merges* the loop's fees into one charge point per iteration
  (fee = 2·regular_op_cost at pc 1), so the interpreter single-steps ~10⁻⁴ zero-fee
  `block`/`end` pairs per charged step — ~10⁻⁴ steps per 2·822,756 gas.

## The fix: precomputed arcs over zero-fee `block`/`loop`/`end`/`nop` runs

Per function, `buildArcs` scans `pf.code`/`pf.gas` (tables `prepare` already produces) for
maximal runs of pcs that are (a) `block`/`loop`/`end`/`nop` and (b) free (`gas[pc] = none`).
An arc records the net effect of single-stepping the run:

* `runEnd` — first pc after the run; the fused trailing `br l` if the run ends at one;
* `pops`/`pushes` — label-list surgery: drop `pops` entry labels, push `pushes`
  (target/arity/isLoop static; `height := s.stack.size` at arc entry — constant inside the
  run because no run instruction touches the value stack);
* `guard` — required entry label depth so that (i) every `end` in the run pops a *run*
  label (never `doReturn`, never an entry underflow) and (ii) the fused `br l` is not a
  return. Under the guard the run is a pure pc/labels relabel: one arc step replaces
  `runEnd − pc` single steps **and consumes the same fuel**, so `wasmFuel`'s meaning,
  every fuel-monotonicity theorem and the `successorFuel_moves_only_exhausted` statement are
  unchanged; the fused-br charge keeps the real `charge` call (same failure states).

`stepArc` fires an arc only when the guard holds; otherwise it is exactly `Exec.step`.
The design is *additive*: `Exec.step`, `Exec.run`, `Prepare`, `FiniteWasm` are untouched, so
the signed `D3` path and every existing theorem are unaffected; the target theorem is
`runArc = run` (fuel-parameterised), after which the successor's `StorageExecution` can
switch wholesale.

## Measured results (this host, compiled `arcproto` binary, pinned NearSpecV3)

A/B = identical `Wasm.outcome`-style line (burnt/used/status/return) for old vs fast:

| case | old | fast | speedup |
|---|---|---|---|
| `blocks4999` @ 2·10¹⁰ fuel | 439,604 ms | 298 ms | **1,474×** |
| `blocks500` @ 2·10¹⁰ fuel | 464,755 ms | 3,078 ms | **151×** |
| `blocks4999` @ **300 Tgas full wasmFuel** | (est. 13–55 h) | **26.7 s** | ~10³–10⁴× |
| `nops` 300 Tgas | 7,256 ms | 3,911 ms | 1.9× |
| `spin` 300 Tgas | 12,764 ms | 13,609 ms | 0.94× (no arcs fire) |
| `mixed` (realistic loop, small arcs) 300 Tgas | 1,193 ms | 1,321 ms | 0.90× (see L3) |

Parity: **9,375/9,375 exact** — 200 `gen_d3a.py` random contracts (seed 7) + 9,175
`opcases.py` opcode/limit cases at 300 Tgas, plus the directed shapes above (incl. the
4,999-block cap contract `cap4999`, `deep200` push-heavy arcs, `mixed` calls/locals/globals).

`buildArcs` at the 4,999-block cap: ≤ 2 ms per prepare (amortised once per call; the table
is per-`Prepared`, so ~2 ms per contract call, not per step).

## Honest limitations (what production must fix)

* **L1 — no theorem.** This directory is a perf prototype. The equivalence `runArc = run`
  (and the charge-fail-state equality for fused charged brs) must be proved in Lean before
  the successor can use it; the guard/label-surgery argument is mechanical but every `exec`
  arm and the `afterRun` charge-fail replay need covering lemmas.
* **L2 — fused-br materialization subtlety.** Fusing a charged `br` keeps `charge` on the
  pre-arc state *when it fails* (`afterRun` replay) and on the post-charge state when it
  succeeds. The prototype recharges on the post-run state in the failure path to match
  single-stepping exactly (verified by parity); the theorem must pin this equality.
* **L3 — short-arc overhead.** On realistic loops whose free runs are 2–4 steps
  (`mixed`), the arc bookkeeping costs ~10% *net* — the production version should apply a
  minimum-run-length threshold (e.g. ≥ 5, chosen because the charged-br step dominates
  otherwise) or fuse only loop-back arcs.
* **L4 — `else`/`if` not fused.** Only `block`/`loop`/`end`/`nop` runs; `else`/`if`/`br_if`/
  `br_table` single-step (they read the value stack). Mainnet contracts compiled by
  rustc are `block`-heavy, so coverage is already near-total for the worst case, but a
  follow-up can extend runs across `if`-ends.
* **L5 — one host, one seed.** All numbers are from a single 32-core host (other load
  present); the corpus parity is the repo's own generators, not the full 3,138-census /
  235,716-case corpus replay, and not against nearcore.

## Why bulk-skip is *sound* here (the semantic observation)

Zero-fee `block`/`loop`/`end`/`nop` instructions cannot touch the value stack, locals,
globals, memory, gas or host state; their whole observable effect is `pc` + the label list.
With the label-depth guard the label surgery is determined by static tables (`endOf`,
`btResults`), so a run collapses to one jump. This is the same trick a JIT does with
superblocks, but kept inside the definitional interpreter so that the kernel-reducibility
of the relation (and the segment proofs in `Wasm/Segment.lean`, which `seg`-split exactly
this `run`) survive unchanged.
