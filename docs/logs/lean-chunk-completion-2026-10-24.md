# Lean completion execution — 2026-10-24

Owner: integration agent. Base: main `6d526b0cf`.
Worktree: `/data/illia/nearproof-wt/lean-chunk-integration`.
Branch: `work/lean-completion-except-w05-20261024`.

Scope: W00–W04 and W06–W16, respecting their success criteria and dependencies.
W05 remains owned by the other agent: do not change or merge its arithmetic/host checkpoint.
Shared integration ownership: successor configuration, drivers, harness and CI; later semantic
adapters must preserve signed definitions and coordinate through the published interfaces.

First deliverable: executable access to all six existing successor configurations and fail-closed
replay accounting with executable/input/output identities. This supplies W01/W12 evidence tooling;
it does not close missing semantics, observable comparison or release gates.

## First executable checkpoint

W01: added an explicit-tier successor driver and a strict replay runner. Empty runs, duplicate or
foreign rows, missing outputs, invalid verdicts, I/O failures, crashes and timeouts fail. Reports bind
the executable, input files, output and harness sources; failed preflight invalidates an older pass.
Baseline D3 and float replay paths now use strict result accounting. Successor comparison permits the
explicitly widened gas band and only licenses residual exclusions on mixed-family cases.

W03: implemented the pinned x86-64 Wasmtime 45 pooling allocation model, including imports, tables,
distinct escaped function references, global alignment and instrumentation's additions. The
successor loading preflight returns a zero-gas failed call before charging/linking/method resolution.
The signed configuration disables it definitionally; the new preservation theorem's axiom closure
is only propext, Classical.choice and Quot.sound. The runtimeLimits configuration combines this
correction with floats, protocol gas and genesis. It is not evidence of a linear tier-inclusion chain.

Independent nearcore comparison: **1,030 / 1,030 exact full-output matches**, comprising 30 directed
and 250 generated cases for each seed 17/29/43/71. Outcomes: 361 loading failures, 669 successes.
The removed-check control reproduces the old success versus nearcore's loading failure.
The generated modules and recorded oracle outputs replay in corpus-free CI.

A separate versioned oracle package preserves signed v3-d3 sources while allowing a replacement
test contract and targeted calls. Four generated windows yielded **209 chunks that execute the
target contract: 204 accepted, five correctly retained ETH/ML-DSA exclusions**. Variants exercise
the exact size boundary, above it, and mixed import/table/function layouts. Four independently
judged chunk fixtures are committed. Removing the new check makes a valid loading-failure chunk
reject with an incorrect main-transition state root. This control runs in CI. A further 366 target-contract mutants agree with nearcore: 298 rejects
and 68 accepted mutations (not 366 semantic negatives).

W12: the pre-runtime combined gas/float/genesis driver passed **1,788 cases** (1,452 accepts,
134 rejects, 202 asserted residual exclusions). The selected population includes all recorded
genesis, float and above-cap cases plus bounded unchanged-domain controls. This is a verdict
checkpoint, not full observable or 1,000-block representative validation.

Evidence directories: ../../docs/evidence/lean-chunk-completion/{runtime-limits,runtime-chunks-209,runtime-mutants-366,combined-1788}.
The runtime mock comparison is full-output; chunk replay checks the existing checker's aggregate
commitments and verdicts. It does not yet emit the full W01 per-case computed-observable schema.

## Checks and remaining obligations

- Incremental Lean root/successor/driver build: 206 jobs passed; all six named driver executables built.
- 59 Python tests discovered: 58 passed, one environment-dependent corpus test skipped.
- Seven-configuration smoke: 35 comparisons; four runtime chunk regressions plus removed-check control.
- Full `make d3-smoke` passed, including baseline, successor and runtime gates.
- Runtime golden replay: 1,030 comparisons plus removed-check control.
- Pinned oracle checks and manifest schema pass. Inventory remains 222 rows / 28 missing-or-partial;
  source hashes now include InstanceLayout. This checkpoint does not relabel unrelated rows complete.
- W05 arithmetic/host files and branch commits remain untouched.
- Whole-checker gas monotonicity is still open: attempted proofs did not compile within their proof
  bounds; no failed theorem, sorry or semantic axiom was added to the repository.
- W03 still needs the remaining LinkError/WasmUnknownError environment/reachability audit and final
  package validation. Its pooling LoadingError branch now has executable and whole-chunk evidence.
- W01 still needs computed chunk observables; W00/W07/W08/W09/W11 still need shared semantic adapters.
- W04 still needs varied float whole-chunk families; W06 key algorithms and W10 overlap/fact closure
  remain open. W14/W16 depend on full W12 closure including the separately owned W05.
- W13 needs an authenticated validator witness source; requested its location from the user while
  continuing independent work. Pinned public JSON-RPC has no state-witness retrieval endpoint.
- W15's inspected D3 reference evidence is local/unsigned or partial, not a live formal-tier
  admission for the exact current package. No signing, deployment or admission is claimed.

## Runtime environment follow-up

The original `uq014_instance_size.py` now requires successor full-output parity and a removed-check
control, rather than succeeding on the old divergence. Fresh run passes all three legs including
nearcore preparation. The old signed checker is still intentionally unchanged.

The concurrency-permit branch cannot be dismissed as indefinitely blocking: pinned nearcore
`wasmtime_runner/mod.rs:239–260` increments a `u16` retry counter with `checked_add(1)?`.
Exhausting retries returns `None`, and `:1013–1019` turns that into a charged
`LinkError("failed to acquire execution slot")`. Whether a production execution can exhaust that
counter requires a scheduler/concurrency argument or measurement; ordinary successful allocation
fixtures do not establish absence. Earlier lane language saying contention cannot fail is too strong.
The successor does not yet model that environment input. W03 remains open for this reason.
