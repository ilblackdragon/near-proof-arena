import NearSpecV3.ChallengeChunkV3
import NearSpecV3.ChunkValidationD2

/-!
# `NearSpecV3.ChallengeChunkV3Gas` — a prover-independent gas bound (L1 groundwork)

Plan §4 L1 asks for an additive successor relation whose limits come from **protocol behaviour**, not
from one prover's table height. The current D3α relation caps chunk function-call gas at

  `gAlpha = 2 ^ 22 * 822756 = 3_450_888_781_824`  (≈3.45 Tgas)

where `2^22` is *one np-udr-stark proof's maximum table height* and `822756` is the cheapest Wasm
operator's gas. That number is therefore a statement about the prover, not about NEAR: the protocol's
own per-chunk bound is `max_gas_burnt = 1_000_000_000_000_000` (1 Pgas, PV86 runtime config), which is
**289.8× larger**.

**This module does not change `RelD3`.** The signed `near-chunk-v3` challenge (and its draft
generator, `spec/tools/build_challenge_draft_v3_chunk.py:104`) pins `G_α` as a checked condition
`e.g_alpha`, and `make pin-check` verifies those hashes. Editing `gAlpha` would silently change the
statement a candidate is admitted against. So the successor relation is defined *alongside* the
existing one.

## What is established here, and what is not

Established: the protocol bound is defined from the pinned runtime config; the successor relation
(`checkD3Proto`) is the same checker with that bound in place of `gAlpha`; and the cap values differ by
a decided constant.

**Not established, and deliberately not claimed:** that `RelD3Proto` admits strictly more *chunks*
than `RelD3`. The two relations differ only in the cap value, so their difference as relations is the
set of chunks whose function-call gas falls in the band. Whether that set is non-empty is a question
about real chunk data, not about the caps — and no such chunk is exhibited here. An earlier draft of
this module asserted the strict widening as a theorem; that assertion was not provable from the caps
alone and was removed rather than left as a `sorry`.

Also not established: that `RelD3Proto` is *correct* against nearcore. Widening the cap admits chunks
whose Wasm execution the spec models but which no single proof can carry; whether the spec's execution
of those chunks agrees with nearcore is the differential obligation L2–L7 owe. Nor is it established
that 1 Pgas is reachable end-to-end by any proof system — that is a prover-lane question, and the plan
deliberately separates it from the semantics.
-/

namespace NearSpecV3

open NearSpec

/-! ## The protocol bound -/

/-- Per-chunk burnt gas limit from the pinned PV86 runtime config
(`max_gas_burnt = 1_000_000_000_000_000`, `runtime_configs/74.yaml`; inventory
`docs/research/near-wasm-boundary-inventory.json` → `parameters.max_gas_burnt`).

This is the protocol's own bound on a chunk's *total* burnt gas. It is not the same quantity as
`gAlpha`, which sums only `gas_burnt_for_function_call` (Wasm execution incl. host gas). The
function-call subset is at most the total, so bounding the subset by this value is conservative in the
permissive direction: it cannot reject a protocol-valid chunk. That direction is the one that matters
for a successor whose job is to stop excluding valid chunks. -/
def maxGasBurnt : Nat := 1_000_000_000_000_000

/-- The successor relation: the D3 checker with the protocol's gas bound in place of the
proof-capacity-derived `gAlpha`. Every other condition is `checkD3` unchanged. -/
def checkD3Proto (claimBytes witnessBytes : Bytes) : Except String Unit :=
  checkD2Core (D3.d3Hooks Wasm.pv86) true claimBytes witnessBytes (some maxGasBurnt)

def RelD3Proto (claimBytes witnessBytes : Bytes) : Prop := checkD3Proto claimBytes witnessBytes = .ok ()

/-! ## The caps are different, and the protocol's is the larger one -/

/-- `G_α` is below the protocol's own per-chunk gas limit. Decided from the two literals, so it fails
to compile if either constant changes without review. -/
theorem gAlpha_lt_maxGasBurnt : D3.gAlpha < maxGasBurnt := by decide

/-- The two relations agree except on the gas condition, so a gas value inside
`(gAlpha, maxGasBurnt]` is the only possible source of disagreement. Stated on the cap values: this is
what *is* known, and it does not by itself exhibit a chunk. -/
theorem caps_differ : D3.gAlpha ≠ maxGasBurnt := by decide

end NearSpecV3
