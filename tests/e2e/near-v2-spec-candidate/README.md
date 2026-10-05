# near-v2-spec-candidate (TEST ONLY, DEMO tier)

A minimal `near-arena-claim-v2` candidate used only by
`runners/worker/tests/near_v2.rs` to drive the v2 draft challenge
(`challenges/drafts/near-transfer-receipt-v2.draft.json`) through the real
worker pipeline (validate, build, conformance, adversarial, benchmark) with
the governed `near-arena-oracle --scope v2`, the v2 generator specs and the
pinned v2 public fixtures.

It is **not** a submission and carries no formal certificate: `prove` and
`verify` shell out to `nearspec-check --scope v2` (the compiled Lean reference
semantics, `spec/lean/Main.lean`), which the test copies into `bin/` from a
local `lake build nearspec-check`. `prove` derives the claim from the request
and witness; the proof is `"NSV2" ‖ u32 len(request) ‖ request ‖ witness`;
`verify` accepts iff `nearspec-check` reports `ok` (derived claim equals the
claim bytes and `decide (TransferV2.NearRelation c w)` holds). The proof
reveals the witness: this is a re-execution test harness, not a succinct or
private proof.
