# demo-toy-arithmetic — DEMO TIER, NOT NEAR SEMANTICS

> **This challenge does not concern NEAR.** It is a plumbing fixture so the
> arena pipeline can be exercised end to end before the spec lane publishes
> the real NEAR state-transition slice. A result under this challenge says
> nothing about nearcore, NEAR protocol semantics, or any chain. The
> `nearcore` / `protocol_version` fields of the challenge are carried only
> because the `ChallengeDefinition` contract requires them.

## Relation

`ToyRelation(claim, ()) :⇔ claim.c = claim.a * claim.b mod 2^64`
(Lean: `Arena.Demo.ToyArithmetic.ToyRelation` in `lean/ToyArithmetic.lean`).

## Encoding (`claim_encoding.format = "demo-toy-arith-v1"`)

All integers are unsigned 64-bit little-endian.

| file          | layout          | size |
|---------------|-----------------|------|
| `request.bin` | `a ‖ b`         | 16 B |
| `witness.bin` | empty           | 0 B  |
| `claim.bin`   | `a ‖ b ‖ c`     | 24 B |

`expected_claim(request) = a ‖ b ‖ (a·b mod 2^64)`. The judge computes this
itself; a candidate claim that differs is `CLAIM_MISMATCH`.

## Workloads

* `toy-small`: `a, b` uniform in `[0, 2^32)` (generator `generators/small.json`).
* `toy-large`: `a, b` uniform in `[0, 2^64)` (generator `generators/large.json`).

Seeds are drawn by the judge after the challenge is frozen. Public fixtures:
`fixtures/`. There is no held-out set for this demo; the commitment field is
the explicit all-zero placeholder.

## What is NOT established

Everything about NEAR. Also: no cryptographic soundness is required (no
FORMAL_* obligations are required in demo tier), so the "proof" may be the
claim itself.
