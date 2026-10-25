# Research direction: authenticate events, derive the trace

2026-10-24. Hypothesis, not a new sound protocol or a novelty claim. Target:
PQ recursive NEAR proof <300,000 bytes and finalization <=2 seconds after
chunk availability. Full chunk correctness and history binding remain required.

## What the prior art teaches

My reconstruction of the design reasoning (not the authors' private history):

1. Count expensive authenticated data, not abstract constraints. A representation
   that is cheap to evaluate can still be costly to commit and open.
2. Use structure: addresses, small symbols, increments and fixed tables contain
   much less information than their expanded polynomial representations.
3. Co-design the relation and commitment. Moving work out of commitments only
   helps if the new opening reduction is cheaper and remains sound.
4. Price the whole protocol, including setup, security parameters and recursion.

[Twist/Shout](https://eprint.iacr.org/2025/105) already exploits one-hot addressing
and increments. Current [Jolt](https://github.com/a16z/jolt/tree/7931b223ddefe3cfa35671d0fa8321df4578ff96)
has a first-class lattice Akita path, native batching and serialized proofs.
Its historical `specs/akita-optimal-committed-data.md` explicitly proposes
committed symbols instead of expanded one-hot objects. That idea is prior art,
not our invention. Jolt reports 1.42 s for 2^20 sha2-chain rows on M4 Max in
`specs/akita-pr-1732-benchmarks.md`; a DIFFERENT, older run reports 89,173 bytes
and 4.385 s in `specs/akita-native-trace-batching-performance.md`. Neither is
our NEAR end-to-end result. SDK recursion aliases currently select Dory;
the existence of a recursion example does not establish Akita IVC.

## Proposed additional step

Compile NEAR's semantic execution events directly into authenticated obligations,
without first committing a dense AIR trace. Treat the trace as a deterministic
virtual view. Receipt parsing, memory changes and SHA block transitions have
different structure; share their authenticated boundary data rather than forcing
all three into one generic instruction trace.

The measured receipt table has 68.94M cells but 1.96M nonzero constant intervals.
This motivates the direction, but interval count is still large and compression
alone does not make proving cheap. Most measured intervals are singletons.

For one column defined by change events (s_i, delta_i), with height T=2^n:

    f[t] = sum_i delta_i * [s_i <= t]
    f~(r) = sum_i delta_i * (1 - F_r(s_i))
    F_r(s) = sum_{0 <= t < s} eq(r,t)

F_r(s) can be computed with a binary comparison recurrence in O(n), without
materializing T equality weights. `event_opening.py` independently checks this
against dense multilinear evaluation, including Boolean challenges and boundary
positions. It is only an algebra prototype. Sparse sums, prefix transforms and
digit recurrences are established techniques, not claimed inventions.

The research question is whether an authenticated opening reduction and a NEAR
constraint compiler can preserve this event complexity across the WHOLE proof.
An interval variant replaces (1-F(s)) by F(end)-F(start). Choose the cheaper
representation per column; do not assume change events always beat intervals.

## Candidate protocol and its missing arguments

1. Fix public relation ID, capacities, state roots, chunk ID and predecessor
   accumulator. Commit event records, active lengths and boundary witnesses
   BEFORE deriving opening/batching challenges. Setup must depend on a public
   capacity class, not the witness's exact message lengths or positions.
2. Prove canonical encoding: bounded positions, ordered/unique change locations
   where required, correct deltas, active masks and zero padding. Hash blocks
   use fixed templates with constrained length/padding and chaining state.
3. Prove every local constraint on a complete partition induced by the events
   of its input columns AND shifted columns. Proving selected boundaries is
   insufficient: prove sorted-union completeness or use a reduction that covers
   the full row domain. Boundary selectors must also be included. Nonlocal buses
   need separate authenticated multiset/memory arguments.
4. Reduce virtual trace openings to the committed event records using the prefix
   recurrence. A candidate sumcheck relation has to authenticate position bits,
   delta values and recurrence evaluations. Intermediate recurrence witnesses,
   degree, Booleanity and sorting can erase the savings; measure all of them.
5. Bind receipt bytes, hash requests/responses, state updates and execution
   effects through common committed boundary records. A public hash-batch root
   alone is not this bridge. Cross-field conversion needs explicit range and
   equality proofs; do not add an unchecked random linear combination.
6. Accumulate these obligations with a compatible lattice folding protocol.
   Define initialization, update invariant and terminal discharge. Preserve
   predecessor linkage and reject omissions/reordering. A bare sum of residuals
   is not a recursive proof. Terminal verification must not replay history.

[SuperNeo](https://eprint.iacr.org/2026/242) and
[Symphony](https://eprint.iacr.org/2025/1905) inform step 6; their composition
with this relation and Akita is NOT established. Check field/ring compatibility,
norm bounds, adaptive challenges, extraction and QROM composition first.

## Why this could affect the deadline

Reusable capacity templates remove witness-dependent circuit/setup from the
critical path. Independent event segments can be processed while execution
progresses, then bound to the finalized chunk. However, post-commitment challenges
still require later work: do not claim all openings can be precomputed. Measure
both full latency starting from an already available chunk and online tail
latency when data was available earlier. Publish the arrival assumption.

Our actual 2,460-message SHA component has warm witness+prove median ~1.084 s,
but first proof ~10.143 s plus ~0.261 s export, analytical rather than serialized
proof size, and no receipt binding. It demonstrates why eliminating shape setup
matters; it does not meet the end-to-end target. Jolt reproduction is in progress.

## Experiments and stop conditions

1. Reproduce current Jolt/Akita with real wire sizes and separate setup/prove/
   verify; use this as the implementation baseline before inventing a PCS.
2. Prototype event-opening authentication on one receipt column, including
   position checks. Compare full commit+reduce+open against dense Akita, at equal
   security. Stop if added recurrence/sorting work eliminates the benefit.
3. Add one actual receipt constraint with complete partition coverage; attack
   omitted events, gaps, shifted boundaries and duplicate IDs. Then add the
   receipt/hash bridge using the existing exported messages checked against the
   original SHA byte/digest buses. No extrapolation from the algebra evaluator.
4. Replace exact hash layouts with reusable capacity templates; measure the
   masking/range/length overhead and cold/warm latency across different chunks.
5. Demonstrate 1/2/4/8 history steps with constant terminal size and no historical
   witness replay, including predecessor/claim mutations. Audit concrete PQ
   security and count all bytes needed by an independent verifier.

Success requires representative NEAR workloads, actual serialized packets,
all preparation and bridges, p95 timing on named hardware, and bounded queues.
If event authentication loses, retain Jolt/Akita as the fallback. No GPU latency
prediction or state-of-the-art claim follows from these algebra tests.

## Further hypothesis: finalize the execution frontier

The next architectural step is to exploit *when* obligations become final, as
well as their sparse representation. This is a research hypothesis, not a claim
of novelty: streaming proofs, authenticated dataflow and folding are prior art.

Partition execution into segments with typed interfaces: input/output state
commitments, receipt identities, memory dependencies and hash requests/results.
Each segment proves its local semantics and binds its interface. Maintain an
accumulator whose invariant covers every completed segment plus a committed set
of outstanding dependencies. On insertion, consume matching dependencies exactly
once and add new ones. Chunk closure binds the final state and receipt commitment,
checks the prescribed completed-segment set and discharges allowed outstanding
cross-chunk messages under NEAR's actual semantics. An empty set alone cannot
prove completeness: an attacker could omit both ends of an interaction.

The proposed gain is an authenticated frontier: closed internal dependencies no
longer expand the finalization relation. The accumulator still binds them, and
soundness must prevent a prover from deleting obligations or substituting another
history. Receipts destined for later chunks must be carried explicitly, not
incorrectly required to vanish. No history replay is allowed at verification.

Timing must separate three regimes:

| Regime | Work available before chunk closes | Required measurement |
|---|---|---|
| Cold verifier/prover start | None | Setup and full processing latency |
| Chunk arrives as a complete object | Reusable setup only | Full execution-to-proof latency |
| Online producer | Finalized segments of this chunk | Tail latency AND sustained throughput |

Online processing helps only if segments become irrevocable early enough and
there is spare proving capacity. Post-commitment challenges create genuine later
work. No changing the clock origin to hide hashing, execution, or queue growth.

A falsifiable first experiment is a two-segment receipt/hash relation. Prove
local processing against a common authenticated interface; join using exact
request identity, byte length and digest; bind the result to an independently
computed chunk claim. Test omission of both producer and consumer, duplicates,
reordering where order matters, wrong predecessor, and cross-chunk replay. Then
scale to 1/2/4/8 accumulated segments and record total work, post-close work,
packet bytes and queue depth. Compare against the same monolithic relation at
identical security. Reject the design if interface proofs or accumulator updates
consume the savings. A complete compatible PQ accumulator remains unimplemented.

The [security screen](SECURITY_SCREEN.md) prevents using the current 1.7-second
hash result as the secure endpoint in that comparison. First qualify and measure
a replacement parameter policy; then test the frontier hypothesis. This ordering
keeps a representation improvement from being mistaken for a security reduction.
