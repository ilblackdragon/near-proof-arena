# PQ tail architecture experiment

> **Status (2026-10-31): unproven research direction.** Not a qualified NEAR chunk proof,
> not a PQ128 claim, not linked to the Lean statement, and no accumulation/folding yet.
> The headline 250 KB packets likely model below 128 bits. Merged to `main` only to preserve
> the work. Read [EVALUATION-2026-10-31.md](EVALUATION-2026-10-31.md) before relying on any number here.

Branch `lane/pq-tail-architecture`, base `8ac3de9f6`. Target: a recursively composable,
post-quantum proof below **300,000 bytes**, with the final proof ready **within 1–2 seconds of the chunk**
(user clarification), as well as sustained throughput matching chunk arrival. Neither recursion nor PQ security is
established by the current diagnostic packet.

See [current agent handoff](ACCOUNT_LEDGER_HANDOFF.md) for the accepted forged-balance
counterexample, ordered account model, scratch paths and next circuit work.

## Current decision

[Combined source lists](MULTI_LISTS.md) now prove all three lists of two original
fixtures: 814 receipts / 3.011 s and 711 receipts / 2.792 s warm, each 247,786 B
(or 248,012 B including all source paths). Claim-derived source order/context
and complete outcome roots pass host checks; fresh proof verification passes.
Authenticated account state and ordered writes, full runtime, composed PQ/history
and the 1–2 s deadline remain open. Earlier single-list results follow.

[Packed source/outcome lists](PACKED_RECEIPT_LISTS.md): an original **804-receipt
list proves in 244,838 B / 4.543 s warm**, and its packet verifies freshly in
1.549 s. Exact packed concatenation lets the 1,024-slot profile construct within
16 GiB. It fits size but misses the deadline; source inclusion, state/runtime
and bounded PQ history remain open. A [source-byte budget experiment](SOURCE_BYTE_BUDGET.md) remains log23 and
takes 4.20–4.35 s; it does not solve the deadline. [Bitmask selection](SELECTION_AND_PARALLEL.md) increased circuit size and was
rejected. Four-core execution of the existing relation gives 244,814 B /
3.72–3.77 s; fresh single-core verification passes. [Parallel commitment](PARALLEL_COMMIT.md) now gives 244,814 B / 3.13–3.30 s
on four cores; exact parity and older-verifier checks pass. [Backend profiling](LABRADOR_PHASES.md) attributes the remaining cost to initial
constraint lifting, commitment, projection and amortization. [Parallel pair products](PARALLEL_PAIRS.md) now cut the initial kernel from
153–156 ms to 44–57 ms, with 244,814 B / 3.15–3.34 s warm readiness.
[Parallel JL collapse](PARALLEL_JL.md) now lowers three initial JL lifts from
151 ms to 48–57 ms, giving 244,814 B / 3.00–3.11 s warm.
Next investigate lifting aggregation; source inclusion/state/runtime
and PQ history still remain.

The earlier [receipt-only batch](RECEIPT_BATCH.md) measured 215,398 B / 1.52–1.54 s
for 814 receipts, but omitted incoming source-list work. Do not substitute that
narrower timing for the new integrated relation or full NEAR.

[Metadata guard correction](STRICT_METADATA.md) remains mandatory; earlier
MSB-only range guards were underconstrained. Composed PQ security, untrusted
codec safety, representative positive-gas claims and full deadline remain open.

[Outer security evidence](OUTER_SECURITY.md) and the
[execution-frontier hypothesis](EVENT_PROTOCOL.md#further-hypothesis-finalize-the-execution-frontier)
retain the wider protocol and completeness obligations.

[Source membership audit](SOURCE_MEMBERSHIP.md) now matches 268 lists to
claim-derived roots across 64 original cases. The large proof plus a two-step
public path is 244,900 B. Native claim derivation remains trusted; complete
source execution/order, state/runtime and PQ/history remain open.

## Event protocol research

[Design and falsifiable experiments](EVENT_PROTOCOL.md): current Jolt/Akita prior
art, event-derived trace openings, complete constraint coverage and reusable hash
templates. Algebra prototype passes 3,120 identity checks; authentication and
recursive composition are open. [Jolt reproduction](JOLT_SCREEN.md) now verifies
a decoded 97,998 B proof; scale 20 is 99,490 B / 7.46 s prover for just 277 hashes.
[Reusable hash template](HASH_CAPACITY.md) proves 2,460-message and 12-message
actual batches with one circuit/setup: **1.67–1.74 s warm**, ~116 KB analytical,
four honest proofs / 24 mutants / 44 gadget checks. Construction/setup adds
12.84 s cold; receipt binding, wire codec, PQ audit and recursion remain open.
[Actual export](EXPORT_CODEC.md) is now **165,950 B** including public root and
framing. Both honest exports decode and verify in fresh processes (~0.65 s),
against independently computed roots, with byte-identical backend re-encoding.
Export-inclusive warm readiness is **1.67/1.73 s** for the two tested layouts.
Decoder safety for arbitrary metadata remains open; it is a local research API.

## Binary/lattice candidate

[LaBinius screen](LABINIUS_SCREEN.md): private 64 KiB SHA-256 message (1,025
compressions) proved in **194 ms**, verified in **97 ms**, with **97,745 B
analytical proof size** on one CPU core. Three honest proofs and nine negative
checks passed. This is a component result with opaque C proof objects; canonical
serialization, concrete PQ128 analysis, actual NEAR hash-bus binding and whole
chunk recursion remain open. It changes assumptions from the SHA384-only baseline.

## Latest live screen

The newer declared-profile packet derives its key locally from trusted AIR,
expected claim and a four-byte width selector. Independently rebuilt/replayed
three original-witness cases: **258,792 / 274,763 / 279,454 B**; no supplied key,
prover/verifier key hashes agree, all nine width mutations rejected. Thus a
3 MB key sidecar is not inherently required.

Proof-ready wall times were **17.26 / 20.10 / 20.86 s** on a loaded host.
Native CPU compilation accelerates the build relative to generic settings,
but concurrent aggregation prevents a clean performance comparison.
The largest honest D0a witness tested creates **156,624,112 cells** and passes
constraint/bus precheck, then fails the fixed profile's 65,536-row capacity.
No proof exists for that case in this screen. **None meets the 2 s deadline.**
Evidence: `evidence/live-native/audit.json`; runner: `audit_live.py`.

The next architectural bottleneck is the work representation: receipt and
receipt-SHA tables account for 140,247,040 cells (89.5%) in that large case.
Study direct byte/word constraints and specialized hash proving, coupled with
a GPU commitment/opening path. Do not merely enlarge the profile and call
small-fixture timing representative of NEAR. Existing Binius component trials
in `results/swirl-security-review` use diagnostic security settings and are
not a complete replacement; keep the terminal compression/security gates.

## Compact-representation experiment

[Virtual trace experiment](VIRTUAL_TRACE.md): exact interval receipt evaluation
reduces storage 276 MB → 23.5 MB and local-constraint evaluation sites 236M → 33M.
All 900 original local constraints retained; three mutations rejected. Opening
authentication, bus binding, kernel equivalence and composed proof remain open.
This is a candidate architecture, not a new sub-300 KB proof result.

## Start from the authenticated endpoint

The existing `pq-realtime-hypothesis` experiment is substantially beyond its 21 KB
GKR endpoint. Its single-pass prover combines frontend/stacking checks, the GKR
endpoint, and a shared opening authentication into one packet. Reuse this as the
baseline before inventing a replacement. The standalone GKR endpoint leaves an
input-oracle obligation; the complete packet attempts to discharge it through the
shared opening. Component size alone is not proof size.

Historical packet layout (bytes):

| Component | Bytes |
|---|---:|
| Hint + column root | 58 |
| Frontend | 32,192 |
| Stacking | 2,320 |
| Endpoint | 21,216 |
| Shared sumcheck | 2,208 |
| WHIR opening | 200,758 |
| Framing | 36 |
| Total | 258,788 |

The opening is 78% of the packet. Improving endpoint serialization alone has
limited value. The historical prepared-trace prover recorded 10.64 seconds;
this excludes witness execution and trace generation. Rebuilt measurements: **29.82 s median prover process / 0.864 s median
verifier process**, three identical 258,788-byte packets; all ten external
mutation cases rejected. See `evidence/replay/audit.json`. This build does not
reproduce the historical latency; source/dependency/build differences need
isolation before attributing the gap. The generated key is **3,045,746 bytes**
of JSON, excluded from the packet: cross-chunk reuse is a critical size gate.

## Experiments in priority order

1. **Reproduce the complete packet.** Rebuild source, prove three times, verify
   in separate processes with the existing key and expected claim, and mutate
   every section plus framing. Pin inputs and binaries. `audit_packet.py` runs
   this audit. These checks establish reproducibility/binding examples, not
   soundness. Preserve negative-test stderr when diagnosing unexpected exits.
2. **Freeze the statement and setup.** Inventory every verifier input: expected
   claim, AIR, key, parameters, public tape helper. Determine which key fields
   depend on trace shape or witness. Exercise different chunks with an agreed
   reusable key policy; count any per-proof setup against 300,000 bytes. Do not
   accept a prover-selected key as an authenticated statement.
3. **Measure the missing work.** Run from original witness through execution,
   trace generation, terminal proof, and independent verification. Start with
   D0a, then representative table/trace sizes; D3 requires the missing AIR work.
   Record throughput, p50/p95 latency, peak memory, packet bytes and machine.
   Set the real-time threshold from actual chunk arrival and hardware budgets.
4. **Specify committed accumulation.** Keep an authenticated accumulator of
   algebraic obligations, rather than recursively proving the whole generic
   verifier at each step. Define the accumulator invariant, initialization,
   update and terminal discharge before implementing it. Bind prior state,
   chunk identity, public claims, circuit identity and transcript domains.
   Test 1/2/4/8 updates: terminal size must not grow linearly with history,
   and historical witness replay must not be required to verify. The current
   single-chunk endpoint is not already such an accumulator.
5. **Attack the dominant opening.** Compare one shared opening over accumulated
   obligations against a binary-field commitment or lattice folding terminal
   compressor on the same committed-input workload. Include conversion and
   finalization costs, security parameters and assumptions. No toy gate-count
   or unauthenticated-oracle win qualifies.

## Candidate methods and decision gates

- [Symphony](https://eprint.iacr.org/2025/1905): investigate a folding compiler
  avoiding Fiat–Shamir hash circuits in the recursively proved computation.
  Need compatible commitments, accumulation invariant and concrete QROM bound.
- [Neo/SuperNeo](https://eprint.iacr.org/2026/242): investigate small-field,
  Module-SIS folding. This changes assumptions and introduces lattice parameter
  accounting; do not silently substitute it into a SHA384-only security claim.
- [LaBinius](https://eprint.iacr.org/2026/2103): investigate binary-field PCS plus
  LaBRADOR as a terminal compression candidate. Its published size/performance
  results are not measurements of this NEAR relation or recursive composition.

Select on **full terminal packet + full prover cost + defensible composed
security**, not smallest component. First architectural bet: share authenticated
algebraic work and compress only at the boundary. Reserve a new PCS for evidence
that the remaining opening is the bottleneck after that change.

## Security gates

The diagnostic profile uses SHA384 truncated to 42 bytes, extension degree 12,
a numeric target of 268, and zero query/folding/mu grinding. This differs from
the approved U10 grinding profile. A numeric target is not a concrete PQ proof.
Required: interactive soundness, commitment binding, transcript ordering and
cross-protocol domain separation, adaptive batching, Fiat–Shamir/QROM losses,
recursion composition and all hash bridges. Keep `security_established=false`.
Zero knowledge is also unestablished. Signed arena challenges are unchanged.

## Reproduction and limits

```
python3 research/near-compression/tail-architecture/audit_packet.py \
  --manifest research/near-compression/tail-architecture/evidence/rebuilt-manifest.json \
  --output /tmp/pq-tail-audit --repeats 3
```

Manifests contain machine-local paths. The historical binaries were missing, so
an isolated source snapshot was rebuilt offline in
`/data/illia/pq-tail-architecture-20261023`; see build/source provenance. External
path dependencies remain shared, and some lack Git history: this is an audit
checkpoint, not a hermetic distributable build. Original historical evidence
is retained separately. Generated packets and ~3 MB key sidecars stay local;
reports pin their sizes/hashes. Rejection via Rust assertions is accepted as
research behavior, not production parser hardening.
