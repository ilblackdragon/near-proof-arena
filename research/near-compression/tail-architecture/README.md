# PQ tail architecture experiment

Branch `lane/pq-tail-architecture`, base `8ac3de9f6`. Target: a recursively composable,
post-quantum proof below **300,000 bytes**, with the final proof ready **within 1–2 seconds of the chunk**
(user clarification), as well as sustained throughput matching chunk arrival. Neither recursion nor PQ security is
established by the current diagnostic packet.

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
