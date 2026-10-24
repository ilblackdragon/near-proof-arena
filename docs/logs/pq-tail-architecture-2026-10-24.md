# PQ tail architecture — 2026-10-24

Worktree `pq-tail-architecture`; goal still open: PQ recursive NEAR proof below
300,000 bytes, ready within 1–2 seconds of chunk. No main changes.

- [Event protocol](../../research/near-compression/tail-architecture/EVENT_PROTOCOL.md):
  prior-art-derived hypothesis; 3,120 algebra identities checked, no PCS claim.
- [Jolt screen](../../research/near-compression/tail-architecture/JOLT_SCREEN.md):
  current Akita path found and audited at source level. Benchmark workloads and
  security revisions differ from historical reports. Fat/thin LTO exceeded the
  16 GiB bound; CI-profile build proceeds with separate prover/CLI invocations.
- [Hash capacity](../../research/near-compression/tail-architecture/HASH_CAPACITY.md):
  all 64 D0a cases exported, no export failures. Largest receipt workload remains
  2,460 messages/5,875 blocks. Fixed bucket policy nominally 7,296 blocks; existing
  variable-length gadget's storage rounding would actually produce 10,384.
  Tighten with enforced bounds or measure that overhead explicitly.
- Actual hash-batch evidence/source is preserved under
  `research/near-compression/tail-architecture/evidence/actual-hash-batch`.
  Warm witness+prove median ~1.084 s; first proof ~10.143 s plus export ~0.261 s.
  Analytical size only, exact-layout setup, no receipt/hash bridge or recursion.

Follow-up: current Jolt independently measured 97,998/99,490 serialized bytes at
scale 18/20, 1.99/7.46 s proving. Decoded-object verification and one wire mutation
passed on a patched scale-18 rerun (2.32 s full process). Reusable hash template
now proves both large and small actual layouts without rebuilding: four proofs
ready in 1.67–1.74 s warm; 24 mutants reject; tighter-length gadget passes 44
checks. Cold construction/setup adds 12.84 s. Evidence and source linked above.

Next: canonical LaBinius wire codec and authenticated receipt/hash connection;
measure complete capacity-class pipeline. Keep full NEAR semantics, composed PQ
security and recursive history linkage as completion gates. Current CPU Jolt
whole-VM path is too slow even for a small hash workload; preserve it as a baseline.

Export follow-up: complete hash-component exports are 165,950 bytes each, versus
~116 KB analytical. Fixed-width terminal coefficients suffice without entropy
coding. Independent structural reader consumes all fields and rejects six
malformed-framing cases. Native decoding and verification from bytes remain
unimplemented; do not promote the export to a verified proof claim. See
[codec evidence/gates](../../research/near-compression/tail-architecture/EXPORT_CODEC.md).

Decode follow-up: both 165,950-byte exports now verify in separate fresh processes
without witnesses, against Python-derived expected roots. Backend re-encoding is
byte-identical; wrong root/tape mutations reject (four checks). Decode ~0.06 ms,
verify ~0.65 s after cold setup. New packet-ready timing includes export/write:
1.672/1.728 s, and emitted packets match the independently verified ones exactly.
Decoder remains explicitly unsafe for untrusted metadata/RNS; arbitrary-input
hardening and statement-dependent dimensional checks are not established.
The first decode rejected legitimate tail kappa1=0; fixed the format check only.
Sources/logs: `evidence/import-codec` under the lane research directory.
Prioritize concrete PQ feasibility (16-byte C transcript/SHAKE128/AES128/lattice
sizing) before treating this as a full-system integration choice.

Security follow-up: parsed the exported backend's actual parameters and legacy
verifier bounds. Greyhound-reference scalar Euclidean SIS model estimates
92.485–117.925 quantum bits for all ten obligations; all pass the old gate.
Five regression checks and ten C/Python crosschecks pass. This rejects the
measured configuration as evidence of PQ128, not a demonstrated attack. Initial
commitment, outer PCS, structured attacks and QROM remain outside this screen.
Pinned sources/results: [security screen](../../research/near-compression/tail-architecture/SECURITY_SCREEN.md).
Next: justified bounds/parameter policy, regenerate real proofs, then test a
complete two-segment authenticated receipt/hash join. EVENT_PROTOCOL now defines
an execution-frontier hypothesis, completeness attacks and explicit cold/full/
online timing regimes. No recursion or novelty claim.

Backend policy experiment: revised source/target collision bounds and scalar
quantum-128 rank checks ported into isolated backend. Prediction-only selection
failed honestly at 127.995 bits; added 2x target-norm selection headroom with
unchanged actual-bound verification. All 44 final obligations screen >=140.45
bits (C/Python agree). Eight backend reductions shrink terminal witness; these
are not history recursion.

Fresh decoding initially exposed quadratic-check failures. Export assertions
found noncanonical top-limb carry lost by 48-bit packing. Canonicalization before
all transcript/wire packing fixes it; 704 residue boundary checks pass (legacy
fails 512). Both regenerated 150,526 B packets independently verify in fresh
processes against external roots; four root/tape mutations reject. Final measured
warm readiness 1.707/1.724 s; previous run 1.80/2.03 s, so no p95 margin claim.
Outer PCS, transcript/QROM and full NEAR/history remain open. Patches, failures,
final logs and manifest: [policy experiment](../../research/near-compression/tail-architecture/SIS_POLICY_EXPERIMENT.md).

Outer security follow-up: source-derived setup census found legacy Y/u/R bridge
ranks and three-limb ring-648 commitment unchanged by the backend port. Conditional
scalar screen distinguishes 2x direct collision from extraction factors; main
three/four/five-limb estimates under notebook factor are 79.235/125.61/176.49 bits.
Author's benchmark description explicitly targets 100-bit security. Saved notebook
outputs archived as not rerun. A single signed short challenge has support at most
2^103.997; this is not the full protocol's soundness or a demonstrated forgery.

Implemented five limbs and model-selected bridge ranks 15/5/11. First honest proof
failed static no-wrap bound (145.209e12 > 140.737e12). Verifier now uses announced,
transcript-bound, statement-enforced nonbinary norm bounds; binary caps unchanged.
No guard removed. Same packet subsequently verifies, including in fresh process.
Two final packets: 158,654 B, readiness 2.1657/2.1275 s; cold setup ~13.02 s extra.
Twelve in-process and four fresh root/tape mutations reject. All 44 backend model
crosschecks pass (minimum 144.69 bits). Source/patches, failures, final logs and
manifest: [outer screen](../../research/near-compression/tail-architecture/OUTER_SECURITY.md).
Component misses 2 s and full PQ/NEAR/history obligations remain. Do not extrapolate
GPU speed or count two observations as p95.

Public event experiment: removed in-circuit SHA512 record-root calculation;
exposed metadata/digests as public outputs and checks the same expected root
natively. Dense wire 305,510 B failed size. Canonical active-record encoding
reconstructs the identical dense vector: 258,134/157,766 B, fresh verification and
independent source-record matching pass. Twelve codec checks and 24 mutation
checks in four repeated proofs pass. Backend model floor unchanged (minimum
143.895 bits in the two packets), not composed security.

Timings: dense 1.974/1.895 s; first compact 2.904/2.574 s; repeats
2.033/1.965/2.002/2.002 s. File timestamps disprove own compilation as the cause of
slow compact proving (build began ten seconds after completion); build did overlap
fresh verification. Preserve all runs, no deadline or p95 claim.

Independent D0a outcome-tree reconstruction matches every internal preimage/ID/
digest in all 64 cases. Largest has 813 internal nodes derived entirely from 814
public leaf digests; odd nodes promoted unchanged. Candidate non-Merkle policy
fits corpus at 5,248 SHA blocks vs 7,296. Next implement native authenticated tree
composition, not just host audit. Full chunk claim and byte-bus links still open.
Evidence: [public events](../../research/near-compression/tail-architecture/PUBLIC_EVENTS.md).

## Native outcome-tree composition

Implemented removal of internal Merkle jobs from the private hash circuit; native
verifier derives their exact records and checks the original full job root.
225,985/158,950 B; alternating warm 1.517/1.483/1.506/1.494 s, fresh verification
0.664/0.656 s. 69 independent fixtures, 208 tree mutations, 24 proof mutations pass.
Backend scalar minimum 144.955 modeled bits; new main-ring geometry needs a new
outer analysis. No full NEAR/PQ/history or p95 claim. Leaf-link census supports
next reduction to 3,232 SHA blocks, not yet implemented.
[Reproduction and limitations](../../research/near-compression/tail-architecture/NATIVE_OUTCOME_TREE.md).

## Native receipt leaves

Implemented receipt-ID + proven-PEO reconstruction of leaves, then native tree.
Same complete original job root; exact PEO/receipt association enforced.
Large 833 private hashes, 814 native leaves, 813 native nodes; 266,607 B.
Small 206,889 B. Warm 0.844/0.829/0.863/0.842 s; fresh byte verification passes.
69 independent fixtures/450 mutations; 24 proof mutations; 26 backend scalar
checks pass (minimum modeled 140.185 bits, not composed PQ security). Witness
log 20/column log 9 changes geometry and grows backend despite faster proving.
Execution, byte-bus, chunk and PQ history links remain required.
[Evidence](../../research/near-compression/tail-architecture/NATIVE_RECEIPT_LEAVES.md).

## Original-claim outcome linkage

Verifier now requires caller's original claim and compares its outcome root to
the authenticated PEO/receipt tree. Same packet and job root; fresh verification
passes (~0.387 s). Independent 64-case field/root audit; 304 mutations reject,
integrated cross-claim substitution rejects. Explicit scope test: all 64 altered
state roots still pass this outcome-only predicate. Prefix extraction is not
full claim decoding/validation. Next prove execution-emitted RC/PEO/RID bytes
equal the private hash inputs, plus state/history and composed security.
[Evidence](../../research/near-compression/tail-architecture/CLAIM_OUTCOME_BINDING.md).

## Metadata guard correction and receipt producer audit

Found `assert_false` (MSB-only) misused for active/flag/id range and inactive-field
zero checks. Length 11 + flag 3 aliases public length 10 + flag 1. Four malformed
local witnesses pass old guards/reject strict guards; replaced six predicates
with `assert_zero`. Earlier metadata-relation claims superseded. New NPSTRICT
packets remain 266,607/206,889 B; warm 0.864/0.834/0.877/0.836 s, fresh claim/job
root verification ~0.388 s. Backend scalar min 139.92 modeled bits, not PQ proof.
Independent receipt oracle matches 4,602 jobs/540,197 bytes in 64 cases; 384
mutations reject. All 2,138 receipts have zero block gas price/no token burn;
positive-gas coverage currently synthetic (7 valid/6 invalid arithmetic cases).
Execution/hash-byte binding, state/history and full security remain required.
[Evidence](../../research/near-compression/tail-architecture/STRICT_METADATA.md).

## Receipt arithmetic circuit

Implemented unsigned 128-bit credit/storage/burn/refund constraints. Initial
IntMul implementation was rejected by LaBinius (no IntMul IOP oracle); switched
constant products to checked shift/add. Independent 2,910-case oracle: 2,699
accept/211 reject; 18,893 changed output/system flags reject, including positive
gas branches. Actual isolated witness log is 7, below PCS minimum 8, so the
proof attempt stops at parameters; no arithmetic PCS proof claimed. Next combine
with the necessary outcome serialization/SHA relation, not artificial padding.
Preserved unbuilt shared-wire outcome draft; not correctness evidence.
[Details](../../research/near-compression/tail-architecture/RECEIPT_ARITHMETIC.md).

## Shared-wire receipt arithmetic, serialization and hash

Compiled kernel derives system status from predecessor bytes and hashes outcome
bytes built from constrained burn/refund outputs. 2,305 independent cases match
(2,268 accept/37 reject), 27,216 output/length mutations reject. Three initial
and two focused refund proofs verify in-memory; 15 input/burn/digest verifier
mutations reject. Witness log 11 resolves the isolated arithmetic geometry limit.
Public-input local harness only: not a batch/state/receipt-source proof or new
size/speed/PQ result. Census: no-refund receiver<=18 takes one SHA block; other
no-refund <=64 takes two; refunds <=50 take two, >50 takes three. Observed maxima
813 short no-refund / 6 refund; unseen longer classes remain valid and required.
[Evidence](../../research/near-compression/tail-architecture/RECEIPT_OUTCOME.md).

## Private receipt batches, typed and uniform profiles

Moved receipt/account fields to private witnesses, bound shared declared context,
public receipt IDs and computed outcome hashes; native tree matches expected roots.
Typed [1024,8,8,8] profile: dense 301,310 B failed budget; sparse 266,078 B large
with 1.04–1.09 s warm, but narrow refund capacity. Broadened to uniform 1024 slots
supporting every kernel shape: 814 real receipts 215,398 B / 1.542,1.521 s; small
158,488 B / 1.506,1.519 s. Synthetic 1024 varied long refunds 230,098 B / 1.560 s
(repeated-input predecessor 1.555 s also retained). All six uniform packets
verify freshly ~0.71–0.73 s; wrong expected root/context reject. Each codec
passes 66 independent fixtures/762 mutations; full-capacity cases additionally
prove/verify. Backend scalar min 144.955 modeled bits, not composed PQ security.
Private source/state inputs are still unauthenticated; other SHA jobs omitted.
Next source-byte equality and state/runtime/history integration, no full-goal claim.
[Evidence/reproduction](../../research/near-compression/tail-architecture/RECEIPT_BATCH.md).

### Source-to-kernel audit after private batch checkpoint

Committed/pushed uniform batches as `483b3ccd6`. Independently parsed original
RC messages against exact batch bytes: 64 cases, 2,138 receipts, 10,690 rejected
field mutations. Largest receipt batch requires 1,770 additional RC SHA blocks
(three lists: 151/1,263/111,780 bytes), absent from current proof. Exact interval
report is reproducible with `audit_receipt_source.py`; compact evidence is
`evidence/receipt-source-audit.json`. Host conformance only; next circuit must
share source fields with kernel wires, constrain signer/key/list structure,
and authenticate source lists plus state/context. Full PQ/recursive NEAR goal
remains open.

### Constrained singleton source serialization

`receipt_source.rs` now serializes incoming D0a fields from the same wires as
receipt arithmetic/outcome SHA. The harness hashes a singleton RC list: 2,158
valid / 12 invalid cases, 56,108 rejected mutations; three in-memory proofs and
12 public mutations pass. 47 original singleton RC messages match exactly;
other receipts are synthetic singleton wrappers. Witness log13 vs prior local
outcome log11. No private batch or full-source membership claim. Next: measure
multi-receipt source concatenation and integrated cost before scaling. Evidence:
`research/near-compression/tail-architecture/RECEIPT_SOURCE.md` and corresponding
source/log/hash manifest. Initial generic-target build failed; explicit native
RUSTFLAGS and isolated stronger backend succeeded.

### Ordered source-list circuit and scaling failure

Fixed 16-slot shared source/outcome circuit: original lists of 0/1/2/3/4/9
receipts prove and verify freshly, 198,526–200,830 B, 0.256–0.296 s warm in the
six-case run (initial samples up to 0.300 s). Fresh verification 0.164–0.167 s.
42 proof/public mutations and 18 fresh checks reject; reversed nine-receipt
input fails source-root assertions. Independent public statements match packets.
1,024-slot construction aborts at allocation under 16 GiB virtual cap: peak RSS
9,939,772 KiB, failed allocation 6,509,559,824 B, 13.88 s. No large proof exists.
Next cheaper packing/streaming, not merely raised memory limits. Expected source
roots are not yet bound to claim membership; state/runtime/PQ/history remain.
See RECEIPT_LISTS.md and evidence/receipt-lists for code, logs, manifests.

### Packed source concatenation reaches original 804-receipt list

Direct bounded word shifts/canonical suffixes replace generic concat. Local
source kernel log13->12; 625 short + 410 wide dirty-suffix oracle cases pass,
46,062 mutation rejects; prior 2,170 source cases and three proofs still pass.
First packed large attempt still failed; removing repeated per-level cleaning
allows cap1024/log23 within 16 GiB. Original 804-receipt list: 244,838 B,
prepare0.063/prove4.480/ready4.543 s; fresh decode+verify1.549 s. Peak whole-run
RSS14,256,456 KiB; cold circuit20.710/setup4.060 s. Six small lists also verify
freshly; reversed order rejects. Full details and failure history in
PACKED_RECEIPT_LISTS.md and evidence/packed-receipt-lists. This is one list, not
full chunk; source inclusion/state/runtime/PQ history remain. Next isolate
worst-case source SHA budget from packing; any capacity reduction must be a
publicly declared, circuit-enforced profile with explicit larger-source coverage.

### Source-byte capacity experiment and prover attribution

NPLIST03 fixed full/compact modes count an eight-byte selector; compact forces
source <=128*receipt capacity in circuit. Exact512-byte cap4 case proves;513
rejects at source-byte-cap and proves in full mode; fresh checks pass. Initial
tiny ColumnTooShort issue fixed by bounding column log to witness log-8.
Original804 compact128KiB source profile:244,814B; readiness4.350/4.197/4.318s,
fresh1.489s. Still log23:10,074,314 private words. Source SHA capacity5553->2049
is insufficient. Profiled prover:opening1706ms,bitand1078ms,commit642ms,
shift579ms,switch198ms,pack50ms. Next smaller domain requires <=8,388,608 private
words (16.7% reduction). Pinned frontend select uses BMUL; next compare exact
bitmask selection rather than further source-size narrowing. Keep full profile
as coverage baseline. Source/state/runtime/PQ history remain incomplete.
See SOURCE_BYTE_BUDGET.md and evidence/source-byte-budget.

### Selection rejection and four-core baseline

Bitmask-concat selection passes all short/wide/source and capacity checks but
increases cap16 private words112734->114931 and AND55594->78752; cap1024 build
fails 16 GiB virtual limit. Rejected, source preserved. Existing byte-budget
binary with Rayon4/CPUs8-11 proves original804 in244814B /3.770 and3.716s warm;
fresh Rayon1/CPU8 verification1.448s passes. Commit~0.63s/opening~1.8s unchanged;
next inspect OpeningProof::timings and serial commitment/opening, not another
thread sweep. Source/state/runtime/PQ history remain incomplete. Evidence:
SELECTION_AND_PARALLEL.md and evidence/selection-and-parallel.
