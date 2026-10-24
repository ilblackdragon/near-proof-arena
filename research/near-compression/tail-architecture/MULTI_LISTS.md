# One proof for every source list in two original chunks

2026-10-24. One combined relation now covers all source lists of each of two
original D0a fixtures, with a shared block context and independent expected
public bytes. Their full ordered outcome roots match the original claims.
The envelope includes every source Merkle path and remains below 300,000 bytes.

| Original fixture | Ordered receipt counts | Inner packet | With all paths | Warm readiness |
|---|---|---:|---:|---:|
| `00-h10035-s3` | 1, 9, 804 | 247,786 B | 248,012 B | 3.011 s |
| `00-h10036-s3` | 0, 0, 711 | 247,786 B | 248,012 B | 2.792 s |

These are different workloads, one observation each, not repetitions or p95.
Warm readiness measures witness fill, proof, encoding and file export of the
inner packet; it excludes circuit/setup and host claim/envelope validation.
No GPU was used. The 1–2 second deadline is still unmet.

## Update: account ledger constrained (NPMULT02)

The same circuit now carries a 16-slot public account table and running-
balance registers threaded across lists; the forged-starting-balance
counterexample rejects in-circuit. A review-caught off-by-one in the table
padding constraint (the byte at name_len was unconstrained; fixed with
icmp_uge after reproducing a +1 forged-balance exploit through it) is
documented in ACCOUNT_LEDGER_HANDOFF.md. Packets 250,094 B, envelopes
250,320 B, warm 3.090/3.133 s, fresh verify 1.511/1.502 s (pre-fix binary;
post-fix reruns 3.56/3.88 s under background load, sizes unchanged), RSS
13,115,024/13,024,740 KiB. See ACCOUNT_LEDGER_HANDOFF.md and
evidence/account-ledger-circuit for the constraint description, negative
batteries, the boundary-exploit record, and the host-audited trie-path
binding. This section's earlier numbers remain the pre-constraint
baseline.

## Combined relation

`near-receipt-multi` builds each existing receipt-list relation within one circuit
and one commitment/opening. It explicitly equates gas price (two words), height
and destination shard across lists. Each list independently constrains its count,
ordered source serialization/hash, local D0a transfer arithmetic and outcome
hashes. The source and execution inputs remain shared wires.

The tested fixed profile is capacities `[16,16,1024]`, compact source byte budgets
`[2048,2048,131072]`. Counts are `[1,9,804]` or `[0,0,711]`, not fixed by the
profile. Both use log23, 10,299,688 private words and 11,643 public words. The
profile is an explicit supported subset, not a universal bound; the corpus has
up to nine lists. Other profiles need their own capacity and performance checks.

`NPMULT01` carries list count, ordered capacity vector, mode and the same seven
length-framed proof sections. The decoder compares all profile fields against
locally selected expected values before importing C objects. This is a new
circuit/codec: the old single-list verifier cannot verify it. Fresh verification
uses the new binary with serial backend/thread defaults, without receipt witnesses.
C decoding remains trusted-local.

## Claim-relative terminal checks

`multi_statement.py` checks an `NPMSET01` envelope:

```
magic8 || u32(packet_bytes) || packet || u32(number_of_paths)
       || (u32(depth) || (direction_u8 || sibling32)*)*
```

It requires exactly one path for every source in claim-derived application order.
It checks fixed capacities/mode, shared context derived from the expected claim,
count/active-prefix/index formatting, each source digest's double-hashed Merkle
membership, zero inactive records and distinct active receipt IDs.

For each active receipt, it constructs the outcome leaf from
`u32(2) || receipt_id || partial_outcome_digest`, hashes it, and reconstructs the
ordered tree (promoting odd nodes unchanged). The resulting root equals the
original claim's outcome-root field in both fixtures. The public tape also
matches an independently generated concatenation of the original list fixtures.

The helper returns the inner packet and public statement. **The caller must
cryptographically verify that packet against that same public statement and
fixed profile.** Host checks alone are not proof verification. Expected sources
and context come from a separate claim-only native exporter, not prover metadata.
The native claim parser/source selection/shuffle remain trusted here.

## Validation

- Both full original list sets prove and pass 21 public mutations per proof.
- Fresh serial verification: 1.446 / 1.449 s; no witnesses, canonical backend
  roundtrip and four negative checks per packet.
- All source paths, ordered public records and complete outcome roots match
  original claims. Twenty-four host-envelope mutations reject per fixture,
  including omitted/reordered paths, altered profiles, contexts, counts, source
  digests and outcome digests.
- A targeted two-empty-list fixture proves with consistent context. Changing one
  list's shard and recomputing its otherwise-correct source digest rejects solely
  at `.shared-context-1-3`, testing the new cross-list constraint.
- Peak RSS: 12,806,272 KiB under a 16 GiB virtual limit. CPU: Ryzen 9 9950X3D,
  physical cores 8–11; Rayon/commitment/pair/JL workers all four for proving.

## What remains unproved

This is stronger than the earlier isolated-list result, and the account
ledger is now circuit-constrained (ordered balances, repeated receivers,
final balances), but it is still not full NEAR validity. The account
table's trie membership is host-audited rather than proven in-circuit;
access keys, routing/domain predicates, general actions/Wasm, scheduling
and full state transition semantics remain absent. Matching outcome
commitments cannot substitute for those checks. Recursive bounded history,
composed PQ security, zero knowledge and hostile parser safety also remain
open.

The next semantic priority is in-circuit trie membership for the account
table (replacing the host audit), then access keys and routing. Broader
source profiles and lower proving latency remain necessary alongside that
work.

## Reproduction

Driver/codec source, exporter, logs and hashes are in `evidence/multi-lists`
(pre-constraint baseline) and `evidence/account-ledger-circuit` (NPMULT02 with
the account ledger). Reuse prior support modules and parallel-JL backend.
Generate fixtures with (ledger JSON exports come from account-ledger-export):

```
python3 make_account_ledger_fixture.py account-ledgers/CASE.json OUT/CASE.ledger
python3 make_multi_lists.py EXPORTS LISTS OUT --capacities 16,16,1024 \
  --ledgers account-ledgers 00-h10035-s3 00-h10036-s3
LABRADOR_JL_THREADS=4 LABRADOR_PAIR_THREADS=4 LABINIUS_COMMIT_THREADS=4 \
RAYON_NUM_THREADS=4 NEAR_LEDGER=OUT/CASE.ledger NEAR_EXPORT_DIR=OUT \
  taskset -c 8-11 near-receipt-multi 16,16,1024 compact FIRST.multi SECOND.multi
RAYON_NUM_THREADS=1 NEAR_LEDGER=OUT/CASE.ledger NEAR_VERIFY_EXPORT=PACKET \
  NEAR_EXPECTED_PUBLIC=PUBLIC taskset -c 8 near-receipt-multi 16,16,1024 compact
python3 audit_multi_statement.py PACKET PUBLIC ROOTS_JSON AUTH_JSON CLAIM_BIN \
  ENVELOPE LEDGER REPORT --capacities 16,16,1024
python3 audit_account_paths.py PATHS_JSON LEDGER REPORT
```

Build with existing native RUSTFLAGS and isolated backend path. Claim roots JSON
must use this checkpoint's exporter, which includes the claim-derived context.
