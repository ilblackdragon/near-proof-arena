# PQ tail architecture — 2026-10-23

Worktree `/data/illia/nearproof-wt/pq-tail-architecture`, branch
`lane/pq-tail-architecture`, based on `8ac3de9f6`.

Created an isolated research lane and [experiment plan](../../research/near-compression/tail-architecture/README.md).
Audited the existing untracked `pq-realtime-hypothesis` single-pass endpoint +
shared-opening prototype. Original recorded executables were missing; rebuilt
source snapshots offline, without changing their owning lane or dependencies.

## Measured checkpoint

- Three fresh D0a prepared-trace proofs: identical **258,788 B** packets, 41,212 B
  below the decimal cap. Separate-process verifier accepted all three against
  the existing key, AIR and expected claim, without witness sidecars.
- Median process wall: **29.816 s prove**, **0.864 s verify**. Eight Rayon threads
  for prover on CPUs 8–15/24–31; verifier pinned to CPU 8. Historical 10.64 s
  internal prover timing was not reproduced; no claim of a like-for-like regression.
- Ten external mutations rejected: seven section bit flips plus trailing byte,
  truncation and oversized section length. Verifier additionally reports its
  internal shape/wire checks. Rejection exits include assertion exit 101.
- Generated key JSON: **3,045,746 B**, separate from packet. Reuse on this same
  fixture works; authenticated setup reuse across chunks remains unestablished.
- WHIR is 200,758 B (78%): opening authentication dominates terminal size.

Evidence and runner: `research/near-compression/tail-architecture/`.
Packets/key sidecars are ignored local outputs; hashes and reports are committed.
Build scratch: `/data/illia/pq-tail-architecture-20261023`; sources are snapshots,
external path dependencies are shared, some lack usable Git history. Provenance
is recorded, but a portable hermetic build is unfinished.

## What this does not establish

No recursive accumulator, end-to-end witness execution timing, D3 AIR proof,
ZK or complete PQ security bound. Diagnostic zero-grinding profile differs from
approved U10. Numeric security target 268 is not a composed QROM proof. Existing
verifier report contains a stale “live single-pass prover remains” limitation;
this audit supplied fresh packets, while its setup/security limitations remain.

## Next work

1. Freeze verifier statement/setup policy and test cross-chunk key reuse.
2. Isolate rebuilt/historical performance gap; measure execution + trace costs.
3. Specify authenticated algebraic accumulation invariant and terminal discharge;
   test history lengths 1/2/4/8 before calling the construction recursive.
4. Compare shared opening and candidate terminal PCS on identical obligations.
   SHA384-only baseline remains; lattice assumptions require an explicit choice.

Do not resume blind parameter sweeps or promote this diagnostic to admission.

## Live witness and locally derived-key follow-up

User clarified deadline: **final proof within 1–2 seconds of chunk**.
Rebuilt newer `declared-profile-prover` and `local-key-packet-verifier` from the
isolated source snapshot, with `-C target-cpu=native`; original fingerprint
also used native CPU compilation. This is not a clean speed comparison:
an unrelated aggregation process consumed ~20 logical CPUs during this run.

| Fixture | Trace cells | Packet B | Trace + prove s | Verify s |
|---|---:|---:|---:|---:|
| 00-h10004-s3 | 1,262,608 | 258,792 | 17.26 | 1.17 |
| 00-h10006-s3 | 2,107,452 | 274,763 | 20.10 | 1.28 |
| 00-h10013-s2 | 2,669,472 | 279,454 | 20.86 | 1.28 |
| 00-h10035-s3 | 156,624,112 | none | profile rejects | — |

Selection: prior two fixtures, median and maximum witness-byte fixtures among
64 `expected_rel_d0a=true` cases in public-d0a/d0. All three produced packets
verify without a supplied key and match prover-generated key hashes. Width
0/129/width+1 rejected for each. Largest fixture passes full trace constraint
and bus precheck, then fails the n_stack=14 height bound (65,536 rows). No
inference of relation invalidity or proof-system impossibility follows.

The 3 MB sidecar concern is addressed for these three cases by local derivation;
security for the profile family and full NEAR support remain open. Receipt and
receipt-SHA tables consume 89.5% of the largest trace. This changes priority:
measure representation/commitment acceleration, not further small-fixture tuning.
Runner and captured reports/logs are in tail-architecture/evidence/live-native.
Scratch contains full trace dumps; committed evidence excludes these large files.
