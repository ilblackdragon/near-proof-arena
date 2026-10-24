# Account ledger handoff — 2026-10-24

## Checkout and runtime state

- Owned worktree: `/data/illia/nearproof-wt/pq-tail-architecture`.
- Branch: `lane/pq-tail-architecture`; checkpoint preceding this handoff: `b76be2f48`.
- Main checkout: `/data/illia/nearproof`. Do not merge or modify main implicitly.
- Scratch: `/data/illia/pq-tail-architecture-20261024`.
- All builds/proofs/verifications finished. No live process/session to resume.
- No GPU measurements. CPU Ryzen 9 9950X3D, physical cores 8–11 for four-core runs.
- No `.codegraph/` in this owned worktree or scratch when last inspected.

Goal remains under 300,000 bytes, PQ, bounded recursive history, applicable to
full NEAR, final proof within 1–2 seconds of chunk. **Not achieved.**

## Best integrated result

See `MULTI_LISTS.md`. One circuit covers all three original source lists of:

- `00-h10035-s3`: counts [1,9,804], 814 receipts, 3.011 s warm.
- `00-h10036-s3`: counts [0,0,711], 711 receipts, 2.792 s warm.

Fixed capacities [16,16,1024], compact source-byte limits [2048,2048,131072].
Inner packet 247,786 B; NPMSET01 envelope with all paths 248,012 B.
Source/context/order and complete outcome-root host checks pass against original
claims. Fresh serial proof verification without receipt witnesses passes
(1.446/1.449 s). Peak RSS 12,806,272 KiB, virtual cap 16 GiB. Cold circuit/setup
excluded from warm measurements. New multi circuit requires its own verifier.

## Latest finding: an accepted state-chain counterexample

The current relation does **not** authenticate starting balances or link
consecutive receipts for the same account. We demonstrated this, not just inferred
it: change `00-h10035-s3`, list1 receipt4 (global index5), receiver `s0a01`.
Its previous update is global index0. Increase private before and recorded after
by one; leave deposits, source bytes, public digests and all public outputs intact.

- Expected before: 999981279259175733117231851975.
- Forged before: 999981279259175733117231851976.
- Forged after: 999981279784123420617231851976.
- Existing proof accepts: 247,786 B, 3.032 s warm.
- Fresh verifier accepts against the **original** expected public vector in 1.451 s.
- Existing source/context/outcome host checks also accept (same claim roots).
- New ordered account model rejects exactly at `list=1 receipt=4`.

This is a known missing obligation in a diagnostic relation, **not a fixed bug**.
Never describe the current packet as full NEAR validity. Evidence is in
`evidence/account-ledger`; actual mutant fixture/packet remain in scratch.

## Account model and next implementation

`audit_account_ledger.py` independently threads balances through the raw original
list fixtures and compares initial/final 72-byte account values with native trie
exports. It checks receiver names/padding, before balance, deposit/after,
unchanged locked/storage/code bytes, no omitted/extra account table entries and
final account values. It is a host model, **not yet a circuit constraint**.

All 64 fixtures / 2,138 receipts match; 2,010 repeated updates and 25 cross-list
links. Ninety-six altered initial/final account tests reject. Maximum unique
receivers observed: 10. This observation is not a universal NEAR domain bound.

For each large fixture, a variable-length public table holding receiver names,
initial account bytes and final amounts would occupy 974 B. All raw main-state
witness values total 3,996 B (54 values) for the 814/711 fixtures. These are size
censuses, not an implemented minimal multiproof or final combined packet size.
Initial authentication currently trusts native partial-trie construction;
full final-state root calculation also remains unproved.

Suggested next implementation: a bounded public account table (e.g. 16 slots)
and private running balance registers through the existing multi-list circuit.
For every active receipt, require exactly one canonical receiver match, bind its
before/locked/storage to that account register, and update the register with the
already constrained arithmetic after value. Enforce unique canonical account
names, zero inactive table rows, valid lengths and final balances. Preserve
registers across list boundaries. Include initial/final account bytes in the
public statement and authenticate their reads/writes against expected state
roots. Keep this counterexample as a required rejection test. Measure circuit
size/memory before promoting; the 16-account profile would be explicit, not a
claim of arbitrary full-NEAR coverage.

Still open: authenticated state updates, access-key/routing/domain checks,
scheduling, general actions/Wasm, recursive history, composed PQ security,
zero knowledge, hostile C decoder safety and the two-second deadline.

## Files / commands for continuation

Scratch implementation:
- `labinius/crates/binius/src/bin/near-receipt-multi.rs`.
- `labinius/crates/binius/src/bin/support/receipt_multi_wire.rs` and prior support modules.
- `labrador-sis128/`: stronger-policy C backend, optional parallel pairs/JL.
- `export/src/bin/account-ledger-export.rs`: native initial/final account exporter.
- `account-ledgers/*.json`: 64 native account exports.
- `multi-lists/{00-h10035-s3,00-h10036-s3}.multi` and `.public`.
- `multi-lists/forged-repeat-balance.multi`.
- `exported-forged-state/forged-repeat-balance.packet`.
- `account-ledger-audit.json`, `forged-repeat-balance.log`,
  `verify-forged-repeat-balance.log`, `forged-state-host-audit.json`.

Original claims: `/data/illia/nearproof/oracle/fixtures/v3/public-d0a/d0`.
Original exported receipts: scratch `receipt-export/CASE/{rcpt,sha_r}.json`.
Original per-list fixtures: scratch `receipt-lists/CASE-listN.list`.

From scratch `labinius`, build with explicit native flags (global config otherwise
can override native CPU features):

```
ulimit -v 16777216
RUSTFLAGS='-C target-cpu=native -C link-arg=-fuse-ld=mold' \
CARGO_TARGET_DIR=/data/illia/pq-tail-architecture-20261024/target \
LABINIUS_LABRADOR_DIR=/data/illia/pq-tail-architecture-20261024/labrador-sis128 \
  taskset -c 8-15,24-31 cargo build --release -j4 -p labinius-binius \
  --bin near-receipt-multi
```

Prove with `LABRADOR_JL_THREADS=4 LABRADOR_PAIR_THREADS=4
LABINIUS_COMMIT_THREADS=4 RAYON_NUM_THREADS=4`, CPU8–11,
`near-receipt-multi 16,16,1024 compact FIXTURE.multi`.
`NEAR_EXPORT_DIR` selects packet output. Fresh verify uses
`NEAR_VERIFY_EXPORT=PACKET NEAR_EXPECTED_PUBLIC=PUBLIC RAYON_NUM_THREADS=1`,
CPU8, same binary/profile. C decoding remains trusted-local.

Native exporter builds from scratch `export` with
`CARGO_TARGET_DIR=.../export-target cargo build --release -j4 --bin account-ledger-export`.
Run it as `account-ledger-export CASE_DIR OUTPUT_JSON`.

Run `audit_account_ledger.py EXPORTS LISTS LEDGERS CLAIMS REPORT --mutant MUTANT`.
For packet host checks use `audit_multi_statement.py` as documented in
`MULTI_LISTS.md`; this does not replace cryptographic proof verification.

## Lessons to preserve

- Frontend `assert_false` checks only MSB; use `assert_zero` for whole-word guards.
- Do not relax lattice ranks/norm/security policy for speed; composed PQ is unproved.
- NEAR receipt membership starts at SHA256(list_digest), not list_digest.
- Public source/outcome commitments do not authenticate private account balances.
- Canonical receiver padding/uniqueness is essential for account-table matching.
- Serial/parallel kernels retain exact per-output accumulation order; scalar-product
  lazy cache must be warmed before worker launch. Keep the existing whole-prover lock.
