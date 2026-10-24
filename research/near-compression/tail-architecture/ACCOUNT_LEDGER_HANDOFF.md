# Account ledger handoff — 2026-10-24 (post circuit constraint)

## Checkout and runtime state

- Owned worktree: `/data/illia/nearproof-wt/pq-tail-architecture`.
- Branch: `lane/pq-tail-architecture`; checkpoint preceding the circuit fix: `d9b5c4d02`.
- Main checkout: `/data/illia/nearproof`. Do not merge or modify main implicitly.
- Scratch: `/data/illia/pq-tail-architecture-20261024`.
- All builds/proofs/verifications finished. No live process/session to resume.
- No GPU measurements. CPU Ryzen 9 9950X3D, physical cores 8–11 for four-core runs.

Goal remains under 300,000 bytes, PQ, bounded recursive history, applicable to
full NEAR, final proof within 1–2 seconds of chunk. **Not achieved.**

## Circuit fix landed: the forged-starting-balance hole is closed

The prior handoff's counterexample — `forged-repeat-balance.multi`, list1
receipt4, receiver `s0a01`, before/after +1 with public digests unchanged — is
now **rejected in-circuit**:

- Rejection point: `.list-1.slot-4.account-bind.before-balance-0-0`
  (`Word(0xe1b14706136c69c8) != Word(0xe1b14706136c69c7)`), plus the
  downstream slot-8 chain break.
- Mechanism: a 16-slot public account table (18 words/row: active, name_len,
  name[8], initial balance/locked/storage, final balance) and private
  running-balance registers threaded through every receipt slot in
  application order, across list boundaries. Registers start at each row's
  public initial balance, so first touch and repeats are one case: `before ==
  register` on every matched receipt, and the register advances to the
  already-constrained arithmetic after-value.
- Guards: exactly-one padded-name match per active receipt (sum asserted),
  pairwise-distinct canonical names, zero inactive rows (whole-word), active
  rows 1..=64 name length with byte-exact zero padding **from name_len on**
  (`icmp_uge`, see the boundary-bug note below), every active row
  matched at least once (row-covered), final table balances == final
  registers, locked/storage invariant per matched row on every touch.

## Boundary bug found in review (fixed): name-padding off-by-one

The first version of the padding constraint gated on `icmp_ugt(k, name_len)`
— strictly greater — leaving the byte at `k == name_len` unconstrained in
table rows. That was exploitable, and an external review caught it: a table
row and receipts carrying **matching** garbage at that boundary byte still
word-matched (name_eq compares all eight full words), while `clean()` in the
source/outcome serializers masks bytes `>= len`, so the digests stayed
honest. With that, a +1 forged starting balance was accepted for all 78
`s0a01` receipts — reopening the exact hole the constraint was built to
close. Reproduced before fixing: `populate_wire_witness` succeeded on the
exploit pair (evidence `exploit-padding-boundary.{ledger,multi}`).

Fix: `icmp_ugt` -> `icmp_uge` in the table padding loop — the byte at
`name_len` is padding too. After the fix the exploit rejects at
`.account-table.account-0.name-padding-0-5` (the boundary byte itself), the
original counterexample still rejects at its exact transition, all six
ledger mutants still reject, both originals still prove (250,094 B) and
fresh-verify, and the empty-context pair still proves. The lesson: a padding
boundary is a `>=` boundary, and masking in the serialization layer must
never be the only thing standing between garbage padding and name matching.

## Latest integrated result (NPMULT02, account-table profile)

One circuit covers all three original source lists of both fixtures with the
account ledger constrained. Fixed capacities [16,16,1024], compact budgets,
16 account slots.

| Original fixture | Ordered counts | Packet | With paths | Warm ready | Fresh verify |
|---|---|---:|---:|---:|---:|
| `00-h10035-s3` | 1, 9, 804 | 250,094 B | 250,320 B | 3.090 s | 1.511 s |
| `00-h10036-s3` | 0, 0, 711 | 250,094 B | 250,320 B | 3.133 s | 1.502 s |

Baseline (pre-constraint): 247,786/248,012 B, 3.011/2.792 s, verify
1.446/1.449 s, RSS 12,806,272 KiB. Account-constraint overhead: +2,308 B,
+0.08/+0.34 s warm, +0.05 s verify, +0.2–0.3 GiB RSS. Single observations,
not p95. Witness log stays 23 (no suite jump); public 11,931 words, private
10,695,840, AND 4,087,792. Peak RSS 13,115,024/13,024,740 KiB under the
16 GiB cap. Geometry: circuit_s ≈ 19.1 s cold.

State-root binding (host-audited, NOT in-circuit): per-account PTrie path
witnesses (6 nodes each) rehash to the claim's `prev_state_root`
(`7156f545…` / `2ee62d9e…`); each leaf's `value_ref` is
`u32le(72) || sha256(initial)` binding the table's initial bytes. Four
root/node/leaf/swap negatives reject per case. The table is public in the
statement and bound by the proof; the trie chain check remains host-side.

## Negative evidence

- Forged counterexample rejects at the exact transition (above).
- Ledger mutants all reject in-circuit at their designed constraints:
  duplicate name (`distinct-names`), wrong initial (`before-balance`),
  wrong final (`final-balance`), wrong locked (`locked-unchanged`), nonzero
  inactive row (`inactive-zero`), inert uncovered row (`row-covered`),
  forged receiver padding (`exactly-one-match`).
- 112 in-proof account-table mutations reject (16 rows x 7 positions).
- 21 in-process public mutations reject per proof; 137 host-envelope
  mutations reject per fixture (113 of them table positions); empty-context
  pair with empty table still proves.

## Files / commands for continuation

Scratch implementation (all updated for NPMULT02):

- `labinius/crates/binius/src/bin/near-receipt-multi.rs` — driver; reads
  `NEAR_LEDGER` (NPMLEDG01 binary fixture), threads registers, emits
  NPMULT02 packets; `NEAR_EXPECT_REJECT=1` prints in-circuit rejection points.
- `labinius/crates/binius/src/bin/support/receipt_account_ledger.rs` — the
  account table/register constraint module.
- `labinius/crates/binius/src/bin/support/receipt_multi_wire.rs` — NPMULT02
  decoder (trusted-local).
- `export/src/bin/account-trie-path-export.rs` — per-account trie path
  witnesses + prev_state_root.
- Pre-fix snapshots: `prover-before-account-ledger.rs`,
  `support/receipt_multi_wire_before_account_ledger.rs` in scratch.

Research scripts (worktree `research/near-compression/tail-architecture`):

- `make_account_ledger_fixture.py` — NPMLEDG01 generator from native JSON.
- `audit_account_paths.py` — trie-chain host audit + 4 negatives.
- `multi_statement.py` / `audit_multi_statement.py` / `make_multi_lists.py` /
  `receipt_list_public.py` — NPMULT02 statement checks (table parsing,
  ledger-fixture comparison, 113 table mutations).

Evidence: `evidence/account-ledger-circuit/` — manifest.json (hashes,
measurements, trust boundary, open obligations), both packets' envelopes,
proof/verify logs, rejection log, trie-path witnesses and reports, source
copies, ledger fixtures.

From scratch `labinius`, build with explicit native flags (global config
otherwise can override native CPU features):

```
ulimit -v 16777216
RUSTFLAGS='-C target-cpu=native -C link-arg=-fuse-ld=mold' \
CARGO_TARGET_DIR=/data/illia/pq-tail-architecture-20261024/target \
LABINIUS_LABRADOR_DIR=/data/illia/pq-tail-architecture-20261024/labrador-sis128 \
  taskset -c 8-15,24-31 cargo build --release -j4 -p labinius-binius \
  --bin near-receipt-multi
```

Prove (note: `NEAR_LEDGER` is now required; ledger fixtures are generated by
`make_account_ledger_fixture.py` from the native `account-ledgers/*.json`):

```
LABRADOR_JL_THREADS=4 LABRADOR_PAIR_THREADS=4 LABINIUS_COMMIT_THREADS=4 \
RAYON_NUM_THREADS=4 NEAR_LEDGER=CASE.ledger NEAR_EXPORT_DIR=OUT \
  taskset -c 8-11 near-receipt-multi 16,16,1024 compact CASE.multi
```

Fresh verify: `NEAR_VERIFY_EXPORT=PACKET NEAR_EXPECTED_PUBLIC=PUBLIC
RAYON_NUM_THREADS=1 NEAR_LEDGER=CASE.ledger`, CPU8, same binary/profile.
Required-rejection runs: add `NEAR_EXPECT_REJECT=1` (prints the failing
constraint paths). C decoding remains trusted-local.

Trie-path export (scratch `export`):
`account-trie-path-export CASE_DIR OUT_JSON` (built into
`export-target/release`); then
`audit_account_paths.py OUT_JSON CASE.ledger REPORT`.

## Lessons to preserve

- Frontend `assert_false` checks only MSB; use `assert_zero` for whole-word
  guards (the account-table booleans/ranges depend on this).
- A running register initialized to the row's public initial balance removes
  the first-touch/repeat case split entirely; before==register is then the
  single binding for every touch.
- Match on full padded name words (length + all eight 64-bit words); pad
  rows byte-exact, or padding garbage silently changes which account a
  receipt binds to.
- Do not duplicate circuit constraints in the host fixture parser: reject
  paths must exercise the circuit, not a host assert (the nonzero-inactive
  mutant initially passed because the parser pre-validated it).
- Host audits check what the proof does not; make the split explicit in
  docs. The trie-chain check is host-side today; in-circuit SHA256 chains
  are the next step toward state-validity proof.
- Do not relax lattice ranks/norm/security policy for speed; composed PQ is
  unproved.
- NEAR receipt membership starts at SHA256(list_digest), not list_digest.
- Serial/parallel kernels retain exact per-output accumulation order;
  scalar-product lazy cache must be warmed before worker launch. Keep the
  existing whole-prover lock.
- Before committing, check `git status` for incidental deletions under
  `research/near-compression/native/wasm-base/target` (a recurring pattern
  from concurrent lanes); restore them with `git checkout --` rather than
  committing the deletions.

## Still open

In-circuit trie membership (replace the host audit), access-key/routing/
domain checks, scheduling, general actions/Wasm, full state-transition
semantics, recursive history, composed PQ security, zero knowledge,
hostile C decoder safety, and the 1–2 second deadline. The 16-slot account
profile is explicit, not a claim of arbitrary full-NEAR coverage.
