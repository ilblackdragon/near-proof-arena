# Account ledger handoff — 2026-10-25 (post in-circuit trie)

## Checkout and runtime state

- Owned worktree: `/data/illia/nearproof-wt/pq-tail-architecture`.
- Branch: `lane/pq-tail-architecture`; checkpoint preceding the trie goal: `3e18aa43b`.
- Main checkout: `/data/illia/nearproof`. Do not merge or modify main implicitly.
- Scratch: `/data/illia/pq-tail-architecture-20261024`.
- All builds/proofs/verifications finished. No live process/session to resume.
- No GPU measurements. CPU Ryzen 9 9950X3D, physical cores 8–11 for four-core runs.

Goal remains under 300,000 bytes, PQ, bounded recursive history, applicable to
full NEAR, final proof within 1–2 seconds of chunk. **Not achieved.**

## State authentication is now IN-CIRCUIT (NPMULT03)

The account table's trie membership is proven, not host-audited. Each PTrie
witness node's `node_ser` is reconstructed in-circuit from decoded fields and
hashed with tight_sha:

- The chain top hash must equal four public statement words carrying the
  claim-derived `prev_state_root` (statement head).
- Branch children link by rank among set bitmap bits, selected by the row's
  key nibble; ext children link after their fragment.
- Each active row's leaf `value_ref` must equal `u32le(72)||sha256(72-byte
  initial value)`, binding the trie leaf to the public table row (the 4
  code-hash words are witness-only, authenticated through the leaf).
- **Key-path correspondence** (the binding the old host audit lacked): key =
  `nibbles(0x00||name)` computed from the row's PUBLIC name wires; branches
  consume exactly one nibble each; ext/leaf hexPrefix fragments equal the key
  nibbles positionally; the path ends exactly at the leaf; walked nibbles
  must be set bitmap bits. A swapped witness chain for another account is
  rejected by nibble selection even when both accounts have identical values
  (demonstrated with a crafted duplicate-initial fixture).

Corpus profile (explicit, not universal): 5 shared chain nodes with roles
[Branch,Branch,Branch,Ext,Branch], per-account leaf attaching by the final
key nibble, max node 331 B, 16 account slots. Tag-2 branches are out of
profile (roles asserted). Empty tables gate all trie constraints on a
has-accounts bit; the empty-table root remains host-checked only — that is
the one remaining host-side root case, documented.

## Latest integrated result (NPMULT03)

| Original fixture | Counts | Packet | Envelope | Warm ready | Fresh verify |
|---|---|---:|---:|---:|---:|
| `00-h10035-s3` | 1, 9, 804 | 250,126 B | 250,352 B | 3.082 s | 1.521 s |
| `00-h10036-s3` | 0, 0, 711 | 250,126 B | 250,352 B | 2.983 s | 1.477 s |

vs NPMULT02 baseline: +32 B (root words), AND +2.5% (4,191,241), private
+1.8%, warm/verify within run noise, peak RSS 13.3 GB-scale KiB under the
16 GiB cap, witness log 23 (no suite jump). Single observations, no p95.
One 00-h10036-s3 run produced a 295,038 B packet (nondeterministic LaBRADOR
terminal tail block when the deepest reduction crossed rank 13); three
repeats and the final runs measured 250,126 B. Backend export size is
witness-shape dependent; both observed sizes are under 300,000 B.

## Rejection battery (all in-circuit, with the final binary)

Prior: forged-repeat-balance at `.list-1.slot-4.before-balance`; boundary
padding exploit at `.name-padding-0-5`; forged receiver padding at
`.exactly-one-match`; dup-name/wrong-final/nonzero-inactive at their table
constraints. Note the trie now catches several ledger mutants earlier:
wrong-initial and wrong-locked at `r0-vref-hash`, inert-account at
`leaf10-hp-len-range` — the trie value binding is doing work.

New trie negatives: wrong root word at `trie-root-0`; mutated shared node at
`link-b1`; mutated leaf value_ref at `r0-leaf-link`/`r0-vref-hash`; swapped
chain at `r0-leaf-link`; **duplicate-initial swap rejected by key-nibble
selection despite identical value hashes**; corrupted branch bitmap at
`branch-3-kids-overflow`/`len_check`.

## Files / commands for continuation

Scratch implementation:
- `labinius/crates/binius/src/bin/near-receipt-multi.rs` — NPMULT03 driver;
  requires `NEAR_LEDGER` (NPMLEDG01) and `NEAR_TRIE` (NPMTRIE01).
- `.../support/receipt_account_trie.rs` — the in-circuit trie module.
- `.../support/receipt_account_ledger.rs` — the ledger/table module.
- `.../support/receipt_multi_wire.rs` — NPMULT03 trusted-local decoder.
- `export/src/bin/account-trie-path-export.rs` — NPMTRIE01 witness exporter
  (shared-prefix + role assertions; value_ref==sha256(initial) at export).
- Pre-trie snapshots: `prover-before-npmtrie.rs`.

Research scripts (worktree `research/near-compression/tail-architecture`):
- `audit_account_paths.py` — reference model incl. key-path correspondence.
- `multi_statement.py` / `audit_multi_statement.py` — NPMULT03 statement
  checks (root vs claim-derived value; 141 mutations reject per fixture).

Evidence: `evidence/account-ledger-trie/` — manifest.json (44 verified
hashes, measurements, rejection records, trust boundary, open obligations),
both envelopes, prove/verify logs, all 15 rejection logs, witness fixtures
+ 6 trie mutants, source copies.

Prove/verify commands (build unchanged; see the previous handoff for the
native-flags build):

```
LABRADOR_JL_THREADS=4 LABRADOR_PAIR_THREADS=4 LABINIUS_COMMIT_THREADS=4 \
RAYON_NUM_THREADS=4 NEAR_LEDGER=CASE.ledger NEAR_TRIE=CASE-trie.bin \
NEAR_EXPORT_DIR=OUT taskset -c 8-11 near-receipt-multi 16,16,1024 compact CASE.multi
RAYON_NUM_THREADS=1 NEAR_LEDGER=CASE.ledger NEAR_TRIE=CASE-trie.bin \
NEAR_VERIFY_EXPORT=PACKET NEAR_EXPECTED_PUBLIC=PUBLIC \
  taskset -c 8 near-receipt-multi 16,16,1024 compact
```

Trie witness export: `account-trie-path-export CASE_DIR OUT.bin` (writes
OUT.bin + OUT.bin.json); `audit_account_paths.py OUT.bin.json LEDGER REPORT`.

## Lessons to preserve

- The framework's booleans are MSB-bools: `band(shr(x,k),1)` is an LSB 0/1
  that ANDs to zero inside select/band/assert_true. Normalize with
  `shl(..,63)`; keep raw 0/1 only for arithmetic (popcounts).
- No u16-wraparound arithmetic tricks on u64 words — use `isub` variants.
- A running register initialized to the row's public initial balance removes
  the first-touch/repeat case split; before==register is the single binding.
- Match on full padded name words; padding boundaries are `>=` boundaries.
- Do not duplicate circuit constraints in host parsers — reject paths must
  exercise the circuit.
- Conditional asserts need explicit OR-inactive escapes for zero-row tables.
- Host audits check what the proof does not; now that the trie chain is
  in-circuit, the Python audit is a reference model, not the binding.
- Before committing, check `git status` for incidental deletions under
  `research/near-compression/native/wasm-base/target`; restore, don't commit.

## Still open

Variable-depth/variable-shape trie chains (the 5-node shared profile is
asserted, not general), post-state root and full state-transition semantics,
access keys/routing/domain checks, general actions/Wasm, scheduling,
recursive history, composed PQ security, zero knowledge, hostile C decoder
safety, and the 1–2 second deadline. The 16-slot account profile is
explicit, not a claim of arbitrary full-NEAR coverage.
## History (superseded sections preserved in git)

- 2026-10-24 (commit 2da81825c): the forged-starting-balance hole closed via
  the 16-slot account table + running-balance registers (NPMULT02); the
  handoff counterexample rejected at `.list-1.slot-4.before-balance-0-0`.
- 2026-10-24 (commit 3e18aa43b): review-caught padding off-by-one fixed
  (`icmp_ugt` -> `icmp_uge`; boundary exploit reproduced first, then
  rejected at `.name-padding-0-5`).
- 2026-10-25 (this commit): trie membership moved in-circuit (NPMULT03);
  key-path correspondence closes the duplicate-value swap class.
