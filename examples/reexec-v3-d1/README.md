# reexec-v3-d1 — formal normal form for the D1 witness (HANDOFF, not a submission)

**Status (2026-10-06): stopped by the plan change to a single challenge `near-chunk-v3`
(statement Rel_D3α, declared-domain coverage).** The separate D1 reference was not finished as a
package; its **Lean development is complete and reusable** for the D3α reference
(`examples/reexec-v3-d3`, other agent). Only `formal/` and `judge-local/` are meaningful:
`build-recipe/`, `source/prover/ProveMain.lean` and `candidate.toml` are still the D0 copies
(not adapted), and `source/verifier/sync-vendor.sh` points at a formal-checker config that was
removed. `source/lean-vendor/` = trusted modules of the D1 closure at `04799708`.

## What is proved (`formal/ReexecV3D1/`, axioms ⊆ propext, Classical.choice, Quot.sound; no sorry / native_decide)

* `relDk_normal` (`NormalForm.lean`, here `relD1_normal`): every RelD1 witness has a normal-form
  RelD1 witness, no longer, = the prover's `normSW` output; `normalW_sound`, `normalW_fixed`:
  accepted proofs are fixed points of `normSW` / `normW`; `certificate` against the local
  emulation `judge-local/Expected.native.lean.template` (params = struct literal with
  `spec := NearSpecV3.challengeSpecD1`).
* Normal form of the D1 witness: zero `height_included` / signature / transition block hashes;
  receipt-proof entries deduplicated (last wins) and sorted by key (byte segments of the input);
  `base_state` values reduced to the relation's read set, deduplicated, sorted;
  `transactions` / `new_transactions` / `applied_receipts_hash` kept verbatim (their exact
  bytes are hashed by the relation: no freedom).
* Read set (D1): `qFor` over `[keyBufferedIdx] ++ mainKeys receipts bshards ++ txKeys w.txs`
  (`KeysD1.lean`, verbatim prefix of `checkD1`); implicit transitions as D0.
* Reusable for D3α: `CFTx.lean` — `cf_pTxD1` (context-freeness of the version-peeking
  transaction parser via `pTxD1_eq`/`txCore_cf`), `Cons` (minimum consumption), `cf3` tactic
  (`CF.lean`: bind/ite/split/pVec/pOption).

## Known residual freedom (not closed)

Values revealed by the builder but not read by the run: the per-key builder reveals the paths
of `txKeys` for *every* transaction, but the run reads a signer's account / access key only if
the transaction reaches steps 5/6 (nearcore: "prefetched only"); such nodes may be present or
absent. Closing it needs the exact read set of the runtime (an instrumented trie), not done.
