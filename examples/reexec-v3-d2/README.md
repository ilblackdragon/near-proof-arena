# reexec-v3-d2 — formal normal form for the D2 witness (HANDOFF, not a submission)

**Status (2026-10-06): stopped by the plan change to a single challenge `near-chunk-v3`
(statement Rel_D3α, declared-domain coverage).** The separate D2 reference was not finished as a
package; its **Lean development is complete and reusable** for the D3α reference
(`examples/reexec-v3-d3`, other agent). Only `formal/` and `judge-local/` are meaningful:
`build-recipe/`, `source/prover/ProveMain.lean` and `candidate.toml` are still the D0 copies
(not adapted), and `source/verifier/sync-vendor.sh` points at a formal-checker config that was
removed. `source/lean-vendor/` = trusted modules of the D2 closure at `04799708`.

## What is proved (`formal/ReexecV3D2/`, axioms ⊆ propext, Classical.choice, Quot.sound; no sorry / native_decide)

* `relDk_normal` (`NormalForm.lean`, here `relD2_normal`): every RelD2 witness has a normal-form
  RelD2 witness, no longer, = the prover's `normSW` output; `normalW_sound`, `normalW_fixed`:
  accepted proofs are fixed points of `normSW` / `normW`; `certificate` against the local
  emulation `judge-local/Expected.native.lean.template` (params = struct literal with
  `spec := NearSpecV3.challengeSpecD2`).
* Normal form of the D2 witness: zero `height_included` / signature / transition block hashes;
  receipt-proof entries deduplicated (last wins) and sorted by key (byte segments of the input);
  `base_state` values reduced to the relation's read set, deduplicated, sorted;
  `transactions` / `new_transactions` / `applied_receipts_hash` kept verbatim (their exact
  bytes are hashed by the relation: no freedom).
* Read set (D2): `qAll` = every hash `NearSpecV3.D2.revealAll` passes to `hGet` from the
  pre-state root (`KeysD2.lean`, verbatim prefix of `checkD2`) / from the previous post-state
  root for implicit transitions; `normValsH` keeps the `mkHStore` answers (last value per hash).
* Reusable for D3α:
  * `CFD2.lean`: context-freeness of every D2 witness parser — `cf_pRcpt`, `cf_pActionR`,
    `cf_pAct` (incl. delegate actions recording consumed bytes, via `pAct_eq`/`delRel_rel`),
    `cf_pBaseAct`, `cf_pTxD2` (version peek, `txCore2_rel`), `cf_pEntryD2`.
  * `TrieQ.lean`: `get?_insert`, `hGet_mkHStore` (last value wins), `hGet_normValsH`,
    `revealAll_agree`, `qAll_agree`.
  * `StoreCong.lean`: `applyNewChunkD2_store` — with `d2Hooks` the runtime never reads
    `Env.store`. **For D3α this does NOT hold** (the FunctionCall hook reads code via
    `Env.codeOf` = `hGet env.store`); there the normal form must keep the code blobs the run
    looks up and the congruence must be "stores agree on every `codeOf` query", proved through
    the D3 hook.
  * `Normal.lean`: the lockstep `checkD2_normal` / `keysD2_normal` (handles the
    `Scheduler.Params.calculate` match and the env-store rewrite).

## Known residual freedom (not closed)

`revealAll` reveals the whole recorded trie reachable from the root, so a reachable node the
run never reads may be present or absent (both accepted by nearcore and by Rel_D2). Closing it
needs the runtime's exact read set (instrumented trie operations), not done.
