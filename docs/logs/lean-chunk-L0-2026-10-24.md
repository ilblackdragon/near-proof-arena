# L0 lane log — 2026-10-24 — W00 successor API published

Package: **W00 Boundary inventory and successor API** (workplan
[`../requirements/LEAN_CHUNK_COMPLETION_WORKPLAN.md`](../requirements/LEAN_CHUNK_COMPLETION_WORKPLAN.md)
§"W00 Boundary inventory and successor API").
Lane **L0**, integration owner for the successor API.

Acceptance state: **ready for integration** (not "integrated", not "validated on the frozen package").
The API compiles and its axiom closure is clean; it has **no differential evidence** and **one
verification-integrity discrepancy** (§6) that the integration owner must decide.

## 1. Exact tip and provenance

| | |
|---|---|
| worktree | `/data/illia/nearproof-wt/lean-chunk-L0` |
| branch | `lane/lean-chunk-L0` |
| base tip | `46ddb874692225cbafdd7bc5cac9baa3834ae2b6` (`46ddb8746`, "handover: correct "merged" to "fully merged", and record what is not") |
| working-tree change | **untracked additions only**; zero modified tracked files |
| nearcore | `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4) |
| protocol version | 86 |
| Lean toolchain | `lean-toolchain` in `spec/lean/v3` (unchanged) |

Verified with `git status --porcelain`: the only entries are
`?? docs/research/lean-chunk-w00-owner-map.md`, `?? spec/lean/v3/NearSpecV3/Successor.lean`,
`?? spec/lean/v3/NearSpecV3/Successor/`. Every file the hard constraints protect is byte-identical to
the base tip (`git diff --quiet HEAD -- <file>` for each of `ChunkValidationD2.lean`,
`D3/FunctionCall.lean`, `Wasm/Exec.lean`, `Wasm/Host.lean`, `D2/Types.lean`, `NearSpecV3.lean`,
`lakefile.toml`).

### Artifact hashes (sha256)

Lean sources:

| file | sha256 |
|---|---|
| `NearSpecV3/Successor.lean` | `2f271057f3dc8ac6b3e3adc9ba7896746964a7530537d1d731ec8609e8fd82c9` |
| `NearSpecV3/Successor/Config.lean` | `6edb25e902239abfe5bf151cfdb8fc40f2cb8051a3321909bf4e3fd363128ff1` |
| `NearSpecV3/Successor/HostDispatch.lean` | `a6f839d1c4d06148ad65fcb4b0514db3bacbed989909c3b4ffd259ba8cdb7a8e` |
| `NearSpecV3/Successor/ActionsReceipts.lean` | `773c948028367dddbd32ce6ba193ef17a5501d6821785839c4aecc78b1847f27` |
| `NearSpecV3/Successor/Resolution.lean` | `01cc6fbf5d26a01f9ac7a8e425671bc68801b64978f8ccd83c0a3be72f2518c0` |
| `NearSpecV3/Successor/TrieRecorder.lean` | `fff623b2e6f7d64be647b68d8891e3b7d391452a215ca22369a4a071f00fb6a0` |
| `NearSpecV3/Successor/BoundaryFacts.lean` | `be37c3fa450ee0f12f61f9311e8550e8070829c8c219545e38deab5fa101a535` |
| `NearSpecV3/Successor/Differential.lean` | `bcaccab6e0f9fa00133e1ccd912650a9bd9dd532fd15199bbfd8f98c875a67b6` |

Built `.olean` artifacts (from the green `lake build NearSpecV3.Successor`):

| artifact | sha256 |
|---|---|
| `NearSpecV3/Successor.olean` | `75294ebae64f894425304d02f9ed943754cfb74843089f1ca07a9065323242c3` |
| `NearSpecV3/Successor/Config.olean` | `1178df4ef578bca6da0343f761db5ecd53f2b0a1db08fda2528d35d8b388cfca` |
| `NearSpecV3/Successor/HostDispatch.olean` | `b31ca32d11db6a21f932c6f339b340ac2683c4f7ed10d5311e7b9f91c5fee240` |
| `NearSpecV3/Successor/ActionsReceipts.olean` | `df0759e6c795d94a2cbf261f9a8dd8c675949fb94b136632164f6dcba1f7ac65` |
| `NearSpecV3/Successor/Resolution.olean` | `f3ec5535465117a85a46fca8fc61cac7664ece92b1ad244fad0464de848e5392` |
| `NearSpecV3/Successor/TrieRecorder.olean` | `b92d5a94f6b21f651b729d95bdbc19e503004ea42756281f040fcf5d10d8c612` |
| `NearSpecV3/Successor/BoundaryFacts.olean` | `9443bbf58963e8350b2eed856a255e4e1c7fcfffcd9e6773f9ce65c33ac0fd7e` |
| `NearSpecV3/Successor/Differential.olean` | `99e7d9ffcfe3eada1642e6e77c09acb2ee6f626d7f5ba23f6733ec3ab9f1bcbb` |

Module line counts: `Successor.lean` 155, `Config.lean` 296, `HostDispatch.lean` 264,
`ActionsReceipts.lean` 388, `Resolution.lean` 257, `TrieRecorder.lean` 212, `BoundaryFacts.lean` 288,
`Differential.lean` 331 — **2,191 lines** total across eight new files.

## 2. What compiles and what does not

### Compiles (green, verified this session)

| command | result |
|---|---|
| `lake build NearSpecV3.Successor` | **exit 0**, "Build completed successfully (96 jobs)" |
| `lake build NearSpecV3.Successor.<M>` (all seven) | exit 0 each |
| `lake build NearSpecV3` | exit 0, 91 jobs (the signed root module's closure; does **not** include Successor) |
| `lake build` (default targets) | exit 0, 184 jobs — **but see §6: this does not compile the new modules** |
| `make pin-check` | **exit 0** (all oracle-pin lines `ok`) |
| `python3 tools/d3/lean_chunk_coverage.py --repo . --nearcore /data/illia/nearproof-deps/nearcore --check docs/research/lean-chunk-coverage.json` | **exit 0**, "Lean chunk coverage matches pinned sources (research evidence only)" |

The drift-check invocation was read from the script's own `argparse`
(`tools/d3/lean_chunk_coverage.py:548-560`): `--repo` and `--nearcore` are **required**, and exactly one
of `--output`/`--check` is required. The flags are not guessed; they are the script's declared options.

### Does not compile

Nothing in the eight modules. There are **no** build errors and **no** `sorry`/`admit`/`native_decide`
tactic terms. Remaining warnings in the build log come from pre-existing files
(`D2/Types.lean:330` unused variable, `Wasm/Host.lean:225` deprecated `List.asString`,
`Secp256k1.lean:264,266` deprecated `if_pos`, `D3/GlobalContract.lean:334` unused `chainId`), not from
the new modules. The new modules emit no warnings.

## 3. Success criteria — passed and open

The workplan lists four W00 criteria. Status against each:

| # | Criterion | Status | Evidence |
|---|---|---|---|
| 1 | Every inventory row and UQ has an owner, disposition, source justification and test obligation; unknown answers explicitly open and block Gate B | **PASSED for owner + disposition; test obligations carried from the generated inventory** | `docs/research/lean-chunk-w00-owner-map.md` §2 (28 rows) and §3 (17 UQs); generated JSON unchanged |
| 2 | API contracts written and compile with existing float/gas/genesis adapters | **PASSED for the seven signatures; PARTIAL for verification reach** | 96-job green build; §6 records that the default target does not include them |
| 3 | Schema decision: which claim fields suffice, which need a versioned extension, how external facts authenticate; no computed result admitted as a fact | **PASSED as a decision document** | owner map §4; `BoundaryFact.kind`/`stateRoot_computed` prove computed outputs are labelled computed; no schema change made |
| 4 | Inventory drift check passes, IDs unique, static vs evidence distinguished, no relabelling | **PASSED** | `--check` exit 0; no row status edited; JSON not rewritten; `git status` shows JSON unmodified |

Criteria 1 and 3 are documentation/decision criteria and are met by the owner map. Criterion 2 is met at
the module level but **not** at the default-build level (§6). Criterion 4 is met and independently
re-verified.

### Open items that block Gate B (all owned, none closed here)

Gate B cannot close while any UQ in the owner map §3 is open. This work **closes no UQ**. Specifically
still open and blocking: `UQ-001`…`UQ-017`, all 17. The ones this work newly *surfaces in Lean* (without
deciding) are `UQ-001`, `UQ-002`, `UQ-004`, `UQ-005`, `UQ-006`, `UQ-007`, `UQ-008`, `UQ-009`, `UQ-010`,
`UQ-011`, `UQ-012`, `UQ-013`, `UQ-014`, `UQ-015`, `UQ-016`, `UQ-017`.

## 4. Residual premises — every one, by module

The successor API publishes contracts; it does not prove semantics. Each module's docstring records its
own premises. Consolidated:

### `Successor/Config.lean`

1. `checkD3GProtoFloat` (genesis + floats + protocol-gas composition) has **no differential evidence**.
   It is a composition of two adapters (`checkD2CoreG` and the float `NearCfg`), not a validated checker.
   W12 must not admit it as accepted without W13 replay.
2. No theorem states any successor tier agrees with nearcore. Agreement is W13/W14's obligation.
3. `checkSuccessor` is a dispatch table over configurations, **not** proved to be a refinement of
   `RelD3`. Refinement is W12's obligation.
4. `Tier.domainPredicate` is stated on the *verdict*: the declared domain is "everything the tier
   decides". It is **not** proved equal to `Wasm.DomainD3`'s predicates (`UQ-010`). W00's stated
   resolution of *which* predicate is the statement of record — `checkD3`/`RelD3`, with sources — is in
   the owner map §3.1; the reconciliation of `DomainD3` itself stays L1's open decision.

### `Successor/HostDispatch.lean`

5. The successor table is *additive naming*: `successorTable` extends `hostCall` with the crypto table
   and is proved to agree with `hostCall` wherever `hostCall` is defined
   (`successorTable_extends_hostCall`) and to fall through otherwise
   (`successorTable_fallsThrough`). It does **not** prove the crypto host semantics correct.
6. `HostContract.gasOrder` / `errorClass` are **declarations**, not theorems about the underlying host
   implementations. `UQ-004` (curve gas schedules) and `UQ-014` (Wasmtime error branches) stay open.
7. 14 curve hosts are named in `unimplementedHosts` with owners but have no semantics at all.

### `Successor/ActionsReceipts.lean`

8. `pActV` decodes tags 9/10/11 and delegates the rest to `D2.pAct`; the tag-9/10/11 branches are proved
   to reach the `L4` decoders (`pActV_tag9/10/11`). **No** whole-chunk *execution* semantics for those
   actions exists — the rows `L0-action-09/10/11` remain `missing` for execution.
9. `GcdBody`/`DistReceipt` **represent** distribution receipts; whether such a receipt can appear in a
   chunk witness at PV86 is `UQ-006` and stays open. No round-trip decode/encode theorem is proved for
   the full body (only `distReceipt_encode_layout`, a layout fact).
10. `KeyForm` represents the ML-DSA-65 full key and handle; whether the handle is part of the pinned
    claim/trie model is `UQ-005`, open. `KeyForm.wf` is a length check only; no borsh round-trip theorem.
11. The rollback structure is typed; its interaction with the real `ReceiptManager` (`UQ-016`) is not
    proved.

### `Successor/Resolution.lean`

12. `ResolutionEnv` types resolution and deploy tracking against the existing `Ovl`/`Rci`; **no**
    theorem proves `resolveCodeHash` agrees with `contract_code.rs`'s `RuntimeContractIdentifier::resolve`.
13. `ethWallet_kind_unreachable` states the *kind* is unreachable for the global path; it does not prove
    the wallet-hash enumeration `UQ-007` asks for.
14. `coldCache_independent` / `validatorCache_not_independent` are field facts. The substantive claim
    (`UQ-001`: is cold-cache the admitted statement?) is not decided.
15. `validatorCache_not_admitted` documents that a validator cache breaks cache-independence; it is not a
    proof that a specific corpus case is misclassified.

### `Successor/TrieRecorder.lean`

16. `RecorderOps` is a **structure of operations** with a contract, not a re-implementation of the trie.
    `trieRecorderOps` supplies the existing `RealStore` functions; agreement with nearcore's trie is not
    proved here.
17. `recorder_size_record_ge` proves the recorder size never shrinks on a record. The *soundness* of
    `Σ|values| + 2000·R ≤ 4 000 000` as an upper bound (`UQ-015`) is not proved — only the monotonicity.
18. `rollbackEffects_keeps_recorder` proves a rollback keeps the recorder; it does not prove the rest of
    the store state after a rollback matches nearcore's.

### `Successor/BoundaryFacts.lean`

19. `BoundaryFact.obligation` assigns obligation ids; **no** admission contract is proved to bind them
    (`UQ-013`).
20. `BoundaryInputs.ofClaim` projects existing claim fields; the versioned extensions of §4.2 are named,
    not added. `EpochInputs.layoutsOf` and `splitGatesOf` are list projections, not a layout-transition
    model (`UQ-008`).
21. `ShapeExclusion.removedBy` maps exclusions to owners; it is a *declaration* that the named package
    removes the exclusion, not a proof that it does.

### `Successor/Differential.lean`

22. `DiffResult.compare` is the comparison *algebra*; it does not run a checker or read a corpus. The
    cases and the replay are W13/W14's.
23. `Observable.agree` is field-wise and supplied-field-set-sensitive; agreement is proved reflexive but
    **not** transitive across different supplied-field sets. No lane may assume transitivity.
24. `DiffSummary.allAgree` requires zero disagreements and zero invalid cases; it does **not** require a
    minimum agreement count, so a run of zero cases would trivially `allAgree`. `summarise_complete`
    supplies the denominator (`accounted = length`), but a caller must pass the *read* case count, not
    the compared count, to make the denominator honest. That discipline is W13's, not enforced by type.
25. Which observable fields are required per case family is W13's provenance decision; no field is
    mandatory here.

### `Successor.lean` (aggregator)

26. `signedExclusions` has ten entries and is proved complete and duplicate-free
    (`signedExclusions_covers`, `signedExclusions_features`), and every owner in it matches
    `ShapeExclusion.removedBy` (`signedExclusions_owner_consistent`). It does **not** claim the later
    tiers remove exactly those; that mapping is W12's.
27. The aggregator adds no semantics and removes none.

## 5. New reachable paths and their fixtures

This work adds **no** executable path in the signed checker: it is additive types and proofs only. There
is therefore no new whole-chunk fixture for it, positive or negative. The paths it *names* are the
successor's future paths; their fixtures are the obligations listed in owner map §2–§3:

| Named path | Positive fixture owed | Negative fixture owed | Owner |
|---|---|---|---|
| action tag 9 (`ActV.deployGlobal`) | 1 valid whole-chunk | 1 invalid whole-chunk | L4 |
| action tag 10 (`ActV.useGlobal`) | 1 valid whole-chunk | 1 invalid whole-chunk | L4 |
| action tag 11 (`ActV.stateInit`) | 1 valid whole-chunk | 1 invalid whole-chunk | L4 |
| 14 curve hosts | positive/negative host vector + exact gas in a real chunk | same | L3 |
| `ecrecover`, `p256_verify` | host vector + gas | host vector | L3 |
| genesis main transition | genesis B2 with nonempty witness | genesis header negative | L6 |
| resharding | validator fixture crossing a real layout boundary | — | L6 |
| ETH-wallet resolution | replay `d3.call_eth_implicit_local` with wallet hash enumerated | — | L4 |
| global-contract resolution | replay `UseGlobalContract`/`GlobalByAccount` | — | L4 |
| code-cache narrowing | split 279 cases by committed vs rolled-back; replay cold validator | — | L1 |

**None of these fixtures exists yet.** Recording them as owed is the honest state.

## 6. Verification-integrity discrepancy — the default build does not cover these modules

This is the one finding the integration owner must act on, and it is the reason criterion 2 is "partial"
rather than "passed".

### The discrepancy

`spec/lean/v3/lakefile.toml` sets
`defaultTargets = ["NearSpecV3", "nearspec-v3-check", "nearspec-v3-leaftest"]`. The first entry resolves
to the **module** `NearSpecV3.lean`, whose transitive import closure is 74 modules and does **not**
include `NearSpecV3.Successor`. Consequently:

* `lake build` reports **184 jobs** both before and after the eight modules were added — the count is
  identical because the new modules are not in the default target's closure;
* **injected-error test A**: appending `#check thisDoesNotExistAtAll_xyz` to
  `NearSpecV3/Successor/Differential.lean` and running `lake build` exited **0** with "Build completed
  successfully (184 jobs)";
* **injected-error test B**: the same injection in `NearSpecV3/Successor/Config.lean` also exited **0**;
* **olean-deletion test**: deleting `NearSpecV3/Successor/Config.olean` (and `.ilean`) and running
  `lake build` did **not** regenerate them; running `lake build NearSpecV3.Successor` did.

Both files were restored to their hashed state after each test (§1 hashes are post-restoration).

### Why this is not caused by this work

45 of the 119 library modules have no `.olean` under the default build, before and after this work.
`GenesisD3.lean`, `ReshardingD3.lean`, `ChallengeD2.lean` and 42 others are in the same position. The
default target has always been the signed root's closure, not the library's module set. The new modules
inherit that pattern; they do not create it. But the workplan's verification step says "`lake build`
(must be green)" — and green does not mean these modules were checked. That gap must be stated, not
papered over.

### Exact edit needed (W00 does not make it)

`spec/lean/v3/lakefile.toml` is integration-owner territory per the hard constraints. The narrowest edit
that makes the default build cover the successor:

```toml
defaultTargets = ["NearSpecV3", "NearSpecV3.Successor", "nearspec-v3-check", "nearspec-v3-leaftest"]
```

The alternative — `import NearSpecV3.Successor` in `NearSpecV3.lean` — also works but puts the successor
in the signed root's closure, which the hard constraints discourage and which would make every signed
root build depend on successor modules. **Recommendation: the `defaultTargets` edit.**

Until that edit lands, the verification command for these modules is:

```
cd spec/lean/v3 && lake build NearSpecV3.Successor
```

## 7. Interface changes requiring other lanes to rebase or regenerate evidence

| Interface | Change | Who is affected |
|---|---|---|
| new module `NearSpecV3.Successor` + seven submodules | additive only; no existing file edited | no lane must rebase; lanes W02–W14 may import `NearSpecV3.Successor` |
| `checkD3`, `RelD3`, `gAlpha`, `DomainD3`, oracle pins | **unchanged** | none |
| `docs/research/lean-chunk-coverage.json` | **unchanged** (drift check green) | none |
| `lakefile.toml` | **unchanged** (proposed edit in §6 not applied) | integration owner must decide |

No other lane needs to regenerate evidence because of this work. The API is purely additive and every
protected file is byte-identical to the base tip.

## 8. Next executable step

1. **Integration owner** decides the `defaultTargets` edit in §6. This is the only blocker to criterion 2
   being fully "passed". It is a one-line change in a protected file.
2. **L4** closes execution for action tags 9/10/11 (decoders exist) and the global/ETH-wallet resolution
   rows (`L0-D3-006`, `L0-D3-008`).
3. **L3** closes the 14 unimplemented curve hosts and validates `ecrecover`/`p256_verify`.
4. **L1/L5/L6/L9** discharge the proof/decision UQs per owner map §3.
5. **W13/W14** consume `Differential.DiffResult`/`DiffSummary` so a lane cannot report agreement with a
   skipped or invalid case.

### Safe files to edit next

* `spec/lean/v3/NearSpecV3/Successor/*.lean` and `Successor.lean` — W00-owned; additive edits are safe.
* `docs/research/lean-chunk-w00-owner-map.md`, `docs/logs/lean-chunk-L0-2026-10-24.md` — documentation.
* **Not safe without the integration owner**: `lakefile.toml`, `NearSpecV3.lean`, `checkD3`,
  `D3/FunctionCall.lean`, `Wasm/Exec.lean`, `Wasm/Host.lean`, `D2/Types.lean`,
  `ChunkValidationD2.lean`.

### Unresolved discrepancies beyond §6

* The owner map's §2 row counts quote the generated inventory's `owner` field, but several rows list
  multiple owners (`L0-D2-040` = "L5 | L7", `L0-D2-015` = "L1" twice in its dependency column). The
  generated JSON is authoritative; this document does not re-assign owners. If the inventory's
  multi-owner notation is itself a defect, that is an inventory-generator question for L0/L1, not a
  W00 API question.
* `Differential.Observable.agree` is not transitive across differing supplied-field sets. This is by
  design (an under-recorded case must not compare equal to a well-recorded one), but it means a lane
  cannot build an equivalence-class argument on it. If W13 needs transitivity, W13 must supply the
  canonical-field discipline; the type does not.

## 9. Verification commands run this session (exact)

```
cd spec/lean/v3 && lake build NearSpecV3.Successor        # exit 0, 96 jobs
cd spec/lean/v3 && lake build NearSpecV3                  # exit 0, 91 jobs (signed root closure)
cd spec/lean/v3 && lake build                             # exit 0, 184 jobs (does NOT reach Successor; §6)
cd spec/lean/v3 && lake build NearSpecV3.Successor.<M>    # exit 0 per module
cd spec/lean/v3 && lake build NearSpecV3.Examples.RealCase # exit 0, 29 jobs (pre-existing module sanity)
cd repo root && make pin-check                             # exit 0
cd repo root && python3 tools/d3/lean_chunk_coverage.py --repo . \
    --nearcore /data/illia/nearproof-deps/nearcore \
    --check docs/research/lean-chunk-coverage.json         # exit 0
```

Axiom closure: every `#print axioms` check point in the eight modules reports a subset of
`{propext, Classical.choice, Quot.sound}`. Zero `sorryAx`. Zero custom axioms. Twenty-one declarations
are printed across the eight modules, distributed as: **5 with no axioms**
(`ActionTag.ofCode_code`, `distReceipt_encode_layout`, `coldCache_lookup_none`, `permanentExclusions_eq`,
`signedExclusions_covers`), **3 with `[propext]` only** (`pActV_tag9`, `ethWallet_kind_unreachable`,
`signedExclusions_owner_consistent`), **1 with `[propext, Quot.sound]`** (`summarise_complete`), and
**12 with `Classical.choice`** as well. 5 + 3 + 1 + 12 = 21.
