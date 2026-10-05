# Protocol upgrades

How the arena follows nearcore releases and NEAR protocol upgrades without
ever letting a result silently change meaning.

## 1. Invariants

1. A challenge pins **one** nearcore commit (`nearcore.commit`, full hash),
   one `protocol_version`, one `chain_id` and one `runtime_config_digest`.
   It never changes.
2. Every semantic change (anything that can alter `NearRelation`, the claim
   encoding, runtime parameters, or the oracle's outputs on the challenge
   scope) gets a **new challenge** that `supersedes` the old one.
3. Results are bound to the challenge id they were measured under.
   Historical rankings are preserved and displayed with that challenge;
   superseding never re-labels, re-scores or deletes them.
4. Unknown versions fail closed: the judge never evaluates a request,
   oracle output or chain context whose protocol version is not the
   challenge's.
5. "The old Lean proof still compiles" is never evidence that it still
   applies.
6. The trusted Lean base is frozen per challenge. `formal_spec.tree_digest`
   pins `formal-core/` + `spec/lean/`, and the judge builds the reference
   only from the frozen tree with that digest (docs/TCB.md §1a). Changes to
   those directories on `main` — new spec modules, new judge templates,
   `ArenaCore.SHA256Fast` for the ZK backend — take effect **only** through a
   new challenge that pins the new tree; existing challenges keep their tree
   forever.

## 2. Upgrade flow

```
new nearcore release / protocol version
        │
        ▼
1. fetch the new ref into a governance nearcore clone (pinned checkout is untouched)
2. tools/upgrade-monitor --old <challenge pin> --new <ref>         ──► report (JSON+MD)
        │  exit 0 NO_SEMANTIC_CHANGE_DETECTED   exit 3 REVALIDATION_REQUIRED   exit 2 error
        ▼
3. commit the report under docs/upgrade-reports/
4. if exit 0: optional — a new challenge is still required if the operator wants
   results to cite the new commit; otherwise the old challenge stays active.
   if exit 3/2: for each impacted rule (spec/impact-map.toml):
     a. spec lane updates spec/lean + claim encoding + fixtures (new tree digests)
     b. oracle lane rebuilds the oracle at the new commit; runs conformance
        of the *spec* against the new oracle
     c. formal-core / checker changes if any
5. governance drafts the successor ChallengeDefinition (new nearcore pin,
   protocol_version, runtime_config_digest, formal_spec digests, workloads,
   held-out commitment, created_at) and signs it:
     arena-admin supersede --old challenges/<old>.json --draft <new>.json …
   (rejects protocol_version downgrade and non-increasing created_at)
   and publishes the trusted tree it pins (formal_spec.tree_digest):
     arena-admin freeze-trusted --commit <freeze commit> --store <ARENA_TRUSTED_TREES> \
       --challenge challenges/<new>.json
   (refuses unless the commit's formal-core + spec/lean hash to the pin;
   registration in step 6 is refused until this is done)
6. announce a grace period; when it is over, register the successor
   (admin API or ARENA_CHALLENGES_DIR). Registration closes the old challenge
   for new submissions in the same transaction (`open = false`, audit event
   `challenge.superseded`); it stays verifiable, listed, and its board keeps
   its rankings, labelled `superseded_by`. It cannot be reopened (409
   `challenge_superseded`). Submissions already in flight finish under the
   old challenge.
7. candidates re-submit against the new challenge. Formal results are NOT
   carried over automatically — the judge's PROVER_ONLY cache key includes
   the challenge id, so every obligation is re-run.
```

The monitor exits non-zero whenever *anything* in the runtime closure
changed (files, external crate versions, parameters, protocol constants,
`ProtocolFeature` set, closure membership, parse failures). The impact
map only decides *which* obligations/spec definitions to look at first;
the default for an unmapped change is "everything semantic".

Sample: `docs/upgrade-reports/nearcore-2.13.3-to-2.13.4.md` shows that even a
patch release with an unchanged protocol version (86) modifies state
commitment code (`near-primitives` state parts, `near-store` trie), and
therefore requires revalidation.

## 3. Fail-closed handling of unknown versions

* The oracle is built from exactly `nearcore.commit`. Every oracle command
  takes `--challenge FILE` and refuses (exit 3) unless the challenge pins the
  oracle's nearcore commit, protocol version and chain id. `check-request`
  refuses a request whose embedded protocol version or chain id differs, and
  `replay` refuses to reproduce an expected claim for one.
* The worker pins every oracle request to the challenge
  (`RequestPin::from_challenge`: `near-arena-request-v1` header,
  `protocol_version`, `chain_id`). Conformance and benchmark jobs check every
  request before any candidate code runs. A mismatch fails the job as infra
  (judge-side), never as a candidate verdict.
* The claim encoding (`near-arena-claim-v1`) must include the protocol
  version and chain id in the claim, so a proof for one version can never
  be presented as a proof for another **[spec lane to confirm]**.
* The server refuses to load a challenge whose id/signature fails
  (re-verified on every read), and refuses submissions to a closed or
  superseded challenge (409 `challenge_closed`; for a superseded challenge the
  message names the successor).
* The upgrade monitor treats unparseable protocol facts, missing root
  crates, and git/cargo failures as REVALIDATION_REQUIRED (exit 2/3).

## 4. Authenticating the version against chain context

An admitted prover proves `NearRelation_v(c, w)` for the challenge's
version `v`. A *consumer* of such proofs (e.g. a light client) must know
that the chunk it is checking was produced under `v`:

* The claim binds `protocol_version` and `chain_id`; the consumer compares
  them with the epoch's protocol version from the block header / epoch info
  it already trusts. **[aspirational]** the arena does not verify finality,
  epoch transitions or header chains — `block_finality`,
  `receipt_inclusion` and `data_availability` are in every challenge's
  `excludes`.
* Upgrade boundaries: the first block of an epoch with a new protocol
  version must be proven under the successor challenge. Proofs straddling
  an upgrade boundary are out of scope for v1.
* The runtime config actually used on-chain at version `v` must equal the
  challenge's `runtime_config_digest`; the spec lane computes this from the
  pinned parameters YAML for the challenge's `chain_id` (mainnet and
  testnet differ: `parameters.yaml` vs `parameters_testnet.yaml`).

## 5. Historical rankings

* Leaderboards are per challenge id; `compute_leaderboard` only considers
  submissions of that id, so boards are never merged. Every entry carries
  `challenge_id`, `protocol_version` and, once superseded, `superseded_by`
  (`GET /v1/challenges/{id}` also carries `superseded_by`). Superseding
  never re-scores, re-ranks or deletes an entry, and signed reports are
  immutable.
* The web UI does not yet render a "superseded by chl_…" banner. The API
  data is there (`superseded_by` on challenges and entries), but the UI work
  is **[not implemented]**.
* Cross-version comparisons are not computed: different relations,
  parameters and workloads make scores incomparable.
* Revocations (SECURITY_POLICY §5) can still be applied to historical
  results, e.g. if a spec bug is found that also affected the old version.

## 6. Limitations

* The monitor's closure is a static over-approximation of crate
  dependencies; it does not trace `build.rs` file reads or non-literal
  `include!`s (see `tools/upgrade-monitor/README.md`).
* The initial impact map uses `concept:` placeholders until the spec lane
  names exact Lean declarations and fixture paths.
* No newer nearcore release than 2.13.4 exists at the time of writing; the
  committed reports therefore compare older tags *to* 2.13.4.
* There is no signed PV84 challenge. A formal PV84 challenge would need the
  spec, oracle and fixtures at nearcore 2.12.0, and none of these exist. The
  PV84 side of §7 is therefore the real monitor diff plus server-level
  fixtures. It is not a published board.
* The grace period is a governance procedure: the server closes the
  predecessor when the successor is registered.

## 7. Executed flow (2026-10-03)

### 7.1 Same protocol version, new baselines: v1 → v1.1

`chl_5ef2bc7d2068219635426e47ca46bfbb` (`near-transfer-receipt-v1`, PV 86)
was frozen with `baseline_submission = null` and `baseline_ns = []`.
Admissions were decided, but **every score was null**. Pinning baselines
changes the meaning of scores, so it requires a successor challenge
(invariant 2). No other field changes.

```sh
# 1. measure the reference candidate (examples/reexec-witness) through Firecracker
python3 benchmarks/baseline/run_baseline.py --challenge challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json \
  --package examples/reexec-witness --oracle oracle/target/debug/near-arena-oracle \
  --out benchmarks/results/baseline-near-transfer-receipt-v1-r1-devhost-20261003 --cpus 8-15
# 2. successor draft = v1 + baseline (+ name, supersedes, created_at); the script asserts nothing else changed
python3 benchmarks/baseline/pin_baseline.py --old challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json \
  --summary benchmarks/results/baseline-near-transfer-receipt-v1-r1-devhost-20261003/summary.json \
  --name near-transfer-receipt-v1-1 --created-at 2026-10-03T13:00:00Z \
  --out challenges/drafts/near-transfer-receipt-v1-1.draft.json
# 3. sign with the local operator key
target/debug/arena-admin supersede --old challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json \
  --draft challenges/drafts/near-transfer-receipt-v1-1.draft.json \
  --key /data/illia/nearproof-deps/keys/governance-local.key --pubkey challenges/governance-local.pub
#    -> chl_f7eb2d91bf7b363eee134b6ad9d3e011 supersedes chl_5ef2bc7d2068219635426e47ca46bfbb (old file retained)
target/debug/arena-admin verify --pubkey challenges/governance-local.pub --pubkey challenges/governance-dev.pub --all-in challenges
```

The new challenge is `chl_f7eb2d91bf7b363eee134b6ad9d3e011`. Its
`baseline_submission` is `sha256:329c763a92542052e1e2d69b6dc262446571acb1ab9ec50fd4caec170bcd699f`
(the `arena pack` digest of the reference package). Its `baseline_ns` are:

| class | `baseline_ns` |
|-------|---------------|
| batch-1 | 213 592 463 |
| batch-16 | 205 044 335 |
| batch-256 | 216 310 937 |

These are **dev-host** medians from a shared box, not a governed host. See
`benchmarks/results/baseline-near-transfer-receipt-v1-r1-devhost-20261003/README.md`.
Results submitted to v1 stay on v1's board. They are not re-scored against
these baselines.

### 7.2 A real protocol-version boundary: nearcore 2.12.0 / PV 84 → 2.13.4 / PV 86

`tools/upgrade-demo.sh` runs every step below and checks the exit codes.

1. **Monitor.** `upgrade-monitor --old 2.12.0 --new 2.13.4 --impact-map spec/impact-map.toml`
   exits 3 (`REVALIDATION_REQUIRED`). It reports 211 closure files, 20
   external crates, 7 parameter files, `STABLE_PROTOCOL_VERSION` 84 → 86, and
   18 features newly enabled at stable. The reports in `docs/upgrade-reports/`
   were regenerated with the current impact map. As a control,
   `--old 2.13.4 --new 2.13.4` exits 0.
2. **Impact on this challenge.** The relevant semantic change for the
   transfer slice is in `85.yaml`: `min_gas_purchase_price` goes from 0 to
   10⁹ yN/gas. Receipts then buy gas at ≥ 10⁹, so whenever
   `block_gas_price < gas_price` every transfer emits a gas-refund receipt
   and burns at the block price (docs/research/first-slice.md §4, "Tier B").
   This changes `tokens_burnt_total`, `refund_count` and
   `refund_receipts_commitment` in the claim, and the
   `runtime_config_digest`. The impact map routes it through rule
   `runtime-parameters` (`NearSpec.Params.*`,
   `NearSpec.TransferV1.applyReceipt`,
   `spec/challenge-inputs/runtime-config-pv86.json`), rule `protocol-version`
   (`NearSpec.Params.protocolVersion`, `DomainStatic`) and
   `receipt-processing` (`gasRefundReceipt`, `runBatch`, …). The obligations
   to reopen are `FORMAL_SEMANTIC_SOUNDNESS`, `FORMAL_SEMANTIC_COMPLETENESS`,
   `FORMAL_CRYPTO_SOUNDNESS`, `FORMAL_IMPL_CONNECTION`, `AXIOM_AUDIT`,
   `CONFORMANCE_DIFFERENTIAL`, `ADVERSARIAL_PROOFS`, `PROVER_RELIABILITY` and
   `BUILD_REPRODUCIBLE`. Every fixture must be regenerated. 54 changed inputs
   match no rule and get the fail-closed `[default]`.
3. **Fail closed.** The PV 86 oracle refuses a PV 84 variant of the challenge
   (exit 3). It refuses a request embedding protocol version 85 (the
   generator's `wrong_protocol_version` case) and accepts a PV 86 request. The
   worker's `RequestPin` unit test covers PV 85/87, another chain, another
   format and truncation.
4. **Server.** `server/arena-server/tests/supersession.rs` registers
   A = PV 84 (2.12.0) with a full pipeline run, two ranked formal results and
   an in-flight submission. It then registers B = PV 86 (2.13.4) with
   `supersedes = A` and checks:
   * A is closed and `superseded_by = B`, and its definition is untouched;
   * A's entries, ranks and signed reports are identical, now labelled
     (`challenge_id = A`, `protocol_version = 84`, `superseded_by = B`);
   * the in-flight submission is decided under A;
   * B's board starts empty and never contains A's results, and A's never
     contains B's;
   * a new submission to A gets 409 `challenge_closed` naming B, while B
     accepts it;
   * reopening A gets 409 `challenge_superseded`;
   * a revocation still applies to A's historical result, on A's board only;
   * the audit log records `challenge.superseded`.

   A second test registers the successor first and checks that the
   historical challenge is inserted closed.

```sh
tools/upgrade-demo.sh [OUT_DIR]      # needs the nearcore clone with both tags and the shared Postgres
```

### 7.3 Production checker pin + bench-spec-v1.1: v1.1 → v1.2

Integration found that v1 and v1.1 pin `toolchain_policy.checker_image` to
the identity of one host build of the checker tools. The production
Firecracker FORMAL_CHECK worker runs the digest-pinned lean-checker image,
whose tools report another identity. Formal gates therefore came out
UNKNOWN in production, and Milestone D passed only through a locally signed
successor. The checker pin and the procedure both change what a result
means, so the fix is a new successor, `near-transfer-receipt-v1-2`
(`chl_3be93793610370275ae40f36a475f01f`, supersedes `chl_f7eb…`):

* `checker_image = sha256:b6391b3899df90e2557924ae7b67f0c07456fa20d41f6bbf383220a311d15b1e`.
  This is `formal-check --print-image-digest` with the tools of lean-checker
  image `sha256:d85133a1…`, the image the worker selects (the newest
  installed one). The older image `sha256:706f29e0…` carries an
  `arena-audit` whose tools key does not match the current checker, so it
  is not usable.
* `measurement.invocation_mode = vm_per_batch` (BENCHMARK_SPEC §4.4).
* A new baseline measured with that procedure through Firecracker, on an
  unsigned pre-baseline draft. `pin_baseline.py --base` fills in only the
  baseline and refuses a session whose calibration failed.

```sh
python3 benchmarks/baseline/run_baseline.py --challenge challenges/drafts/near-transfer-receipt-v1-2.measure.json \
  --package examples/reexec-witness --oracle oracle/target/debug/near-arena-oracle \
  --fc-deps /data/illia/nearproof-deps/firecracker-rc --cpus 4,5,6,7,20,21,22,23 --out <results>
python3 benchmarks/baseline/pin_baseline.py --base challenges/drafts/near-transfer-receipt-v1-2.measure.json \
  --summary <results>/summary.json --out challenges/drafts/near-transfer-receipt-v1-2.draft.json
target/debug/arena-admin supersede --old challenges/chl_f7eb2d91bf7b363eee134b6ad9d3e011.json \
  --draft challenges/drafts/near-transfer-receipt-v1-2.draft.json \
  --key /data/illia/nearproof-deps/keys/governance-local.key --pubkey challenges/governance-local.pub
```

The formal-check configuration `runners/formal-checker/challenges/near-transfer-receipt-v1.json`
lists `near-transfer-receipt-v1-1` and `-v1-2` as `aliases`. Their formal
semantics are unchanged, and without the aliases the worker found no formal
configuration, so every formal gate was UNKNOWN.

`tests/e2e/milestone-d.sh` now runs against the signed v1.2 itself. It
signs a local successor only if the pinned checker identity differs from
the worker's. Results: `docs/e2e-results/milestone-d-v1-2/`.

### 7.4 Trusted trees frozen per challenge (2026-10-05)

The judge used to build the trusted reference from the checkout it was
deployed from; HEAD's `formal-core/` + `spec/lean/` no longer hashed to the
NEAR challenges' `formal_spec.tree_digest` (`sha256:8090432a…`). Since this
change the reference is built only from the frozen tree the challenge pins
(invariant 6, docs/TCB.md §1a):

```sh
arena-admin freeze-trusted --commit 6873c9980fd93c0483e93b94fe7e8a1fe0d52d52 \
  --store /data/illia/nearproof-live/trusted-trees \
  --challenge challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json   # (+ v1-1, v1-2, v1-3, chl_b7c8…)
# -> sha256:8090432a8236d8a8cacada10c257f83575f6c0ec480a40659d6af023ff39c611
```

Re-running the v1-3 admissions (docs/LIVE.md §5a): the npai-v1 entry is
still ADMITTED; the two native-lean entries are INFRA_ERROR because the
native-lean Expected template is not part of the v1 family's pinned tree.
`ArenaCore.SHA256Fast` (ZK backend) and the spec v2 modules likewise take
effect only for a challenge that pins a tree containing them.

### 7.5 Native-lean template pinned: v1-3 → v1-4, experimental successor (2026-10-05)

**Why.** §7.4 showed that the v1 family's frozen tree (`6873c99`,
`sha256:8090432a…`) predates `spec/lean/judge/Expected.native-lean.lean.template`
(added in `6b9d74c`). The native-lean admissions on v1-2/v1-3 were therefore
judged against a statement their challenge never pinned, and under the pin
they fail as INFRA_ERROR. Governance decision (lead, under the local
operator authority used for v1-1…v1-3): sign successors that pin a tree
containing the template, with the v1 semantics unchanged.

**Tree.** `formal-core/` + `spec/lean/` at `cf5f1f5` (the commit that
signed v1-3): `sha256:190e9a7d210c7a9086d1b0e3fc1c754bc72ea684b2113fbadfebfb13241fd111`
(`arena-admin tree-digest` of `git archive cf5f1f5 -- formal-core spec/lean`
and `spec/tools/tree_digest.py spec/lean formal-core` on a `cf5f1f5`
checkout agree). Relative to `6873c99`, `git diff --name-status` shows:

* added: the native-lean judge templates (`Expected.native-lean`,
  `ExpectedV2`, `ExpectedV2.native-lean`), the spec v2 modules
  (`TrieUpsert*`, `Bandwidth`, `TransferV2*`, `ClaimCodecV2`, `CodecV2`,
  `ChallengeV2`, `ExamplesV2`, `Examples/V2*`), `scripts/gen_example_v2.py`;
* modified, tooling only: `formal-core/InterpRef.lean` (a `batch` mode of
  the reference interpreter CLI), `spec/lean/Main.lean` (the
  `nearspec-check` CLI also decodes v2), `spec/lean/NearSpec.lean` (root
  imports of the v2 modules);
* unchanged: every module the v1 statement uses (`ArenaCore.*`,
  `NearSpec.TransferV1`, `Challenge`, `ClaimCodec`, `Trie`, `Outcome`, …)
  and `Expected.lean.template`. `ArenaCore.SHA256Fast` is **not** in it
  (added later for the ZK backend).

**Challenges** (`arena-admin supersede`, key
`/data/illia/nearproof-deps/keys/governance-local.key`), each identical to
its predecessor except `formal_spec.tree_digest`, `supersedes`,
`created_at` (and `name` for v1-4):

* `chl_f3903307cb9b064d75b35b6af461a0dc` `near-transfer-receipt-v1-4`
  (formal) supersedes v1-3 `chl_fefb…`; v1-3's baseline and measurement
  config are kept.
* `chl_df55f9f7fc94060fdfd6bfeeb1c79c1f` (experimental, name unchanged
  `near-transfer-receipt-v1-2`) supersedes `chl_b7c8…`; still no baseline.

The formal config `near-transfer-receipt-v1.json` lists v1-4 as an alias.
The trusted tree was published with `arena-live freeze-trusted cf5f1f5 …`
before registration.

**Experimental FORMAL_CHECK failures.** On an experimental challenge every
FORMAL_CHECK gate is diagnostic, but a FORMAL_CHECK *job* that failed for
good used to decide the whole run INFRA_ERROR. The control plane now records
those gates UNKNOWN / `INFRA_ERROR` (with the error) and continues to
conformance, adversarial and benchmark; formal tier is unchanged.

### 7.6 Security fix R-L7-5 (csimp audit): v1-4 → v1-5, experimental successor (2026-10-05)

**Vulnerability.** The formal checker audited only the certificate's
dependency closure. A native-lean candidate could add
`@[csimp] theorem check_eq : @check = @acceptAll := sorry` to its verifier
model: the certificate (about `check`) stays sorry-free, but the Lean
compiler applies csimp lemmas, so the **judge-built** native verifier ran
`acceptAll` and accepted garbage. Every challenge whose checker identity
predates the fix (v1…v1-4, the experimental `chl_b7c8…`/`chl_df55…`) is
exposed for the native-lean route.

**Fix** (main `5fa43e9`, lane/fc-csimp): candidate `@[csimp]` lemmas are
audited (exported by their escaped names) and the axiom audit covers the
whole candidate environment, not only the certificate's closure. The fix
lives in `ArenaAudit`, so the lean-checker image changes and with it the
checker identity:

* lean-checker image `sha256:463fdcf45f8818606dc4379d3ba6983ae7187fa83c7592ad175f7b137b16d6fe`
  (`deploy/images/lean-checker/build.sh` from main, installed in
  `/data/illia/nearproof-deps/lean-checker/images-csimp`);
* checker identity (`formal-check --print-image-digest` with that image's
  tools) `sha256:66b014d4e05744bcf21771c469f93d119a0d24a5dc4288d28cb46126c4bf1867`
  (was `sha256:b6391b38…`).

**Challenges** (local operator key), identical to their predecessors except
`toolchain_policy.checker_image`, `supersedes`, `created_at` (and `name` for
v1-5); the trusted tree stays `sha256:190e9a7d…` (cf5f1f5):

* `chl_17ac2f309f490da391081806645b795a` `near-transfer-receipt-v1-5`
  (formal) supersedes v1-4 `chl_f3903307…`;
* `chl_0d36946f05e7e0989f881aa8d8f8fc61` (experimental) supersedes
  `chl_df55…`.

A worker whose checker identity differs from a challenge's pin reports
every formal gate UNKNOWN, so after the image switch v1-4 can no longer be
evaluated and is closed by the v1-5 registration (its board stays as
history). The hostile case `adversarial/hostile-submissions/near-reexec-csimp-sorry`
is the regression check: it must be REJECTED (`SORRY_FOUND`).
