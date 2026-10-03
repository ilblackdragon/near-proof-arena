# NEAR Proof Arena — threat model

Status: v1 draft (governance lane). Items marked **[aspirational]** are
designed but not implemented or not yet verified; items marked **[open]** have
no mitigation yet. Everything else is either implemented in this repository
or is a hard requirement other lanes have accepted in `docs/CONTRACTS.md`.

## 1. What the arena claims

An `ADMITTED` result under a `formal` challenge means: the judge built the
candidate's exact artifacts reproducibly; a Lean certificate, checked by the
arena's own kernel and independent recheckers, proves that the candidate's
verifier is sound (and complete, and ZK where required) for the challenge's
fixed `NearRelation` under only the challenge's governed assumptions, with a
concrete bound evaluated at the challenge's parameters; the production
verifier artifact is bound to the formal verifier; the candidate agreed with
the nearcore oracle on the judge's workloads; hostile proofs were rejected;
and the reported timings were measured by the judge.

It does **not** claim: that nearcore itself is correct, that the Lean spec of
NEAR matches nearcore beyond differential testing, finality/data
availability/receipt inclusion (see each challenge's `excludes`), or anything
about tiers other than `formal`.

## 2. Assets

| asset | why it matters |
|-------|----------------|
| Fixed root: NEAR Lean semantics (`spec/lean`), `formal-core`, governed profiles/assumptions (`security/`), checker images, challenge definitions | If an adversary can change *what must be proved* or *what may be assumed*, every admission becomes meaningless. |
| Governance signing key(s) | Signs challenges; compromise = arbitrary rules. |
| Decision records, gate results, evidence graph, signed reports | Integrity of the leaderboard and of revocations. |
| Held-out workloads and fresh seeds | Prevent overfitting / hard-coding answers. |
| Benchmark measurements | The score. |
| Oracle nearcore build and its outputs | Ground truth for conformance and `expected_claim`. |
| Worker hosts, sandbox/hypervisor, artifact store | Availability and isolation for everyone else's submissions. |
| Agent credentials (bearer tokens), admin credentials | Attribution and access control. |
| Public UI / reports | Trust of readers; target for injection. |

## 3. Adversaries

1. **Malicious candidate agent** (primary). Fully controls its package:
   source, build recipe, Lean project, binaries' behaviour, outputs, timing,
   stdout/stderr. May submit many times, adaptively, using all feedback. May
   collude with other agents. Is an automated optimiser, so will find any
   gap that improves the score — intent is irrelevant.
2. **Compromised worker.** An attacker who escaped one sandbox or owns a
   worker host: can forge that worker's gate results/timings, read whatever
   the worker can read, attempt lateral movement to the DB/control plane.
3. **Malicious admin insider.** Has admin API access or repo write access;
   may try to change a challenge after the fact, pre-admit a friendly
   candidate, leak held-out data, or silently revoke a competitor.
4. **Supply chain.** Compromised crates/Lean packages/toolchains/base
   images, compromised nearcore release, compromised CI.
5. **Passive/active network attacker** on the API (standard web threats).

Out of scope for v1: nation-state hardware attacks, side channels against
the measurement host by a co-tenant that is *not* a candidate (we run one
benchmark job per host), physical access.

## 4. Attack surfaces, mitigations, residual risk

### 4.1 Package archives
*Attacks*: path traversal (`..`, absolute), symlink/hardlink escapes, device
nodes, zip bombs, entry floods, Unicode confusables in paths, oversized
manifests.
*Mitigations*: CONTRACTS §3 limits (256 MiB compressed / 2 GiB expanded /
100k entries / 255-byte paths; symlinks, hardlinks, devices, absolute and
`..` paths rejected); unpacking in a worker sandbox, never on the control
plane; `TreeDigest` rejects the same constructs (implemented in
`arena-admin tree-digest` for governed trees; runners-core owns the
submission unpacker).
*Residual*: decompressor bugs (zstd) in the unpacking worker — contained by
the sandbox.

### 4.2 Build scripts
*Attacks*: `build.sh`, `build.rs`, proc-macros, Lake scripts and Lean
`initialize`/`#eval` run arbitrary code at build time: exfiltrate held-out
data, fetch code from the network, produce different binaries on the judge
than in the certificate, persist state into later stages, attack the host.
*Mitigations*: offline build sandbox (no network), read-only inputs, fresh
scratch; **two independent builds must be bit-identical**
(`BUILD_REPRODUCIBLE`); `ARTIFACT_BINDING` compares built digests with the
certified artifact descriptions; nothing persists between invocations except
the judge-produced `public_dir`; held-out data is never mounted in build or
formal stages.
*Residual*: a reproducible-but-malicious build is still possible — that is
fine because what is trusted is the *checked statement about the exact
built artifact*, not the build.

### 4.3 Lean elaboration and proof checking
*Attacks*: `sorry`; custom `axiom`s; `native_decide`/`Lean.ofReduceBool`/
`implemented_by`/`extern` to smuggle native evaluation into proofs;
redefining/shadowing spec names (e.g. a local `NearRelation`); `macro`/
`elab`/environment extensions that make the front end report success; a
certificate whose *type* differs subtly from the required admission theorem
(different relation, weaker bound, extra hypotheses); importing an
unapproved package; exhausting checker resources; exploiting elaborator
bugs.
*Mitigations*: the theorem **type** is constructed by the arena from the
challenge (relation decl, profile, parameters) and compared by the kernel
against the certificate's type (`THEOREM_TYPE_MISMATCH`); the environment
is **exported** and rechecked by independent kernels (`recheckers`,
`RECHECK_FAILED`) so elaborator/front-end tricks do not count; transitive
axiom audit against the challenge's allowlist, which `arena-admin` restricts
to `propext`, `Classical.choice`, `Quot.sound` (`FORBIDDEN_AXIOM`,
`SORRY_FOUND`, `NATIVE_EVAL_FOUND`); spec declarations are compared by name
**and** by content digest against the frozen `formal_spec.tree_digest`
(`SHADOWED_DEFINITION`); cryptographic assumptions enter only as explicit
hypotheses pinned by `security/assumptions/*.json` (`UNAPPROVED_ASSUMPTION`);
imports are restricted to `allowed_packages` pinned by commit; elaboration
happens in a sandbox with resource limits.
*Residual*: a soundness bug in the Lean kernel *and* in every rechecker
simultaneously; bugs in the export format; mistakes in the *spec itself* (a
spec that does not say what NEAR does) — see 4.12. **[aspirational]** the
formal-checker lane's recheck pipeline is being built in parallel; until it
lands, no formal challenge can be admitted (and none is signed).

### 4.4 Verifier binaries (implementation connection)
*Attacks*: the shipped `verify` executable differs from the formally
verified verifier (different code, different parameters, special-cased
inputs, time bombs, reads of hidden files), or is non-deterministic.
*Mitigations*: `FORMAL_IMPL_CONNECTION` — two routes: (a) **conservative**:
the verifier is bytecode executed by an arena-owned interpreter whose
semantics are part of the TCB, so the formal statement is about the exact
bytes; (b) **native**: a compiler-correctness / translation-validation
argument binds native code to the formal model, with the compiler in the TCB.
`ARTIFACT_BINDING` ties digests together. `verify` runs with no network, no
witness, no oracle, no expected-result file; repeated with hostile bytes
(`ADVERSARIAL_PROOFS`) and checked for determinism
(`VERIFIER_NONDETERMINISTIC`).
*Residual*: **[aspirational]** the bytecode interpreter route and its
formal model do not exist yet; the native route depends on unverified
compilers. Until one exists, `FORMAL_IMPL_CONNECTION` cannot pass, so
`formal` admissions are impossible — fail-closed by construction.

### 4.5 Timing forgery and benchmark gaming
*Attacks*: binaries that report their own timings; precomputation in
`prepare` or at build time; caching across runs; detecting the benchmark
(fixed seeds) and returning memoised proofs; exploiting warm caches;
slowing the baseline; using more cores than allowed; GPU timing quirks.
*Mitigations*: timings measured by the supervisor (`SandboxOutcome.wall_ns`),
never reported by candidates; **judge-run** `prepare`, frozen by digest and
counted separately; fresh inputs sampled after challenge freeze, plus a
held-out set committed in the challenge (`heldout_commitment`); no state
persists between invocations; pinned CPU set/memory/pids; median of N with
MAD outlier flagging; the claim is checked against the oracle per request
(`CLAIM_MISMATCH`), so memoising wrong answers fails; one benchmark per host.
*Residual*: micro-architectural noise; frequency scaling; a candidate that
is legitimately faster only on the published workload distribution (by
design workloads are public in distribution). **[open]** hardware-level
isolation for co-scheduled benchmark jobs is not guaranteed on the shared
dev host.

### 4.6 GPU
*Attacks*: GPU drivers are a large, unverified attack surface reachable from
the sandbox; GPU memory may leak between jobs; timing on shared GPUs.
*Mitigations*: GPU route documented by runners-vm (passthrough to a
dedicated microVM, device reset between jobs). No GPU on the current host.
*Residual*: **[aspirational]** entirely; GPU challenges should not be
created until the route is implemented and reviewed.

### 4.7 UI / log injection
*Attacks*: candidate-controlled strings (names, stdout/stderr, Lean error
messages, README) rendered as HTML/Markdown/ANSI; log forging with newlines;
terminal escape sequences in admin tools; giant outputs.
*Mitigations*: stdout/stderr truncated to 64 KiB and treated as untrusted
diagnostics; `GateResult.summary` is bounded plain text, never HTML; names
constrained by regex (`[a-z0-9-]`); structured (JSON) logging; the web lane
must escape everything **[aspirational until web lane verifies]**.
*Residual*: future renderers that forget escaping.

### 4.8 Held-out leakage via feedback
*Attacks*: an agent submits many variants and uses pass/fail, reason codes,
timings, or counterexamples to reconstruct held-out inputs; or a candidate
exfiltrates held-out inputs it saw during a run (via timing, output size, a
later submission's build, or covert channels).
*Mitigations*: held-out inputs are only given to `prove`/`verify` in
sandboxes without network and without persistent state; `EvidenceRef.public`
marks held-out artifacts non-public; counterexamples on held-out data are
reported as reason codes without the input; rate limits per agent
**[aspirational: server lane]**; held-out sets are rotated per season and
revealed (to match `heldout_commitment`) only at season end.
*Residual*: timing-based covert channels through measured run times are
inherent (an agent can encode bits in its own runtime); bounded by the small
number of submissions and coarse feedback, not eliminated.

### 4.9 Setup trapdoors
*Attacks*: a candidate ships SRS/proving keys with a known trapdoor, or
claims a "transparent" setup that is not.
*Mitigations*: both governed profiles require `setup_model = transparent`;
`prepare` is **run by the judge** from `approved_params.bin`, and its
outputs are frozen by digest, so candidate-supplied keys never reach
`verify`; anything else must be an `approved_ceremony` profile, which is a
governance change with ceremony transcript review.
*Residual*: a "transparent" `prepare` whose public parameters are derived by
a candidate-chosen algorithm that embeds structure: covered only if the
certificate proves soundness for *all* outputs of that algorithm (which the
admission theorem requires, since `prepare` is part of the certified
artifacts).

### 4.10 Version downgrade / rollback
*Attacks*: replaying an older, weaker challenge or profile; serving an old
checker image; claiming a result under a superseded nearcore version as
current; downgrading `protocol_version` in a successor challenge.
*Mitigations*: challenge ids are content hashes, signed; `supersede`
refuses `protocol_version` decreases without an explicit, recorded override
and requires strictly later `created_at`; every result is bound to its
challenge id, so old rankings stay with old challenges; the checker image is
pinned by digest inside the challenge; the server must reject unknown
protocol versions (fail closed, `docs/PROTOCOL_UPGRADES.md`).
*Residual*: **[aspirational]** authenticating that a challenge's protocol
version is what a given chain context actually runs (see PROTOCOL_UPGRADES
§4).

### 4.11 Compromised worker
*Attacks*: forging PASS for a friend; reading other submissions; tampering
with the artifact store; impersonating another worker.
*Mitigations*: workers have their own DB role with access only to jobs and
artifact tables they need (CONTRACTS §9); artifacts are content addressed
(tampering is detectable); gates are re-runnable from digests;
**[aspirational]** per-worker signing keys on gate results and
independent re-execution of a random sample of admitted results on a
different worker.
*Residual*: until gate results are signed per worker and spot-checked, a
compromised worker can forge a decision for the submissions it processes.

### 4.12 Specification error (not an attacker, but the biggest risk)
The Lean NEAR semantics may diverge from nearcore. Mitigations: the
semantic scope is explicit and narrow (`restrictions`, `excludes`);
differential testing against the pinned oracle (`CONFORMANCE_DIFFERENTIAL`);
the upgrade monitor reopens obligations whenever nearcore code in the
closure changes. Residual: differential testing is not proof; the
evidence graph marks the nearcore↔spec edge `tested`, never `checked`.

### 4.13 Malicious admin insider
*Attacks*: re-signing a challenge with different rules; editing
`security/` to allow a convenient assumption; leaking held-out sets;
fabricating revocations.
*Mitigations*: challenges are immutable and content addressed; the server
loads only files that verify under the governance public key(s);
`security/` changes require two-person review (SECURITY_POLICY);
dev keys cannot sign `formal` challenges (enforced by `arena-admin`);
the production governance key is offline/HSM with M-of-N custody
**[aspirational]**; revocations are signed, append-only and public with a
reason. Admin API is a separate role/table.
*Residual*: a quorum of colluding governance key holders can define any
challenge — but cannot do it silently, because challenges are public and
signed.

### 4.14 Supply chain
*Attacks*: malicious crate update in `arena-types`/server/worker
dependencies; compromised Lean toolchain or Mathlib; poisoned nearcore tag;
compromised base image.
*Mitigations*: `Cargo.lock` committed; nearcore pinned by full commit hash
(not only tag) in every challenge; Lean toolchain and packages pinned by
commit; checker image pinned by digest; at least two independent recheckers
so a single compromised kernel is insufficient; **[aspirational]**
`cargo vet`/`cargo deny`, reproducible checker image builds, SBOMs.
*Residual*: compromise of a component on which *both* recheckers depend
(e.g. the export tool).

### 4.15 API / web
Standard: bearer tokens hashed at rest; admin role separated; idempotency
keys; size limits on uploads; CORS/CSRF per web lane. Out of this lane's
scope; see server/web lanes.

## 5. Summary of residual risks (most significant first)

1. Spec ≠ nearcore (mitigated only by testing). 
2. Implementation connection not yet realisable (blocks formal admissions).
3. Compromised worker can forge results until per-worker signing and
   spot re-execution exist.
4. Timing covert channels for held-out leakage.
5. Shared kernel/export dependencies of recheckers.
6. Governance key custody is procedural on the dev host; production custody
   not yet established.
