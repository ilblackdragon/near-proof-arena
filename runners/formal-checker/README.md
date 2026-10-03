# formal-checker

Decides the formal gates of a submission — `FORMAL_SEMANTIC_SOUNDNESS`,
`FORMAL_SEMANTIC_COMPLETENESS`, `FORMAL_CRYPTO_SOUNDNESS`,
`FORMAL_IMPL_CONNECTION` and `AXIOM_AUDIT` — for a candidate Lean project
(`formal/` in the package) whose certificate constant (`[formal].certificate`
in `candidate.toml`) must have **exactly** the judge-constructed admission
statement as its type.

Crate: `arena-formal-checker` (library + `formal-check` CLI). Judge-owned
Lean helper: `lean/ArenaAudit` (`arena-audit`).

## Toolchain (one config value)

`lean-toolchain` in this directory is the only toolchain setting
(`leanprover/lean4:v4.34.1`, same as formal-core). The judge reference build,
sandboxed candidate elaboration, `leanchecker`, `lean4export`, `lean4lean`
and `arena-audit` all use it. Helper tool revisions are pinned in
`tools.toml`. Install/build everything with:

```sh
runners/formal-checker/scripts/setup-tools.sh   # elan toolchain + tools into $ARENA_FC_HOME
```

Layout (content-addressed): `$ARENA_FC_HOME/<toolchain>/<tools-key>/bin/{lean4export,nanoda_bin,lean4lean,arena-audit}`,
where `<tools-key>` = 16 hex of sha256 over the files in `TOOLS_KEY_FILES`
(toolchain, `tools.toml`, the setup script, the ArenaAudit sources). Checkouts at
different revisions therefore never share or overwrite helpers. The key is
also baked into `arena-audit` (`arena-audit version`); `ToolPaths::discover`
refuses (`ToolError::Mismatch`) any helper whose baked key differs from the
key computed from this checker's embedded sources — a stale or foreign helper
is an explicit error, never silently used. A unit test keeps the Rust and
shell key computations in sync.
(default `ARENA_FC_HOME=~/.cache/arena-formal-checker`; per-tool overrides
`ARENA_LEAN_SYSROOT`, `ARENA_LEAN4EXPORT`, `ARENA_NANODA`, `ARENA_LEAN4LEAN`,
`ARENA_AUDIT_BIN`). Changing the toolchain = edit `lean-toolchain`, re-pin
`tools.toml` if needed, rerun the script.

## Pipeline

Everything that touches candidate content runs through the `UntrustedRunner`
seam (`src/sandbox.rs`; same shape as the workspace `Sandbox` trait: RO
mounts, one scratch dir, fixed env, no network, wall timeout, supervisor-side
measurement). `SandboxRunner` adapts it to the shared runner sandbox
(`arena_sandbox::Sandbox`): `bwrap-dev` in development (refused unless
`ARENA_DEV_UNSAFE=1`; reports carry `tier_cap = demo`; `.olean` output dirs
are read-write binds, so their content is treated as hostile afterwards) and
`firecracker` in production once that backend supports read-write output
directories (`GuestLayout::rw_binds`; it is refused until then). The
`formal-check` binary doubles as the sandbox helper
(`formal-check __arena-sandbox-helper ...`).

0. **Reference build** (judge-only content, cached by content digest):
   trusted packages (formal-core, challenge spec; `TrustedPackage` +
   `include` prefixes) and the judge-generated `Expected` module are compiled
   with plain `lean` in judge-computed import order. `arena-audit list-trusted`
   lists every trusted constant; `lean4export` exports those + the expected
   declaration + the allowlisted axioms → `reference.ndjson`. The expected
   module is rendered from a template + typed data (`ExpectedTypeBuilder`,
   `TemplateExpected`; values are spliced only as Lean *literals* — `Nat`,
   string, digest string, byte list — never as syntax).
1. **Stage A — untrusted elaboration.** Static, in Rust: walk `formal/`
   (symlinks/devices rejected), take only `.lean` sources; ignore (warn)
   prebuilt `.olean`/`.lake`/native files and the candidate `lean-toolchain`
   / manifest; **never run the candidate lakefile** — it is only parsed to
   reject forbidden features (`extern_lib`, `script`, `target`, `lean_exe`,
   `moreLeanArgs`/`weakLeanArgs`/server args, `plugins`, `dynlibs`,
   `precompileModules`, link args, `--load-dynlib`/`--plugin`, non-allowlisted
   `require`, unknown keys, non-cosmetic `leanOptions`) → `MANIFEST_INVALID`.
   Candidate module names inside judge-owned names (trusted modules, the
   Expected module, `ArenaAudit`, policy prefixes such as `ArenaCore`,
   toolchain `Init/Std/Lean/Lake`) → `SHADOWED_DEFINITION`. Imports must
   resolve to candidate/trusted/toolchain modules; `prelude` refused. Then
   each module is elaborated offline with `lean -o` in its own sandbox run:
   sources RO, the judge's trusted `.olean`s exposed read-only (symlinks into
   an RO mount so trusted and candidate modules can share a namespace root),
   one RW output dir. Tactics, macros, `#eval`, `initialize` all run here and
   are untrusted; nothing they print or write is ever read as a verdict.
2. **Stage B — clean recheck** (fresh sandboxes; never loads candidate
   plugins, no initializer execution): a *fresh* replay dir holds only the
   candidate modules' `.olean` files (regular files only; links planted by
   the build → `SANDBOX_VIOLATION`) plus links to the pristine trusted ones.
   * `leanchecker` (Lean kernel replay of every candidate module, built into
     the toolchain — the maintained successor of `lean4checker`);
   * `lean4lean` (independent kernel implementation in Lean, `.olean` replay);
   * `lean4export … -- <certificate>` → NDJSON of the certificate's
     dependency closure, then `nanoda_bin` (independent Rust kernel) on it.
   Any rejection → `RECHECK_FAILED`; required recheckers
   (`Policy.required_recheckers`, default `leanchecker`+`nanoda`) that did
   not run → `UNKNOWN`.
3. **Stage C — judge checks**, done twice from independent representations:
   * `arena-audit check` (`lean/ArenaAudit`): imports the Expected module
     and the candidate modules *together* (collisions = shadowing) and uses
     the Environment API: certificate exists and lives in a candidate module;
     its type (universe params instantiated positionally, `mdata` stripped)
     is `==` the expected value — or is literally the judge's
     `ArenaExpected.expectedType` constant; no defeq/unfolding of candidate
     definitions; transitive closure + axioms; every constant of the
     statement comes from trusted/toolchain modules; candidate declarations
     with `@[implemented_by]`, `@[extern]`, `[init]`/`initialize`, `unsafe`
     → `NATIVE_EVAL_FOUND` (the auto-generated pair of a `partial def` is
     exempt); candidate `opaque`/`partial` in the certified closure →
     `UNAPPROVED_ASSUMPTION`.
   * **NDJSON audit** (`src/ndjson.rs`, `src/audit.rs`), on the very export
     nanoda accepted — never maps an `.olean`: strict parser (backward-only
     indices, no duplicates, size cap) + Merkle hashes ignoring binder
     names/info, `mdata` and reducibility hints. Checks structural equality
     of the certificate type with the reference statement; every reference
     declaration present in the candidate export is hash-identical (incl. the
     allowlisted axioms' types) else `SHADOWED_DEFINITION`; the statement's
     reference closure must be present; axiom closure classified:
     allowlisted → ok, `sorryAx` → `SORRY_FOUND`, `Lean.ofReduceBool` /
     `ofReduceNat` / `trustCompiler` / `*._native.*` (Lean ≥4.2x emits one aux
     axiom per `native_decide`) → `NATIVE_EVAL_FOUND`, axioms of trusted
     modules not approved by the challenge → `UNAPPROVED_ASSUMPTION`, anything
     else → `FORBIDDEN_AXIOM`; unsafe/partial in the closure →
     `UNAPPROVED_ASSUMPTION`. Reports the closure (name, kind, decl hash) and
     its digest.
   * The two audits must agree on statement equality and the axiom set,
     else `RECHECK_FAILED`.
4. **Output** (`FormalCheckReport`): `Vec<GateResult>` (FAIL dominates
   UNKNOWN dominates PASS; timeouts and infra problems are `UNKNOWN`, never
   PASS), findings with reason codes, recheckers run and verdicts, the
   closure report, evidence refs (export/olean/audit/closure digests), an
   `EvidenceGraph` fragment (certificate —proves→ statement, —assumes→
   axioms, —rechecked_by→ each checker, statement —defined_in→ trusted
   packages), timings, and `cache_key` = digest of {checker version,
   toolchain, checker image (dev: digest of all tool binaries + pins),
   formal tree digest, trusted tree digests, rendered Expected source,
   certificate name, challenge digest, policy}.
5. Source grep (`src/grep.rs`: sorry/axiom/native_decide/implemented_by/
   extern/unsafe/partial/skipKernelTC/#eval/...) only produces warnings.

### `native-lean` verifier route (candidate model inside the statement)

For `verify_route = "native-lean"` (`formal.verifier_model` +
`verifier_model_module`, `VerifierRoute::NativeLean`):

1. The Expected template defines the statement as a **function of the model**
   (`ArenaExpected.expectedTypeFor (model : OracleVerifier) : Prop`, e.g.
   `spec/lean/judge/Expected.native-lean.lean.template`), so the trusted
   reference build and export stay candidate-free.
2. Stage A0: the model module and its candidate imports are compiled first,
   each in its own sandbox run with only its own output dir writable, against
   the trusted build only. Model-closure modules may import only trusted
   modules, other model modules and `Init` (no `Lean`/`Std`/`Lake`: no
   metaprogram can rewrite the IR behind the kernel definition).
3. Judge build of `verify`: trusted C from the judge-only trusted build,
   model C from step 2, a judge-owned `main` wrapper (`native.rs`,
   CONTRACTS §4 CLI, `pub = public_dir/public.bin`) elaborated with the model
   in scope **and** against a judge stub axiom of the same name/type — the two
   elaborations must be identical (catches candidate macros/notation/instances
   hijacking the wrapper) — then `leanc` compile + link in judge-only runs.
   The binary is reproducible (same digest across runs).
4. The statement is rendered with `{{bin_digest}}` = sha256 of that binary and
   `{{toolchain_id}}`, and instantiated at the model in a judge-generated
   module `ArenaExpectedInst` (`def ArenaExpectedInst.expectedType : Prop :=
   ArenaExpected.expectedTypeFor Candidate.Model.verify`), compiled in the
   sandbox; candidates may state the certificate as that constant, the literal
   application, or its beta-reduced form (checked syntactically on both the
   Lean and the NDJSON side, the latter by hashing the lambda body with the
   model substituted).
5. Audit: the model's dependency closure is the only untrusted content allowed
   in the statement and is held to the certificate's standard (axiom
   allowlist; no sorry / native_decide / partial / opaque / unsafe / extern /
   implemented_by / initialize; must be a `def` in the declared candidate
   module; redefining trusted names → `SHADOWED_DEFINITION`).
6. Gates: an `ARTIFACT_BINDING` gate is added. It passes only when the
   executed verifier is this judge build; a candidate-supplied binary with a
   different digest, a candidate-built native verifier without a model
   (`VerifierRoute::CandidateNative`), a missing model, a model that does not
   build, or a hijacked wrapper → `ARTIFACT_BINDING_FAILED`.
7. Evidence graph: `formal:verifier_model` (`backend_semantics`, digest = model
   closure digest), `statement —contains_candidate_model→ model`,
   `certificate —proves_obligations_about→ model` (checked),
   `artifact:verifier_binary —implements→ model` (**trusted**) and
   `—built_from→ tcb:lean_compiler_runtime`. The report carries
   `native_verifier {path, digest, toolchain_id}` for the worker to run.

Tests: `tests/native_route.rs` (in-repo formal-core Toy): positive (the judge
binary accepts a valid toy claim and rejects an invalid one), model with
sorry / candidate axiom / native_decide / shadowed `ArenaCore.OracleVerifier`
/ missing decl / macro hijacking `OracleVerifier.deployed` / `import Lean`,
foreign candidate binary, candidate-native route. `tests/near_spec.rs`
(`FC_NEAR_SPEC=1`) also builds the NEAR native-lean statement.

### Per-conjunct gates

If `Policy.conjunct_gates` is set and the statement is a right-nested
conjunction whose proof term is an `And.intro` chain, axioms are attributed
per conjunct (e.g. a `sorry` only in the crypto conjunct fails only
`FORMAL_CRYPTO_SOUNDNESS` + `AXIOM_AUDIT`). Otherwise (e.g. formal-core's
existential `AdmissionStatement`) every finding applies to all formal gates.
`AXIOM_AUDIT` fails whenever there is no valid certificate to audit.

### Reason codes used

`CERTIFICATE_MISSING`, `THEOREM_TYPE_MISMATCH`, `FORBIDDEN_AXIOM`,
`SORRY_FOUND`, `NATIVE_EVAL_FOUND`, `SHADOWED_DEFINITION`, `RECHECK_FAILED`,
`UNAPPROVED_ASSUMPTION`, plus `MANIFEST_INVALID` (lakefile/manifest policy),
`ARCHIVE_UNSAFE`, `BUILD_FAILED` (always with `CERTIFICATE_MISSING`),
`SANDBOX_VIOLATION`, `TIMEOUT` and `INFRA_ERROR` (both `UNKNOWN`).

## Usage

```rust
let runner = SandboxRunner::new(Arc::new(sandbox), work_root)?; // any arena_sandbox::Sandbox
let checker = FormalChecker::new(ToolPaths::discover()?, Box::new(runner));
let report = checker.check(&CheckRequest { formal_dir, certificate, trusted, expected: &tmpl,
    challenge_digest, policy, limits, work_dir, cache_dir });
```

CLI: `formal-check --formal DIR --certificate NAME --trusted NAME=DIR[@Prefix,...]
--expected expected.json [--policy policy.json] [--out report.json]`.

## Tests

```sh
cargo test -p arena-formal-checker                       # unit tests; corpus SKIPs
ARENA_DEV_UNSAFE=1 cargo test -p arena-formal-checker -- --nocapture   # + real corpus
ARENA_DEV_UNSAFE=1 FC_FORMAL_CORE_DIR=<formal-core dir> \
  cargo test -p arena-formal-checker --test formal_core -- --nocapture
```

`tests/corpus/<case>/{formal/,expect.json}` against the stand-in trusted
package `tests/fixtures/standin` (`ArenaStandIn.AdmissionStatement`, a
4-conjunct toy) and `tests/fixtures/expected.json`. 30 cases: 4 positive
(plain, multi-module + allowlisted require + foreign lean-toolchain, stated
via `ArenaExpected.expectedType`, custom `elab` tactic) and 26 negative
(sorry; per-conjunct sorry; `axiom : False`; certificate-is-axiom;
unapproved trusted assumption; native_decide; wrong type; wrong params;
defeq-but-not-syntactic; extra `(h : False)`; missing; build error; shipped
altered trusted module; re-declared trusted names; prebuilt `.olean`;
lakefile.lean `extern_lib`+`script`; lakefile.toml `--load-dynlib`/
`precompileModules`/`plugins`/foreign require; `implemented_by`; `@[extern]`;
`unsafe def`; `partial def` in path; `#eval` fake-PASS writer; `initialize`;
`debug.skipKernelTC` ill-typed theorem; non-terminating elaboration →
UNKNOWN; file named like the Expected module). The harness also asserts the
judge's reference `.olean` tree is byte-identical after all cases and that no
fake PASS file reached the host. Typical wall time: ~3–5 s per case,
~20 s for the corpus with 6 parallel jobs.

`tests/formal_core.rs` runs formal-core's real `ArenaCore` + Toy certificate
(PASS), a stale-digest judge (FAIL), and every `negative/*.lean` of
formal-core as `Candidate.lean`, matching their `-- EXPECT:` lines.

## Known gaps

* Dev sandbox only: no memory/disk quotas beyond `RLIMIT_FSIZE` (Lean's
  thread stacks break `RLIMIT_AS`); production isolation is the firecracker
  runner behind `UntrustedRunner`.
* Trusted packages are compiled with plain `lean` (no Lake): fine for
  dependency-free formal-core; Mathlib-style dependencies would need a
  judge-side Lake build producing the RO olean root.
* Lean `module`-system candidates cannot import non-`module` trusted files
  (Lean rule); formal-core decides.
* `lean4lean` builds against v4.34.1 only with the bumped batteries pin; if
  a future toolchain breaks it, it is reported `not_run` (not required by
  default).
* `nanoda_bin` is run with `unsafe_permit_all_axioms` (pure kernel check);
  axiom policy is enforced by the audits.
* Result caching by `cache_key` is left to the worker (`reused_from`).
* native-lean: the binary↔model edge trusts the Lean compiler/runtime (by
  design) and the wrapper-equality check runs in an audit process that maps
  candidate `.olean`s (sandboxed, like the rest of the Lean-side audit).
  Model-closure modules cannot use `Lean` metaprogramming, but compiler
  attributes on candidate declarations are only rejected by the audit after
  the build (the build output is never admitted in that case).
