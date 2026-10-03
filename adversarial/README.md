# Adversarial lane — attacking the judge

This lane is the judge's red team. It ships a permanent suite of **hostile
submissions**, hostile **proof-byte mutators**, **mutation-testing** definitions
for the reference backends, and an **e2e driver** that submits everything to a
running server and asserts the judge does the right thing. The one invariant
behind all of it:

> **No hostile submission is ever `ADMITTED`, `accepted`, scored or ranked.**
> Every case is REJECTED (or, where noted, INCONCLUSIVE) with a specific failing
> gate and reason code, and the judge reaches that verdict *itself* — never by
> trusting anything the candidate says, prints, or writes.

Contracts (`docs/CONTRACTS.md`): gates/obligations §6, reason codes §6, pipeline
and decision rule §7, archive/package rules §3, sandbox interface §9.

## Layout

| path | what |
|------|------|
| `hostile-submissions/` | complete candidate packages, each with `expect.json` |
| `hostile-submissions/generate.py` | source of truth that materializes the packages |
| `proof-mutators/` | Rust crate: hostile proof-byte generators + suite loader (workspace member) |
| `mutants/` | judge-owned source-mutation operators + report format for reference backends |
| `e2e/run.sh`, `e2e/run_hostile.py` | the driver (`make e2e-hostile` entry point) |

## 1. Hostile submissions (`hostile-submissions/`)

Each case is a real candidate package (`candidate.toml`, `source/`, `formal/`,
`build-recipe/build.sh`, `README.md`) plus an **`expect.json`** stating the
expected decision, failing gate(s), reason code(s), the stage it should fail by,
the outcomes that must never occur, and **why** it is hostile. `generate.py` is
the source of truth (`python3 generate.py` to rebuild, `--check` for staleness);
the materialized packages are committed so they are inspectable and the e2e
driver needs no Python package beyond the stdlib.

Build recipes are tiny `/bin/sh` + C, compiled offline with `cc`. **Build-image
assumptions:** no network, `cc` and `/bin/sh` present, read-only bundle, writable
scratch. Nothing is vendored or fetched.

Archive-attack cases are different: the hostile payload is the **archive
encoding** (symlink, `../` traversal, hardlink, device node, decompression
bomb), which a normal directory cannot represent, so those cases ship a
`make-archive.sh` that emits the malicious tar, and the directory itself is a
well-formed placeholder. The e2e driver uploads the builder's output for them.

### Case list (33 cases, 15 families)

Generated from the `expect.json` files; regenerate the packages with
`generate.py` if you change them.

#### Certificate / formal attacks

| case | decision | failing gate(s) | reason code(s) |
|------|----------|-----------------|----------------|
| `always-accept-verifier` | REJECTED | ADVERSARIAL_PROOFS | HOSTILE_PROOF_ACCEPTED |
| `always-reject-verifier` | REJECTED | PROVER_RELIABILITY | PROVER_FAILED |
| `weak-public-input-binding` | REJECTED | ADVERSARIAL_PROOFS | HOSTILE_PROOF_ACCEPTED |
| `malicious-executable` | REJECTED | ARTIFACT_BINDING | ARTIFACT_BINDING_FAILED |
| `wrong-verification-key` | REJECTED | ARTIFACT_BINDING | ARTIFACT_BINDING_FAILED |
| `stale-certificate` | REJECTED | ARTIFACT_BINDING | ARTIFACT_BINDING_FAILED (packaging kill) |
| `restricted-domain` | REJECTED | FORMAL_SEMANTIC_SOUNDNESS | THEOREM_TYPE_MISMATCH |
| `false-premise` | REJECTED | FORMAL_SEMANTIC_SOUNDNESS | THEOREM_TYPE_MISMATCH |
| `missing-certificate` | REJECTED | FORMAL_SEMANTIC_SOUNDNESS | CERTIFICATE_MISSING |
| `additional-axiom` | REJECTED | AXIOM_AUDIT | FORBIDDEN_AXIOM |
| `shadowed-definition` | REJECTED | AXIOM_AUDIT | SHADOWED_DEFINITION |
| `sorry-certificate` | REJECTED | AXIOM_AUDIT | SORRY_FOUND |
| `native-decide-certificate` | REJECTED | AXIOM_AUDIT | NATIVE_EVAL_FOUND |
| `changed-security-parameters` | REJECTED | FORMAL_CRYPTO_SOUNDNESS | SECURITY_BOUND_INSUFFICIENT |

#### Runtime / execution attacks

| case | decision | failing gate(s) | reason code(s) |
|------|----------|-----------------|----------------|
| `forged-pass-output` | REJECTED | FORMAL_SEMANTIC_SOUNDNESS | CERTIFICATE_MISSING |
| `benchmark-shortcut` | REJECTED | CONFORMANCE_DIFFERENTIAL | CLAIM_MISMATCH |
| `precomputed-fixture-table` | REJECTED | CONFORMANCE_DIFFERENTIAL | CLAIM_MISMATCH |
| `background-daemon` | REJECTED | PROVER_RELIABILITY | PROVER_FAILED |
| `sandbox-escape-filesystem` | REJECTED | PROVER_RELIABILITY | SANDBOX_VIOLATION |
| `sandbox-escape-network` | REJECTED | PROVER_RELIABILITY | SANDBOX_VIOLATION |
| `sandbox-fork-bomb` | REJECTED | RESOURCE_LIMITS | RESOURCE_LIMIT |
| `sandbox-ptrace-proc` | REJECTED | PROVER_RELIABILITY | SANDBOX_VIOLATION |
| `forged-timing` | REJECTED | BENCHMARK | SANDBOX_VIOLATION |
| `ui-injection-logs` | REJECTED | ADVERSARIAL_PROOFS | HOSTILE_PROOF_ACCEPTED |
| `ui-injection-manifest` | REJECTED | PKG_WELLFORMED | MANIFEST_INVALID |

#### Build / archive attacks

| case | decision | failing gate(s) | reason code(s) |
|------|----------|-----------------|----------------|
| `build-network-fetch` | REJECTED | BUILD_REPRODUCIBLE | BUILD_FAILED |
| `build-nonreproducible` | REJECTED | BUILD_REPRODUCIBLE | BUILD_NOT_REPRODUCIBLE |
| `build-dependency-substitution` | REJECTED | ARTIFACT_BINDING | ARTIFACT_BINDING_FAILED |
| `archive-zip-slip` | REJECTED | PKG_WELLFORMED | ARCHIVE_UNSAFE |
| `archive-symlink-escape` | REJECTED | PKG_WELLFORMED | ARCHIVE_UNSAFE |
| `archive-hardlink` | REJECTED | PKG_WELLFORMED | ARCHIVE_UNSAFE |
| `archive-device-file` | REJECTED | PKG_WELLFORMED | ARCHIVE_UNSAFE |
| `archive-bomb` | REJECTED | PKG_WELLFORMED | ARCHIVE_UNSAFE |

Per-case rationale lives in each case's `README.md` and `expect.json` `why`.

The gate a case is attributed to may vary slightly with the judge's
implementation (e.g. a sandbox violation surfaced under `PROVER_RELIABILITY` vs
`BENCHMARK` depending on which stage ran the binary). The e2e driver therefore
matches on three things together: decision, **at least one** expected gate
FAILed, and **all** expected reason codes present somewhere in the report.

## 2. Proof mutators (`proof-mutators/`)

A Rust crate of hostile proof-byte generators that feed the `ADVERSARIAL_PROOFS`
gate — beyond the generic byte fuzzers a runner applies by default. Interface:

```rust
trait Mutator {
    fn name(&self) -> &str;
    fn describe(&self) -> &str;
    fn mutate(&self, honest: &[u8], claim: &[u8], ctx: &MutationCtx, rng: &mut Rng)
        -> Vec<MutatedProof>;
}
```

Mutators are generic over an opaque byte format via `FormatHints` (commitment
offsets, length prefixes, NEAR trie-witness node boundaries, transcript/domain
regions); with no hints they fall back to inference. Families: malformed
lengths, noncanonical encodings, altered commitments, truncated Merkle paths,
swapped siblings, duplicated nodes, extension/branch node-type confusion,
transcript tamper, domain separation, mismatched context, recursive proof
substitution, plus empty/truncate/extend/bitflip.

Every mutant carries a **kill classification** and **explain-evidence**:

- `Packaging` — rejection about form (length, truncation, canonicality, **stale
  digests**). A packaging kill demonstrates input validation, **not** soundness.
- `Binding` — a real/valid proof bound to a different claim/context/challenge.
- `Semantic` — the committed values are internally inconsistent (flipped root,
  swapped siblings). Only a semantic kill speaks to the verifier checking the
  relation.

The arena must never report a packaging kill (e.g. a stale-digest failure) as if
it were a semantic-soundness result — the types make the distinction explicit.

`cargo run -p proof-mutators --bin dump-mutants` prints a sample set.

## 3. Mutation testing (`mutants/`)

Judge-owned source-mutation operators (generic + `reexec-merkle`-specific) to be
applied by the integrator once reference backends exist under `examples/`, with
an equivalence policy (correct optimizations are expected to survive) and a
report format whose schema hard-codes: **gate-coverage ratio is not formal
correctness**. See `mutants/README.md`.

## 4. End-to-end (`e2e/`)

`e2e/run.sh` is the `make e2e-hostile` entry point. It runs the Rust suite
well-formedness check, then the Python driver `run_hostile.py`:

- `--dry-run` (default with no server): package every case, build malicious
  archives, validate every `expect.json`. No network.
- `--server URL --token T [--challenge chl_...]`: upload + submit each case,
  poll to a terminal decision, and assert decision / gate / reason codes match
  `expect.json`; assert nothing is admitted, accepted, scored, or present on the
  leaderboard; and assert `ui-log-injection` cases come back with no raw control
  characters.

## Local status (pre-integration)

Runs green now, with no server:

- `cargo test -p proof-mutators` — mutator unit tests (classification,
  determinism, inference fallback, panic-freedom) and suite well-formedness.
- `cargo run -p proof-mutators --bin check-suite` — all 33 packages load, parse,
  and agree with `expect.json`.
- `python3 e2e/run_hostile.py --dry-run` — all 33 packages tar/build (including
  the malicious archives) and every `expect.json` validates.
- All hostile C sources compile offline with `cc`; all `build.sh` /
  `make-archive.sh` pass `sh -n`.

Pending integration (needs other lanes): the full live e2e against the server
(`--server`), and wiring `mutants/` once a reference backend lands under
`examples/`.
