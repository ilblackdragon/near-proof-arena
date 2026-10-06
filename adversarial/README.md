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
`make-archive.py` that emits the malicious tar, and the directory itself is a
well-formed placeholder. The e2e driver uploads the builder's output for them.

### Case list (35 cases, 15 families)

Generated from the `expect.json` files; regenerate the packages with
`generate.py` if you change them.

#### Certificate / formal attacks

| case | decision | failing gate(s) | reason code(s) |
|------|----------|-----------------|----------------|
| `always-accept-verifier` | REJECTED | ADVERSARIAL_PROOFS | HOSTILE_PROOF_ACCEPTED |
| `always-reject-verifier` | REJECTED | PROVER_RELIABILITY | PROVER_FAILED |
| `weak-public-input-binding` | REJECTED | ADVERSARIAL_PROOFS | HOSTILE_PROOF_ACCEPTED |
| `malicious-executable` | REJECTED | ARTIFACT_BINDING | ARTIFACT_BINDING_FAILED |
| `wrong-verification-key` | REJECTED | ARTIFACT_BINDING | ARTIFACT_BINDING_FAILED, THEOREM_TYPE_MISMATCH |
| `stale-certificate` | REJECTED | ARTIFACT_BINDING | ARTIFACT_BINDING_FAILED, THEOREM_TYPE_MISMATCH (packaging kill) |
| `restricted-domain` | REJECTED | FORMAL_SEMANTIC_SOUNDNESS | THEOREM_TYPE_MISMATCH |
| `false-premise` | REJECTED | FORMAL_SEMANTIC_SOUNDNESS | THEOREM_TYPE_MISMATCH |
| `missing-certificate` | REJECTED | FORMAL_SEMANTIC_SOUNDNESS | CERTIFICATE_MISSING |
| `additional-axiom` | REJECTED | AXIOM_AUDIT | FORBIDDEN_AXIOM |
| `shadowed-definition` | REJECTED | AXIOM_AUDIT | SHADOWED_DEFINITION |
| `sorry-certificate` | REJECTED | AXIOM_AUDIT | SORRY_FOUND |
| `native-decide-certificate` | REJECTED | AXIOM_AUDIT | NATIVE_EVAL_FOUND |
| `changed-security-parameters` | REJECTED | FORMAL_CRYPTO_SOUNDNESS | THEOREM_TYPE_MISMATCH |
| `near-reexec-skip-refund` | REJECTED | FORMAL_SEMANTIC_SOUNDNESS | THEOREM_TYPE_MISMATCH |
| `near-reexec-malicious-executable` | REJECTED | ARTIFACT_BINDING | ARTIFACT_BINDING_FAILED |

All 13 NEAR-formal cases (the 11 rows above from `malicious-executable` on, plus
the two `near-reexec-*`) are real NEAR packages: the reference backend
`examples/reexec-witness` (native-lean route), honest except for exactly one
attack. They are **derived cases**: the case directory holds `BASE`
(`examples/reexec-witness`) and only the files that differ; the e2e driver
materializes base + overlay before packing (`run_hostile.py --materialize DIR`
writes the exact submitted tree), the Rust loader checks the union. The 11 are
produced by `generate.py` (edits applied to the base files); the two
`near-reexec-*` are hand-written overlays. On this route the checker attributes
every finding to all formal gates (the admission statement is not a `∧` chain)
and the worker fails ARTIFACT_BINDING on any statement mismatch, so each case
names the gate its attack is *about* plus the attack's specific reason code.
`changed-security-parameters` expects THEOREM_TYPE_MISMATCH, not
SECURITY_BOUND_INSUFFICIENT: the profile is part of the judge-built statement,
so weakened parameters surface as a statement mismatch (the checker never emits
SECURITY_BOUND_INSUFFICIENT).

#### Runtime / execution attacks

| case | decision | failing gate(s) | reason code(s) |
|------|----------|-----------------|----------------|
| `forged-pass-output` | REJECTED | ADVERSARIAL_PROOFS | HOSTILE_PROOF_ACCEPTED |
| `benchmark-shortcut` | REJECTED | CONFORMANCE_DIFFERENTIAL | CLAIM_MISMATCH |
| `precomputed-fixture-table` | REJECTED | CONFORMANCE_DIFFERENTIAL | CLAIM_MISMATCH |
| `background-daemon` | REJECTED | PROVER_RELIABILITY | PROVER_FAILED |
| `sandbox-escape-filesystem` | REJECTED | PROVER_RELIABILITY | PROVER_FAILED |
| `sandbox-escape-network` | REJECTED | CONFORMANCE_DIFFERENTIAL or ADVERSARIAL_PROOFS | SANDBOX_VIOLATION |
| `sandbox-fork-bomb` | REJECTED | RESOURCE_LIMITS | RESOURCE_LIMIT |
| `sandbox-ptrace-proc` | REJECTED | CONFORMANCE_DIFFERENTIAL or ADVERSARIAL_PROOFS | SANDBOX_VIOLATION |
| `forged-timing` | REJECTED | CONFORMANCE_DIFFERENTIAL or ADVERSARIAL_PROOFS | SANDBOX_VIOLATION |
| `ui-injection-logs` | REJECTED | ADVERSARIAL_PROOFS | HOSTILE_PROOF_ACCEPTED |
| `ui-injection-manifest` | REJECTED | PKG_WELLFORMED | MANIFEST_INVALID |

`sandbox-escape-network` (`socket(AF_INET)`), `sandbox-ptrace-proc` (`ptrace`)
and `forged-timing` (`clock_settime`) are caught by **sound syscall-level
detection**: the sandbox init (Firecracker guest `arena-init`, bwrap-dev helper
init) installs a seccomp user-notification filter on the candidate tree
(`runners/seccomp`); the listed syscall is denied (EPERM) *and* recorded by the
init, and the worker fails the gate of the runtime job that ran `prove` first
(conformance or adversarial, scheduled together) with `SANDBOX_VIOLATION`. A
report exists only if a candidate process really made the syscall.
`sandbox-escape-filesystem` stays `PROVER_FAILED`: its prover only opens files
(reads of the sandbox's own rootfs are harmless; writes fail on read-only
mounts), and a failed write to a read-only path cannot be told apart soundly
from an honest-but-buggy program, so it is contained but not reported as a
violation. Build recipes run under the looser `tooling` policy (no socket
rule), so `build-network-fetch` stays `BUILD_FAILED`.

#### Build / archive attacks

| case | decision | failing gate(s) | reason code(s) |
|------|----------|-----------------|----------------|
| `build-network-fetch` | REJECTED | BUILD_REPRODUCIBLE | BUILD_FAILED |
| `build-nonreproducible` | REJECTED | BUILD_REPRODUCIBLE | BUILD_NOT_REPRODUCIBLE |
| `build-dependency-substitution` | REJECTED | ADVERSARIAL_PROOFS | HOSTILE_PROOF_ACCEPTED |
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

### Note: random bit flips are not enough for malleability (2026-10-06)

Live run 1 of the v3 D0 reference (`near-chunk-validation-d0`) was rejected only
because one of the generic `bitflip` mutator's five random positions per proof
happened to land in the chunk signature: the proof was the raw `ChunkStateWitness`,
and nearcore's validator ignores ~100 of its bytes (`height_included`, the chunk
signature, every transition `block_hash`). A rerun could have missed them. The
worker therefore ships a **structure-aware** generic mutator, `v3-ignored-fields`
(`runners/worker/src/mutators.rs`), which flips one bit of each validator-ignored
field of every `near-arena-witness-v3` proof, and the permanent hostile case
`near-v3-malleable-witness` (target `near-v3`) must be REJECTED with
`HOSTILE_PROOF_ACCEPTED` deterministically. **Follow-up:** whenever a statement has
inputs the reference validator does not read (known ignored fields of a witness
format, lenient map decoding, unsorted keys, unreferenced trie nodes), add a
structure-aware mutator for them instead of relying on random positions.

**Lenient decoding (closed 2026-10-06).** Duplicate / unordered
`source_receipt_proofs` keys and reordered, repeated or never-read `base_state`
values are a further malleability class (insertion and reordering, not bit flips)
that the canonical-only reference left open. The worker's generic structure-aware
mutator `v3-witness-freedoms` now applies each of them to every
`near-arena-witness-v3` proof (`entries/duplicate-key`, `entries/reorder`,
`values/{reorder,duplicate,inject-unused}.<main|implicitN>`), the permanent hostile
case `near-v3-lenient-witness` (the canonical-only reference) must be REJECTED with
`HOSTILE_PROOF_ACCEPTED`, and the reference accepts only the **full normal form**
(`examples/reexec-v3-d0/formal/ReexecV3D0/NormalForm.lean`: entries deduplicated
and sorted by key, every `base_state` exactly the read set of the relation's trie
builds, deduplicated and sorted; proved complete and enforced byte-exactly).

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

Judge-owned source-mutation operators (generic + `reexec-merkle`-specific; note: there is no `examples/reexec-merkle` — the re-execution backends are `examples/reexec-witness` and `examples/reexec-witness-fast`) to be
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

## Challenge targeting (`expect.json` `targets` / `runnable`)

`near-v3` targets the v3 D0 challenge `near-chunk-validation-d0` (`run_hostile.py --target near-v3`).

A gate only exists where the challenge requires it, so each case declares which
challenge kind(s) it is meaningful on:

- `targets: ["demo"]` — attacks a gate in the demo challenge's required
  obligations; run by `tests/e2e/run.sh --hostile` (driver `--target demo`).
- `targets: ["near-formal"]` — attacks a formal / artifact-binding / crypto
  obligation that only the NEAR formal challenge has; run by
  `--target near-formal` (`milestone-d.sh`, or `run.sh --hostile-near`).
- `runnable: false` — documents an attack but is not auto-submitted (the
  driver skips it with that note, never faked). No case currently uses it.

## Status

Live, green:

- `tests/e2e/run.sh --target near-formal` (real server + Firecracker worker,
  the signed NEAR challenge `chl_3be93793…` v1-2): **13/13 NEAR-formal cases
  match** decision + gate + reason codes; 0 admitted, 0 accepted, 0 ranked.
  Results: `docs/e2e-results/hostile-near-formal/`.
- `tests/e2e/run.sh --hostile` (= `--target demo`; real server + bwrap-dev
  worker, demo challenge): **22/22 demo cases match**; injection sanitized.
  Results: `docs/e2e-results/hostile-final/`.
- `cargo test -p proof-mutators`: mutator unit tests plus suite
  well-formedness (35 cases, derived ones checked against base + overlay).
- `python3 hostile-submissions/generate.py --check`; `e2e/run_hostile.py
  --dry-run` packages all 35.

Follow-up: wire `mutants/` once the integrator applies the operators to a
reference backend. (The NEAR-formal stubs are now live cases, and sandbox
escapes are reported as `SANDBOX_VIOLATION` via seccomp: see
`docs/e2e-results/hostile-seccomp/`.)
