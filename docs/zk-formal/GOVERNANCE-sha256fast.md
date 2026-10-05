# Governance note: `ArenaCore.sha256Fast` and its `@[csimp]` equality

Status: proposed on branch `lane/zk-L4-sha` (lane L4), 2026-10-03. The lead
has already decided that formal-core ships this (see the zk-formal preamble,
governance decision 1). This note records exactly what changes in the trusted
base and what follows from it.

## What changed in formal-core

| File | Change |
|---|---|
| `ArenaCore/SHA256Fast.lean` | **new**, 283 lines. Defines `ArenaCore.sha256Fast : Bytes → Digest` (`@[noinline]`) and its helpers in `ArenaCore.SHA256Fast.*`. Proves `@[csimp] theorem ArenaCore.sha256_eq_sha256Fast : @sha256 = @sha256Fast`. |
| `ArenaCore.lean` | `+ import ArenaCore.SHA256Fast` |
| `ArenaCore/Interp.lean` | `+ import ArenaCore.SHA256Fast` (import only, no definitions change; see below) |
| `ArenaCoreTests/SHA256Fast.lean`, `ArenaCoreTests.lean` | new compiled-evaluation test vectors, plus their registration |

No existing definition, statement or theorem changed. `ArenaCore.sha256`
remains the specification.

**Why Interp.lean needs the import.** A `@[csimp]` lemma only redirects code
that is compiled in a module where the lemma is imported. Without the import,
the compiled bodies of `Interp.deployedRO` and of the interpreter's `SHA256`
instruction keep calling the slow spec. That covers every native-lean
verifier, because it reaches the hash through `OracleVerifier.deployed` →
`Interp.deployedRO`. Measured before the import: 49–68 µs per block through
`deployedRO`. After it: 1.1 µs. In the generated `Interp.c`, every call now
goes to `lp_ArenaCore_ArenaCore_sha256Fast`. The only remaining calls to
`…_sha256(` are inside `SHA256.c` itself.

## Why

DESIGN.md §7 and R8 explain the need. The native-lean STARK verifier hashes
about 180–236k blocks per proof. The compiled spec SHA-256 alone would take
about 7–10 s of the 10 s verify budget.

## Trust argument

* **The kernel never relies on `sha256Fast` for a statement.** Every arena
  statement (`Admission`, `ROM`, `Interp`, `NearSpec`) still mentions
  `ArenaCore.sha256`. `sha256Fast` appears only on the right-hand side of the
  equality theorem.
* **The equality is an ordinary kernel-checked theorem.**
  `#print axioms ArenaCore.sha256_eq_sha256Fast` reports
  `[propext, Classical.choice, Quot.sound]`. It uses no `sorry`,
  `native_decide`, `implemented_by`, `extern` or `unsafe`, and it
  elaborates in about 0.6 s.
* **What `@[csimp]` does.** It tells the compiler to substitute
  `sha256Fast` for `sha256` in generated code. That is the same mechanism
  core Lean uses for `List.append`, `Nat.repeat` and similar functions.
  Compiled behaviour therefore changes only by an implementation that has
  been proved extensionally equal to the spec, so the trust placed in
  compiled code is the same as before: the Lean compiler and runtime, with
  `UInt32` semantics as modelled by `UInt32.toNat_*`.
* **Proof structure.** Each fast layer mirrors one spec layer:
  * word operations: `add_toNat`, `rotrF_toNat`, `chF_toNat`,
    `majF_toNat`, `bsig0F/1F_toNat`, `ssig0F/1F_toNat`;
  * the 64-round loop with the window held as 16 unboxed arguments:
    `roundsF_spec`;
  * parsing and blocks: `be32_toNat`, `readWords_spec`, `compressF_spec`,
    `blocksF_spec`;
  * padding: `padF_spec`, `padF_length`;
  * the round constants: `KF_map` (by `decide`).

## Tests (`ArenaCoreTests/SHA256Fast.lean`; `#guard`, compiled evaluation)

* FIPS 180-2 vectors: `""`, `"abc"`, the 448-bit vector, the 896-bit vector,
  and 1,000,000 × `'a'`.
* A differential test against the spec, recompiled under a fresh name
  (`specSha256`) so the csimp does not touch it. Lengths covered: 0, 1, 3,
  31, 32, 55, 56, 57, 63, 64, 65, 100, 119, 120, 127, 128, 129, 1000 and
  4096, which include every padding boundary.
* The same check through `sha256` itself, which is redirected.
* The existing kernel vector `sha256_abc` (`decide +kernel`) is unchanged
  and still passes.

## Measurements (Lean 4.34.1, this host, compiled)

The benchmark hashes 200 messages of 65 blocks each. Its source is in the
scratch package `shabench-l4`, which is not in the repository.

| Path | µs / 64-byte block |
|---|---|
| spec algorithm (`specSha256`, not redirected) | 40–52 (one noisy run gave 85) |
| `sha256` call site (redirected by csimp) | 1.04–1.12 |
| `Interp.deployedRO` (with the Interp import) | 1.10–1.17 |
| `sha256Fast` called directly | 1.08–1.19 |

The speedup is about 40×. The generated C of a downstream `sha256 m` call
site calls `lp_ArenaCore_ArenaCore_sha256Fast`.

## Builds

* `formal-core` `lake build` (ArenaCore, ArenaCoreTests, Toy): OK.
* `negative/check_negative.sh`: positive control PASS, all 11 negatives
  REJECT as expected.
* `zk-formal` `lake build`: OK.

## Implications the lead must handle

1. **formal-core identity.** The signed challenge
   `chl_3be93793610370275ae40f36a475f01f` pins
   * `semantic_scope.formal_spec.tree_digest` (`sha256:8090432a…`, the spec
     and formal-core tree);
   * `toolchain_policy.allowed_packages` `ArenaCore @ 4f5c19df…`.

   Adding a module changes both. Using this module on that challenge
   therefore needs either a re-issued or amended challenge, or a policy that
   accepts this formal-core revision. **Alternative with no formal-core
   change.** DESIGN §10.3 verified that a *candidate-side* `@[csimp]` lemma
   `@ArenaCore.sha256 = @alt` also redirects compiled call sites, but only
   in modules compiled with the lemma imported. Since `Interp.deployedRO` is
   compiled inside formal-core, a candidate on that route would also have to
   avoid calling `deployedRO` through formal-core's compiled code. One way is
   a twin csimp for `Interp.deployedRO` defined candidate-side. Another is
   to have the native binary use its own `deployedRO`-equal function. The
   formal-checker audit (`runners/formal-checker/src/audit.rs`,
   `grep.rs`) flags `implemented_by`, `extern` and `unsafe`, but it does not
   flag `csimp`.
2. **Checker image and recheck time.** The new module adds about 0.6 s of
   elaboration and a small number of declarations to recheck. Recheck with
   `leanchecker`, `nanoda` and `lean4lean` has not been measured here; the
   proof is small and uses no large `decide`.
3. **InterpRef / NPAI.** `arena-interp-ref`, the compiled Lean interpreter
   model, now also runs the fast hash through the `Interp` import. Its
   semantics are unchanged because of the proved equality, but its digest
   changes, so the differential test against `runners/npai` should be rerun
   once.
