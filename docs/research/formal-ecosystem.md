# Formal-verification ecosystem survey for NEAR Proof Arena

Status: research note. Snapshot date 2026-10-03. All repositories were shallow-cloned into
`/data/illia/nearproof-deps/<name>` and inspected at the commits listed below. Statements in this
document are about **checked artifacts in the source trees** (theorem statements, `sorry`/axiom
footprints, CI gates), not README/blog claims. Where we relied on a project's own committed axiom
census instead of rebuilding, that is said explicitly.

Arena requirement recap: a candidate prover is admitted only with a machine-checked Lean 4
certificate that binds (1) NEAR state-transition semantics, (2) cryptographic soundness of the
proof system (non-interactive, i.e. after Fiat–Shamir), and (3) the actual artifacts (verifier
code / verifying key / circuit that are deployed).

## 0. TL;DR

* **Nobody provides an end-to-end certificate.** No public project has a machine-checked chain
  "Rust verifier accepts ⇒ (w.p. ≥ 1−ε in the ROM) the guest/AIR relation holds ⇒ ISA/spec
  semantics". Every zkVM effort we inspected *assumes* the proof system (STARK/FRI/LogUp/FS) and
  the bus/lookup argument.
* **Chip-level constraint faithfulness is the mature layer.** Best public artifacts:
  `openvm-fv` (45 RV32IM opcodes + SHA-256/SHA-512/Keccak-f chips vs Sail-Lean / FIPS models,
  axiom-clean, CI-gated with `leanprover/comparator`), and `sp1-lean` (25 RV64IM chips, but the
  machine-level theorem still depends on one `sorry` and on `Lean.ofReduceBool`).
* **Protocol soundness in Lean is immature.** ArkLib has the *definitions* (soundness, RBR, SR,
  FS transform) but FS soundness is not even stated, `fiatShamir_completeness` is `sorry`,
  `rbrSoundness_implies_soundness` is `sorry`, FRI relations are `sorry` defs, BCS is absent.
  Proven pieces: new-framework Sumcheck soundness, Johnson bound, BCIKS20 *unique-decoding*
  regime, DG25, a ToyProblem IOR. VCVio has a sorry-free ROM toolkit, forking lemma,
  Fiat–Shamir **for Σ-protocols (signatures)**, and Merkle extractability in the ROM.
* **Rust ↔ Lean binding:** Aeneas (directly or via `cargo hax into lean`, which now runs
  Charon+Aeneas) is the only realistic route. Kani/Verus/Creusot produce no Lean objects.
  OpenVM's "certified verifier" uses the opposite direction (Lean → C, vendored + CI byte-check)
  but its theorems are in a private repo.
* **Independent rechecking:** `lean4export` + `nanoda_lib` / `lean4lean` / `lean4checker`
  and `comparator` exist and are usable; see `checker-recommendations.md` for hands-on results.

## 1. Commit / toolchain table

| Repo (upstream) | Commit | Date | Lean toolchain | Mathlib |
|---|---|---|---|---|
| sp1-lean (succinctlabs/sp1-lean) | `512e944ab2a680593125265694dcbd9b058b4dcb` | 2026-06-25 | v4.28.0 | v4.28.0 (`8f9d9cff`) |
| sp1 (succinctlabs/sp1) | `edc07b68c92c17e4fc8658c39a2ef8d9ea5d95dc` | 2026-10-02 | – (Rust, v6.8.1) | – |
| clean (Verified-zkEVM/clean) | `fba2a29f5e36420d797c1de118ac9f11f23b819e` | 2026-09-16 | v4.33.1 | v4.33.1 (`0df444a3`) |
| CertiPlonk (NethermindEth/CertiPlonk) | `3f04c97b67e2c42e6dbf0b38df8fa61977d3ae0d` | 2025-11-24 | v4.23.0-rc2 | v4.23.0-rc2 (`90c0e186`) |
| CertiPlonk (logical-intelligence fork) | `9a66e4871d10194472603fed1f412fc6b592ec28` | 2025-07-25 | v4.22.0-rc2 | yes |
| LeanZKCircuit-Plonky3 (NethermindEth) | `1981f3b481515abf76eccc3bea132ebdabd22eea` | 2025-09-29 | v4.23.0-rc2 | yes |
| Plonky3 (Plonky3/Plonky3) | `3acc8b70e68d6c2afc03930700c26540bd47458d` | 2026-10-02 | – (Rust, v0.8.0) | – |
| ArkLib (Verified-zkEVM/ArkLib) | `ace55c3e29da1fc55a321378ada55ea4f7ed8790` | 2026-10-02 | v4.34.0 | v4.34.0 (`5ed29652`) |
| VCVio (Verified-zkEVM/VCVio) | `f5119c64ebb055d69c143704e12eba6df7dc386c` | 2026-09-26 | v4.34.0 | v4.34.0 (`5ed29652`) |
| zkLean (Verified-zkEVM/zkLean) | `eb17e501ba5b81ab77a20df52c590533e537657e` | 2026-03-10 | v4.25.2 | – |
| jolt (a16z/jolt) | `47130f3dc9a51a7ac2754a98ff0aa31981a6b810` | 2026-10-02 | template v4.28.0-rc1 | – |
| openvm (openvm-org/openvm) | `f08bf2836409f3c0a5f6b6cfe73eb177a8a3e8c8` | 2026-09-18 | certified-verifier C from v4.34.0 | – |
| openvm-fv (openvm-org/openvm-fv) | `7523c23a3148100a0f201b33385c0f8e01b2c858` | 2026-07-14 | v4.26.0 | v4.26.0 |
| risc0 (risc0/risc0) | `3bbcd44d6459b9ef6ac0df3846dc9215514934e8` | 2026-07-20 | – | – |
| zirgen (risc0/zirgen) | `df6fb9dda1c20209058d6ee90a8912351b741081` | 2026-01-20 | – | – |
| risc0-lean4 (risc0/risc0-lean4) | `31c956fc9246bbfc84359021d66ed94972afd86b` | 2023-02-14 | nightly-2022-12-23 | – |
| Picus (Veridise/Picus) | `138b151d3a388e5b6c040c163e0a1db04f2ceda6` | 2024-03-14 | – (Racket) | – |
| aeneas (AeneasVerif/aeneas) | `557eff83ecef5083b98a52a94ca7fae63d6c1dab` | 2026-10-02 | v4.31.0 (backends/lean) | v4.31.0 (`fabf563a`) |
| hax (cryspen/hax) | `ea24f98636878b3f87040962fcea47861dd27066` | 2026-10-01 | v4.31.0 (proof-libs/lean) | v4.31.0 |
| kani (model-checking/kani) | `1640445da3fa0d2cb19739652057dc992fef3f18` | 2026-10-02 | – | – |
| verus (verus-lang/verus) | `f319e4d9bd7154cb793bc37ffd90cf8ee8a77bb6` | 2026-10-02 | – | – |
| creusot (creusot-rs/creusot) | `abac8cc03f4b0ac5b689d788de9e4ade4bc5411c` | 2026-10-02 | – | – |
| lean4export (leanprover/lean4export) | `66f1fb4bc256072069767fce52d39480e4524869` | 2026-09-24 | v4.35.0-rc3 | – |
| lean4checker (leanprover/lean4checker) | `91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709` | 2026-03-25 | v4.29.0-rc8 | – |
| nanoda_lib (ammkrn/nanoda_lib) | `3a2407216ee84a75f9e1aead6803d0578be06ae7` | 2026-09-22 | – (Rust) | – |
| lean4lean (digama0/lean4lean) | `8223d223ed98661882e95d9d6a7126df7097cd76` | 2026-08-29 | v4.33.0-rc2 | – (Batteries) |
| comparator (leanprover/comparator) | `fd5d5bcf14177b187f66d4502071268d877887c3` | 2026-09-25 | v4.35.0-rc3 | – |

Lean upstream at snapshot: latest stable **v4.34.1** (2026-09-24), pre-release v4.35.0-rc3;
Mathlib master is on v4.35.0-rc3.

Note `nanoda` (ammkrn/nanoda @ `04c0b5e5`, 2021) is the dead Lean 3 predecessor; `nanoda_lib` is
the live one.

## 2. Raw vs refined hole counts

Raw = `grep -w` over all `.lean` files (includes comments, docstrings, tests, `#guard_msgs`
expected output). Refined = after stripping comments/strings and classifying by hand / by the
project's own kernel-level axiom census where available.

| Repo | .lean files / LOC | raw sorry | refined real sorry | axiom decls (real) | native_decide | bv_decide |
|---|---|---|---|---|---|---|
| sp1-lean | 396 / 77.8k | 27 | **1** (`SP1Clean/Soundness/SP1GatedVm.lean:223`, `sp1_witness_decode`) — reaches the machine theorem | 0 in repo; LeanRV64D dep declares platform/softfloat axioms | 31 (all in `SP1CleanTest`, CI-gated out of main lib) | 7 **in main lib** (`Model/SailWrap.lean`, `FormalModel/Contracts/Chips.lean`) |
| clean | 192 / 49.1k | 11 | 10 (all tactic-test `example`s in `Clean/Utils/Test/TestCircuitProofStart.lean`) | 0 | 122 (≈110 test examples; a few in `Utils/Primes.lean` field-primality facts that *do* propagate) | 6 (4 real: And8, Or8, `not64_eq_sub`, ByteDecomposition) |
| CertiPlonk (NethermindEth) | 9 / 903 | 2 | 0 | 0 | 3 (`prime_BabyBearPrime`, `inv_255`, `inv_256`) → every main theorem depends on `Lean.ofReduceBool` | 0 |
| CertiPlonk-li | 8 / 997 | 20 | 15 (`Wheels.lean` ×4, `MvPolyEquiv.lean` ×11 ring laws) | 0 | 0 | 0 |
| LeanZKCircuit-Plonky3 | 19 / 1.1k | 1 | 0 | 0 | 0 | 0 |
| ArkLib | 1093 / 314k | 235 | 171 in `ArkLib/` (54 files); 286 decls on kernel sorry list | 0 real (7 are axiomsweep test fixtures) | 0 in lib | 0 |
| VCVio | 1003 / 259k | 27 | 16 (signatures: GPV/Falcon/ML-DSA, FS-with-abort; 6 in scripts) | 0 real (7 test fixtures) | 1 (dormant `Interop/Hax`) | 1 (same) |
| zkLean | 42 / 4.0k | 13 | 13, all in `examples/` (core lib 0) | 0 | 0 | 1 |
| jolt zklean-extractor template | 5 / 156 | 1 | 1 (`BN254.ScalarField_is_prime`) | 0 | 0 | 0 |
| openvm-fv | 345 / 407k | 62 | 3, all in `ci/comparator/Challenge.lean` (intentional: frozen statements) | 0 | 0 (CI hygiene scan) | 0 |
| risc0-lean4 | 57 / 6.5k | 48 | 43 (Fri 33, ProofSystem 7, Merkle 3) | 0 | 0 | 0 |
| aeneas backends/lean | – / 71.9k (repo) | 56 | 0 in library (30 are `#guard_msgs` doc strings, rest `tests/`) | 11 in lib (8 opaque types/fns, 2 spec axioms: `get_target.spec`, `Slice.get_unchecked…_spec`; 1 test) + 24 generated in tests | test/examples only | test/examples only |
| hax proof-libs/lean | 22.6k | 49 (repo) | 0 in lib; 9 in `examples/sha3/.../Equivalence.lean` | 0 own (inherits Aeneas) | 0 | 168 raw (tactic tests) |
| lean4lean | 112 / 49.4k | 131 | (meta-theory WIP; checker itself is executable) | 103 raw (theory stubs) | 0 | 7 |
| lean4export / lean4checker | small | 0 | 0 | 0 | 0 | 0 |
| comparator | 46 / 1.1k | 27 | test challenges (intentional) | 6 (test) | 0 | 0 |

Key lesson for the arena: **raw grep is useless as a gate and READMEs are unreliable**
(sp1-lean's README says every soundness theorem is axiom-clean; its own committed census shows
`MulChip.soundness` depends on `Lean.ofReduceBool`). The arena must compute axiom footprints from
kernel terms itself.

## 3. Per-project findings

### 3.1 SP1-Lean (+ SP1 Rust)

**Proven (chip level).** All 25 RV64IM chips (Add, Addi, Addw, Sub, Subw, Bitwise, Lt,
ShiftLeft, ShiftRight, Jal, Jalr, Branch, UType, Load{Byte,Half,Word,Double,X0},
Store{Byte,Half,Word,Double}, Mul, DivRem, AluX0) have
`<Chip>.soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec` and
`completeness`, generic over a prime `p > 2^17` (`2^24` for Mul), with `Spec` stated against
`RV64.*` functions; Sail bridges `correct_<op>_native` / `<op>_chip_reaches_sail` connect to
LeanRV64D (Sail-generated RISC-V model, Succinct fork branch `dtumad/clean-native`).

**Composition.** `Soundness/GatedVm/Capstone.lean: gatedExecution_of_specs_and_balance`:
per-row chip specs + `isConsistentBalanced` state bus over ℤ ⇒ `GatedExecution` (local Sail
correctness of each real row + an Eulerian walk of (clk, pc) edges from init to final).
`SP1GatedVm.lean: sp1_machine_soundness : sp1GatedVm.toEnsemble.Soundness sp1Assumptions sp1Spec`
— but `sp1Spec` only constrains initial/final `clk`,`pc` (10 field elements): **no registers,
memory, public-values digest, or exit code**, and it depends on `sorry` via
`sp1_witness_decode`. `TargetVm.lean: sp1_target_execution` reaches a Sail `try_step` chain but
takes the substance (`TargetObligations`) as a hypothesis.

**Faithfulness to deployed SP1.** Constraints in `Extracted/` come from
`sp1-constraint-compiler` (symbolic evaluation of Rust `eval`, trusted printer) at
`SP1_PINNED_COMMIT = 9d249b8d…` on branch `dtumad/clean-native` (≈ v6.2.2). SP1 `main`
(`edc07b68`, v6.8.1) lacks the flags the script uses → **extraction not reproducible from
main**; no CI re-extract/diff. Faithfulness anchors in `Faithful/` (112 theorems) are partial:
Mul/Bitwise/Shift only one direction, no DivRem anchor, non-byte interactions interpreted as
`True`; the capstone uses hand-written `Native/` circuits.

**Out of scope (their `docs/release-audit.md`):** ECALL/EBREAK/UNIMP, all syscalls, memory
global init/finalize, page protection, Global chip, all 49 precompiles (incl. SHA-256, ed25519,
Keccak — exactly what NEAR guests use), recursion/compress/shrink/wrap, and the entire proof
system (Jagged PCS, LogUp-GKR, sumcheck, FRI/BaseFold, FS) — assumed as the "W8 LogUp axiom".

**Axioms.** `sorryAx` reaches `sp1_machine_soundness`; `Lean.ofReduceBool` (via `bv_decide`)
reaches `MulChip.soundness`, Branch/Jal/Jalr bridges and the capstone; LeanRV64D platform axioms
(`sys_enable_experimental_extensions`, `load_reservation`, `match_reservation`,
`plat_term_write`, ~76 softfloat/platform axioms for target theorems).

**Build:** 391 modules ≈ 3965 s sequential excluding Mathlib/Sail (their profile); CI on 64 CPUs.

**Reusable:** (a) Clean-style `Ensemble.Soundness` shape and bus-balance-over-ℤ lemma
(`BalanceMod.lean: isConsistentBalanced_of_balancedInteractions`, valid only when multiplicities
∈ {−1,0,1} and length < p); (b) nothing; (c) nothing on the verifier side.

### 3.2 Clean

Lean circuit DSL. `Clean/Circuit/Formal.lean`: `Soundness` (Assumptions ∧ constraints ⇒ Spec ∧
Requirements, subcircuits abstracted by their specs), `Completeness`, `FormalAssertion`,
`GeneralFormalCircuit`, `DeterministicFormalCircuit`. AIR layer `Clean/Air/`:
`Ensemble.Statement pi := ∃ witness, publicInput = pi ∧ Constraints ∧ BalancedChannels` where
`BalancedInteractions := length < ringChar ∧ ∀ msg, Σ mult = 0`; `Ensemble.Soundness`.
`FormalEnsemble` has no completeness. **No verifier challenges / LogUp / FS** (roadmap item).

Backends: Circom/R1CS export (0 theorems), `backends/plonky3` Rust POC ("NOT-PRODUCTION-READY")
on Plonky3 rev `47e442f`; no proof that exported constraints equal Lean `ConstraintsHold`.

Gadgets: SHA-256 `CompressBlock` proved vs hand-written `Specs/SHA256.compressBlock` but needs
`p > 2^33` (not usable over BabyBear/KoalaBear/M31); spec validated only by `native_decide` test
vectors. Keccak, BLAKE3 (`p > 2^16+2^8`), Poseidon (BN254), u32/u64. **No ed25519, no non-native
bigint, no borsh, no Wasm.** Field-primality `Fact` instances in `Utils/Primes.lean` use
`native_decide` and taint anything instantiated at BabyBear/M31/SHA-field.

**Reusable for (a):** the cleanest *vocabulary* for "ideal relation ⇒ spec" (Assumptions / Spec /
Ensemble.Statement). Requires replacing native_decide primality with Pratt certificates.

### 3.3 CertiPlonk / LeanZKCircuit-Plonky3 (Nethermind) and the logical-intelligence fork

*LeanZKCircuit-Plonky3*: `class Circuit F ExtF α` (main/permutation/preprocessed columns,
rotations, bus, challenges, public values), `#define_air` string-templating metaprograms, list
lemmas for bus balance in `F` (no wrap-around/characteristic argument; no LogUp soundness).
0 real sorry.

*CertiPlonk*: extractor lives in fork NethermindEth/Plonky3 (`72e4479`):
`air/src/symbolic_builder.rs::print_lean_constraints` prints `SymbolicExpression` trees; a human
pastes stdout into `Extraction.lean`. Extension-field constraints not printed (`// todo`),
permutation-column constraints emitted commented-out, public-values name mismatch; fork predates
current upstream `SymbolicAirBuilder`. Only example: `Add8Air` (12 cols, 11 constraints):
`constraint_i_of_extraction`, `spec_soundness_FBB` (single row, a,b<256 ⇒ c=(a+b)%256),
`determinism`, `spec_completeness`. Verified build (subagent): `lake build` 3m24s, 10 GB RSS;
`#print axioms spec_soundness_FBB` = `[propext, Classical.choice, Lean.ofReduceBool,
Lean.trustCompiler, Quot.sound]` (native_decide BabyBear primality).

*logical-intelligence/CertiPlonk*: actually `CMvPolynomial` (computable multivariate polynomials,
ancestor of CompPoly); 15 real sorries in ring laws; not a Plonky3 tool.

**Reusable:** pattern only (symbolic-builder → Lean printer). Not an artifact binding.

### 3.4 Plonky3 (Rust)

No formal verification in-repo (no Kani/Verus/Creusot/hax/Lean); proptests; one Least Authority
audit; `docs/caller-obligations.md` lists unchecked caller duties (e.g.
`BaseAir::main_next_row_columns`, `air/src/air.rs:178`, "soundness gap" if wrong).

Verifier: `uni-stark/src/verifier.rs` (`verify` l.450, `verify_with_preprocessed` l.465,
`verify_constraints` l.117); transcript schedule `uni-stark/src/transcript.rs` (`StarkShape`,
domain separator `"p3-uni-stark"` v1) binds shape but **not the constraint polynomials** (the AIR
is fixed by the verifier binary — so the arena must pin the AIR by code hash). PCS:
`fri/src/two_adic_pcs.rs:832` → `fri/src/verifier.rs:477 verify_fri`. Merkle:
`merkle-tree/src/mmcs/mod.rs`. Challengers: `DuplexChallenger`, `HashChallenger`,
`SerializingChallenger*`, spongefish-style `challenger/src/fs/`. Grinding: `check_witness`
(`grinding_challenger.rs:48`).

Security calculator (`security/`, `uni-stark/src/security.rs`) run by the subagent on example
parameters (KoalaBear deg-4 ext, blowup 2, 84 queries, PoW 16): **proven 50 bits (UDR) / 57
(list-decoding), conjectured 97, legacy 100**. Proven ≈100+ bits needs ~blowup 8, 120 queries,
16–20-bit PoW (deg-8 extension reaches ~119–128). The calculator itself is unverified f64 Rust.

CPU measurements (AMD 9950X3D, 32 threads, `-Ctarget-cpu=native`, KoalaBear+Poseidon2 Merkle):
2^20-row Poseidon2 AIR (8.4M perms) prove 6.7 s / verify 12 ms / 710 KB / 11.3 GB RSS; custom
Poseidon2 hash-chain AIR written in ~1 hour (~110 LOC): 2^18 steps prove 0.67 s, verify 8.5 ms.
Examples use random round constants — production configs must use standard constants.

### 3.5 ArkLib

Definitions (`OracleReduction/Basic.lean`, `Security/{Basic,RoundByRound,StateRestoration}.lean`):
`Verifier.soundness`, `knowledgeSoundness(With)`, `rbrSoundness`, `rbrKnowledgeSoundness`,
state-restoration soundness, completeness; `NonInteractiveProver/Verifier`; shared oracle
`oSpec` with implementation `impl` (so a random oracle can be expressed).

Implications (`Security/Implications.lean`): only `rbrKnowledgeSoundness_implies_rbrSoundness`
is proven; `rbrSoundness_implies_soundness`, `knowledgeSoundness_implies_soundness`,
`srSoundness_implies_soundness`, etc. are `sorry`.

Composition: legacy `seqCompose_*`, `append_*`, `liftContext_*` all on the sorry list; the new
`Interaction/` framework (PolyFun interaction trees) has sorry-free prefix+suffix error-addition
lemmas (`Interaction/CompositionSoundness.lean: run_appendFlat_soundness` and variants,
`Interaction/Oracle/RuntimeSoundness.lean`).

**Fiat–Shamir** (`OracleReduction/FiatShamir/Basic.lean`): `Prover/Verifier/Reduction.fiatShamir`
defined; only theorem `fiatShamir_completeness := sorry`; soundness is a TODO comment.
Duplex-sponge FS (`FiatShamir/DuplexSponge/`): 19 sorries, `Security/Soundness.lean` is a header
only. **BCS** (`OracleReduction/BCS/Basic.lean`): transform commented out.

Protocols: Sumcheck (new framework, `ProofSystem/Sumcheck/Interaction`) **sorry-free soundness
and completeness** + computable executor; legacy Sumcheck 13 sorries; FRI relations `:= sorry`
defs, `Fri.fri_soundness`/`fri_query_soundness` sorry; STIR main theorems sorry; WHIR absent;
Binius components on sorry list; Spartan/Plonk spec-only; ToyProblem (ABF26 §6) RBR knowledge
soundness **proven** (information-theoretic, empty oracle spec); Johnson bound proven; BCIKS20
unique-decoding regime proven, Johnson/list regime (Thm 5.1, 1.2) sorry; DG25 proven; AHIV22
Ligero proximity lemma proven; capacity/list-decoding bounds admitted as "external" sorries.

Governance worth copying: `scripts/axiom_baseline.json` + `lake exe axiomsweep --check` in CI
(kernel-level list of sorry-dependent declarations; fails on any `ofReduceBool`/`trustCompiler`).
ArkLib uses the Lean module system (`requiresModuleSystem`), so `#print axioms` must run from a
non-module client.

### 3.6 VCVio

`OracleComp spec := PFunctor.FreeM`; `evalDist`, `Pr[...]`; lazy random oracle `romImpl` with
eager≡lazy and programming lemmas; query bounds `IsQueryBound/IsPerIndexQueryBound/
IsTotalQueryBound` preserved under `simulateQ`; birthday/collision bounds; forking lemma
(`ReplayFork.lean`, `SeededFork.lean`); **Fiat–Shamir for Σ-protocols, sorry-free**
(`CryptoFoundations/FiatShamir/Sigma/Security.lean`: `euf_cma_to_nma`, `euf_nma_bound`,
`euf_cma_bound`); Merkle extractability in the ROM (`MerkleTree/…: extractability_rom_bound`,
multi-opening variants); generalized RBR knowledge (`CryptoFoundations/RoundByRound.lean`,
extensional only). Hax interop (`Interop/Hax/Bridge.lean: liftRustM`) is dormant / excluded from CI.

**This is the best existing foundation for (b)**: the arena can state
"∀ adversary making ≤ q RO queries, Pr[x ∉ L ∧ V accepts] ≤ ε(q)" in VCVio terms today; nobody
has *proved* it for a multi-round IOP compiled by FS+BCS.

### 3.7 Jolt / zkLean

`jolt/zklean-extractor`: emits ZKBuilder Lean for the RV64I R1CS (22 constraints/cycle), 55
lookup-table MLEs, 4 sumcheck identities; `MemOps.lean` hand-written; bytecode
read-raf-checking not extracted. **No theorems** over the extracted model; CI's
`lake build` step is commented out. Lean pins `GaloisInc/zk-lean@4ea5a19` (not the
Verified-zkEVM clone). `z3-verifier/`: 52 SMT determinism checks over unbounded Int (not mod p),
35 virtual-sequence checks (10 ignored). HOL Light proofs of Fp64/Fp128 assembly kernels with a
byte-identity checker against compiled objects (opt-in feature, not production default) — a good
pattern for artifact binding. FS: syntactic transcript inventory tests + attack tests; no proofs.
README: alpha, not audited.

zkLean core: ~600 LOC, 0 sorry; `Formalism.sound/complete/deterministic`. Examples (SHA-3) have
sorry'd *circuit definitions*.

### 3.8 OpenVM and openvm-fv

*openvm-fv* (`7523c23a`, Lean v4.26.0, Mathlib v4.26.0, LeanRV = NethermindEth/sail-riscv-lean
`rv32d`): constraints extracted from **OpenVM v2.0.0** (`15a7ab6b`, stark-backend `16d60de7`),
pinned in `extractor/Cargo.toml`. Proven: 45 RV32IM opcodes
(`OpenvmFv/Equivalence/Equivalence.lean`, e.g. `equiv_ADD`: for a row with given opcode,
`execute_instruction instr state = (bus_effect executionBus memoryBus state).2`), plus
`VmExtensions`: `Keccakf.Soundness.keccakf_matches_spec`,
`Sha2BlockHasherVmAir_sha256.BlockSpec.sha2_block_soundness`, SHA-512 analogue,
`Sha2CompressOpcode.equiv_SHA256_COMPRESS` (FIPS 180-4 / 202 models). 0 real sorry (3 in the
comparator Challenge file by design), 0 axioms, 0 native/bv_decide — enforced by three CI gates:
`scripts/check_hygiene.py`, in-build `#audit_axioms` (`VmExtensions/Audit.lean`), and
**`ci/comparator`** (Challenge.lean with frozen statements + `config.json`
`permitted_axioms: [propext, Quot.sound, Classical.choice]`, `enable_nanoda: false`).
Assumptions (REPORT.pdf, RV32IM only): I1 lookup/bus argument correct, **I2 proof system
correct**, I3 Lean RISC-V spec matches the standard, I4 Lean kernel; bus axioms (pc < 2^30,
pc%4=0, timestamp < 2^29) justified on paper; Sail spec modifications S1–S4 and machine-state
assumptions A1–A4. Per-row/per-chip only; no whole-trace theorem; no completeness direction.
This is the **best public template** for chip-level obligations + CI admission hygiene.

*openvm* main (`f08bf28`, v2.1.0): `crates/certified-verifier` vendors ~101.9k lines of C
generated by Lean v4.34.0 from the **private** repo `axiom-crypto/ws-fv@b94bf5a2`; CI checks the
vendored C equals regenerated C; Rust wire encoders (`vk.rs`, `proof.rs`, `public_values.rs`) are
trusted. Exposed via `cargo openvm verify stark --certified`. Theorems not public → cannot be
counted as a checked artifact for us. Security doc claims 100-bit provable security (SWIRL:
sumcheck+WHIR, GKR-LogUp, duplex sponge in the ideal-permutation model) — paper claims + a Rust
calculator. Note v2.x changed the memory architecture vs the v1.5 Nethermind report.

### 3.9 RISC Zero, zirgen, Picus, risc0-lean4

*risc0* (`3bbcd44`, v5.0.0): no Lean/Coq. New C++ rv32im circuit has a Picus extractor
(`compiler/extractor/`, ~45 blocks; DecodeBlock/InstLoad/InstStore/UnitMul commented out);
`bazel/helpers/picus_verify.sh` submits to Veridise AuditHub with the verdict grep commented out;
no CI gate. Security model: 96 bits (rv32im) / 99 (recursion) under ROM **plus the ethSTARK
Toy Problem Conjecture**; Groth16/BN254 trusted setup; calculator `risc0/zkp/src/prove/soundness.rs`.
Verifier: `risc0/zkp/src/verify/{mod.rs,fri.rs,merkle.rs,read_iop.rs}` (~1.1k LOC),
`risc0/zkvm/src/receipt/*`, `risc0/groth16/src/verifier.rs`.

*zirgen* (`df6fb9d`): `--emit=picus`; the only CI-gated check is `keccak-determinism` on a
self-hosted runner via proprietary AuditHub Picus v2. No committed outputs.

*Picus* (open, 2024): QED² uniqueness (underconstraint) for Circom/R1CS/gnark; trusts Racket
lemmas + cvc5 (FF theory)/Z3; no certificates; does not read zirgen's `.picus` format.

*risc0-lean4*: abandoned 2023 research artifact; 43 real sorries incl. `relation := sorry`.

None of these contributes to (a)/(b)/(c) beyond "determinism as an SMT side-condition".

### 3.10 Rust verification / extraction tools

| Tool | What is checked | Lean link | Trust base | Install | Verdict for (c) |
|---|---|---|---|---|---|
| **Aeneas** (`557eff83`, Lean v4.31.0, Charon pin `c8f15d7d`, rustc nightly-2026-09-17) | Total-correctness Hoare triples over a pure functional model (`Result` with `fail`/`div`); overflow → `fail .integerOverflow` | **Native Lean** | rustc MIR (nightly ≠ release build), Charon, Aeneas OCaml translator, 345 hand-written std models, 2 spec axioms in lib, any `FunsExternal` axioms | Prebuilt nightly binaries (`gh release … -R AeneasVerif/aeneas`); from source: opam+OCaml 5 (~½ day) | **#1** |
| **hax → Lean** (`ea24f986`, Lean v4.31.0) | same core: `cargo hax into lean` now runs Charon+Aeneas (cryspen/aeneas fork `6852e647`); adds requires/ensures, `hax_mvcgen` | Native Lean | Aeneas TCB + hax | `cargo install --locked cargo-hax`; tools fetched on demand | #2 (ergonomics; fork lag; Lean examples sorry-laden) |
| Kani (`1640445d`, v0.68.0, CBMC 6.11) | Bounded model checking: no panic/UB/overflow + asserts within unwind bounds | experimental `-Z lean` emits LLBC only | CBMC, SAT, Kani codegen; no proof object | `cargo install --locked kani-verifier && cargo kani setup` (~1–2 GB) | complementary only |
| Verus (`f319e4d9`, Z3 4.16) | SMT-discharged specs | none | Z3, vstd (485 `assume_specification`, 292 `external_body`) | moderate | not usable |
| Creusot (`abac8cc0`) | Why3/Coma + SMT | none | Why3, solvers | moderate | not usable |

Known Rust→Lean prototypes in `Verified-zkEVM/rust-lean` (`49a83d2a`): hax-merkle (rewritten toy
version of RISC Zero Merkle verify, 2 sorry), hax-FRI (13 sorry), aeneas-FRI (main correctness
**axiomatized**: `axiom fold_step_matches_nat`), Plonky3 field arithmetic (16 external axioms).
Templates, not finished bindings.

Semantic pitfalls the arena must handle when using Aeneas:
1. Aeneas models overflow as failure; release Rust wraps. Require either a proof that the model
   never fails on any input, or build the deployed verifier with `overflow-checks = true`.
2. `Usize` width is `System.Platform.numBits` — proofs must cover both 32 and 64.
3. External crates (`sha2`, `borsh`, `ed25519-dalek`) become `FunsExternal` axioms → must be
   explicitly listed as crypto/library oracles in the certificate, or modelled.
4. Reproducibility: re-run Charon+Aeneas in the arena and diff the generated `.lean` byte-for-byte.

### 3.11 Independent Lean checkers

See `checker-recommendations.md` §3 for hands-on build/run results. Summary of what each is:

* **lean4export** (`66f1fb4b`, Lean v4.35.0-rc3): dumps an environment (from `.olean`s) to a
  plain-text/NDJSON export format consumed by external checkers.
* **lean4checker** (`91a7f0e8`, v4.29.0-rc8): replays declarations from `.olean`s into the
  *same* C++ kernel (`--fresh` re-adds everything from scratch). Guards against environment
  hacking by metaprograms, not against kernel bugs.
* **nanoda_lib** (`3a240721`, Rust): independent type checker over lean4export output, with
  configurable permitted axioms.
* **lean4lean** (`8223d223`, v4.33.0-rc2): Lean kernel re-implemented in Lean, runnable as a
  checker; meta-theory (soundness of the kernel) is WIP with many sorries/axioms — its value is
  as an independent implementation, not as a verified one.
* **comparator** (`fd5d5bcf`, v4.35.0-rc3): trusted Challenge (statements with `sorry`) vs
  Solution; exports both via lean4export, checks statement identity and permitted axioms,
  optionally runs nanoda (`enable_nanoda`). Used in production CI by openvm-fv.

## 4. Reusability matrix

| Need | Best available artifact | Gap |
|---|---|---|
| (a) admission theorem shape, constraint side | Clean `Ensemble.Statement/Soundness`; zkLean `sound/deterministic`; openvm-fv per-opcode `equiv_*` + bus lemmas | No public whole-trace (multi-chip, memory consistency) theorem without sorry for any production zkVM; NEAR semantics (Wasm runtime, trie, borsh, ed25519) absent everywhere |
| (a) admission theorem shape, crypto side | ArkLib `Verifier.soundness` with `NonInteractiveVerifier`, VCVio ROM + query bounds | All bridging theorems (RBR⇒sound, FS, BCS) sorry/absent |
| (b) FS / NI security | VCVio Σ-protocol FS + forking lemma + Merkle ROM extractability; ArkLib definitions; Sumcheck (new framework) proven | FS for multi-round IOPs, BCS, FRI/STIR/WHIR soundness, proven-regime proximity gaps, concrete ε arithmetic |
| (c) Rust verifier ↔ Lean | Aeneas / hax-lean; OpenVM's Lean→C vendored verifier with CI byte-check (theorems private); Jolt HOL-Light byte-identity checker pattern | No finished binding of any real STARK verifier; wire-format decoders always trusted |
| Admission hygiene | openvm-fv (hygiene scan + `#audit_axioms` + comparator), ArkLib `axiomsweep` baseline | nanoda not enabled in openvm-fv's comparator config |

## 5. Backend trials on this host

See `checker-recommendations.md` §5 for the measured CPU-only install/prove results of SP1,
RISC Zero, Plonky3 and the transparent re-execution baseline.
