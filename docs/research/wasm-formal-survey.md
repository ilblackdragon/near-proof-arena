# Wasm formal semantics and zk-Wasm: state of the art (snapshot 2026-10-05)

> **Pinned-version note (lane v3-d3).** §0 below was checked against nearcore *master* (2026-10). For the
> pinned target, nearcore 2.13.4 / PV86, `docs/research/near-wasm-boundary.md` is authoritative. Two
> differences matter. First, 2.13.4 still ships the NearVM runner (MIN_SUPPORTED_PROTOCOL_VERSION = 83),
> but PV86 runs on Wasmtime. Second, the NaN question that §0 leaves open is settled: Wasmtime is configured
> with NaN canonicalisation, which Winch honours (boundary doc B3).

Scope: inputs for a Lean 4 executable reference semantics of NEAR contract execution, plus a STARK AIR whose
soundness is proved in Lean against that semantics. This builds on `docs/research/formal-ecosystem.md`
(2026-10-03), which covers SP1-Lean, openvm-fv, ArkLib, VCVio, zkLean, and risc0. That note has **no Wasm
coverage**. Nothing below repeats it.

Verification legend:
- **[checked]**: I inspected the repo or source myself (gh API, shallow clone, grep).
- **[web]**: the claim comes from a project page, paper page, or news item that I read but could not
  re-verify against an artifact.
- **[unverified]**: from memory or a search-engine summary only. Treat with care.

## 0. The NEAR target fragment (sets the scope for everything below) [checked]

`near/nearcore` master, file `runtime/near-vm-runner/src/features.rs` (last changed 2026-09-22):
- **Enabled:** floats, mutable globals, sign-extension, saturating float-to-int, and **reference types + bulk
  memory** (one flag, `REFTYPES_BULK_MEMORY = true`).
- **Disabled:** multi-value (the comment cites a wasmer singlepass limitation), SIMD, threads, tail calls,
  multi-memory, memory64, exceptions, GC, function references, relaxed SIMD, extended-const.
- **Runtime:** Wasmtime has been the only live VM since protocol 84. NearVM was removed in PR #15988
  (2026-07) and the minimum supported protocol version is 85.
- **Gas and stack metering:** done by `finite-wasm` 6 instrumentation (`prepare/instrument_v3.rs`). It
  injects a gas global, a stack global, and `gas_exhausted` / `stack_exhausted` / gas-instrumentation
  functions. Contract preparation also enforces table and element limits.
- **Not checked:** whether ref-types/bulk-memory is protocol-gated in historical versions. I also did not
  check NEAR's float NaN-canonicalisation policy under Wasmtime. Both need confirming before we freeze the
  Lean fragment.

**Implication.** The target is roughly "Wasm 1.0 + sign-ext + sat-trunc + ref-types/bulk-memory + IEEE
floats, single memory, no SIMD", plus finite-wasm's instrumentation semantics and the NEAR host-function
ABI. That is a Wasm 2.0 subset. Every 2.0 mechanisation below covers it. Wasm 3.0 features are irrelevant
today.

## A. Formal WebAssembly semantics

### A1. WasmCert-Coq (Rocq) and WasmRef-Coq
- **URL:** https://github.com/WasmCert/WasmCert-Coq. Releases v2.0.3 (2025-06-02), v2.1.0 (2025-06-29) and
  v2.2.0 (2025-08-20). Last push 2026-10-04. 126 stars. [checked]
- **Coverage:** Wasm 2.0 plus subtyping (from funcref/GC) plus tail calls. SIMD runs through the reference
  implementation's evaluation functions behind opaque opcodes, so SIMD is effectively unverified. Numerics
  come from CompCert's integer and float libraries. [checked README]
- **Proved artifacts:**
  - Type safety.
  - A type checker that is sound and complete.
  - Soundness of instantiation.
  - WasmRef-Coq, an extracted interpreter proved sound w.r.t. the relational semantics.
  - A "progressful" proof-carrying interpreter: Rao et al., POPL 2025,
    https://popl25.sigplan.org/details/POPL-2025-popl-research-papers/22/Progressful-Interpreters-for-Efficient-WebAssembly-Mechanisation.
    Designing/maintaining paper: https://vtss.doc.ic.ac.uk/publications/Rao2025Designing.html. [web]
- **Conformance:** README says it "is expected to pass all the core tests", and the official testsuite runs
  in CI (tail calls excluded). The binary parser is **unverified**. [checked README]
- **License:** custom copyright (Bodin, Gardner, Pichon, Watt, Rao 2019–2026). `src/Parray` is LGPL-2.1.
  GitHub reports NOASSERTION, so check `LICENSE.txt` before copying any code. [checked]
- **Program logics on top:**
  - Iris-Wasm (PLDI 2023): https://pldi23.sigplan.org/details/pldi-2023-pldi/46/Iris-Wasm-Robust-and-Modular-Verification-of-WebAssembly-Programs,
    repo https://github.com/logsem/iriswasm.
  - Iris-MSWasm (OOPSLA 2024): https://iris-project.org/pdfs/2024-oopsla-iris-mswasm.pdf.
  - Iris-WasmFX (PLDI 2026): https://cs.au.dk/~birke/papers/2026-pldi-iris-wasmfx.pdf. [web]
- **Relevance to us: HIGH, as a differential oracle and a spec cross-check.**
  - The extracted OCaml interpreter is a proved-sound oracle for our Lean interpreter on the NEAR fragment.
    Feed it the testsuite and NEAR contract corpora.
  - The CertiK zkWasm proofs (B2) already use WasmCert-Coq's auxiliary definitions as their spec, which
    is precedent for the approach.
  - A Rocq→Lean port is not mechanical; we would re-transcribe it.
- **Caveat:** CertiK found that the WasmCert-Coq commit they pinned (`3977eda`, older) lacked or got wrong
  sign-extension on load, `extend_s`, and shift/rotate mod-width. Those are fixed in 2.x, I believe
  [unverified]. Do not assume older pins are correct.

### A2. WasmCert-Isabelle and WasmRef-Isabelle
- **URL:** https://github.com/WasmCert/WasmCert-Isabelle. BSD-2-Clause. Isabelle2025-2 plus AFP. Last push
  2026-08-27. [checked]
- **Coverage and status:**
  - Updated to Wasm 2.0 reference types and bulk memory: Kalkauskas, WebAssembly Workshop @ SPLASH,
    2025-10-16, https://conf.researchr.org/details/icfp-splash-2025/webassembly-ws-2025-papers/9/Updating-WasmCert-Isabelle-to-WebAssembly-2-0. [web]
  - The refactor touched the soundness proof, the type checker, the interpreter, and instantiation.
  - Type soundness lives in `WebAssembly/Wasm_Soundness.thy`. [checked]
  - Branches `feat/ref-types*` and `feat/pbytes` exist. Whether all of it has landed on master is
    unverified.
- **WasmRef-Isabelle** (PLDI 2023, https://pldi23.sigplan.org/details/pldi-2023-pldi/5/WasmRef-Isabelle-A-Verified-Monadic-Interpreter-and-Industrial-Fuzzing-Oracle-for-We):
  a verified monadic interpreter, refined in two steps from the relational semantics. It is roughly as fast
  as a wasmi debug build. **It is deployed as Wasmtime's fuzzing oracle.** [web]
- **Older relaxed-memory / threads work:** Watt et al., "Weakening WebAssembly", OOPSLA 2019. [unverified;
  not needed, NEAR has no threads]
- **Relevance: HIGH for the oracle pattern.** "Verified interpreter as a differential oracle for a production
  engine" is exactly how we should test the Lean interpreter against Wasmtime. BSD-2 is the most permissive
  licence among the mechanisations. Isabelle is not Lean.

### A3. Official reference interpreter (OCaml) and SpecTec
- **Reference interpreter:** https://github.com/WebAssembly/spec, `interpreter/` (OCaml). It tracks Wasm 3.0.
  It is executable but deliberately slow (WasmRef-Isabelle's motivation). Licence: the repo LICENSE is a
  W3C/Apache-style file and GitHub reports NOASSERTION. [checked metadata]
- **Wasm 3.0:** completed 2025-09-17 and is the "live" standard: https://webassembly.org/news/2025-09-17-wasm-3.0/.
  It adds memory64, multi-memory, GC, typed function references, tail calls, exceptions, and relaxed SIMD.
  [web]
- **SpecTec:**
  - Adopted 2025-03-27: https://webassembly.org/news/2025-03-27-spectec/.
  - Paper: PLDI 2024, https://dl.acm.org/doi/10.1145/3656440.
  - The Wasm 3.0 spec text is generated from it.
- **Backends on `WebAssembly/spec` main** [checked]: `backend-latex`, `backend-prose`, `backend-splice`,
  `backend-ast` (S-expr IL dump), and `backend-interpreter` (a meta-interpreter over the AL that runs .wast).
  **There is no ITP backend on main.**
- **ITP backends in the dev repo** https://github.com/Wasm-DSL/spectec [checked]:
  - `rocq-backend`: PR #207, open since 2025-11-19, last commit 2026-09-22.
  - `mech-backend` / "Mechanization backend - stable branch": PR #234, open, last commit 2026-09-21
    (D. Cupello).
  - `isabelle-mech-backend`: last commit 2026-10-02 (Zilin Chen).
  - "[IL Semantics] Meta-theory in rocq": PR #222, open.
  - An Agda experiment (2023; also https://github.com/peterthiemann/wasm-spectec-experiment).
- **SpecTec → Lean 4** [checked]:
  - Branch `lean4-wip`, PR #192, "Lean4 wip", open since 2025-11-07. Last commit 2026-02-19 by Joachim
    Breitner: "Rebase the lean4 wip code onto rocq-backend".
  - Adds `spectec/backend-lean4/print.ml`, a CI job `ci-lean.yml`, and the generated
    `spectec/test-lean4/Wasm.lean`, pinned to `v4.25.0-rc1`.
  - I downloaded that file: 10,790 lines, generated from `specification/wasm-3.0/*.spectec`. It contains 515
    `inductive` and 266 `def` declarations and the relational `Step_pure` / `Step_read` / `Step`
    relations, with 117 `opaqueDef` placeholders and 0 `sorry`.
  - According to OathTech's notes (next bullet) it **does not currently compile**.
  - It is **relational, not executable**. It is Prop-valued inductive step relations for the whole of 3.0,
    including GC and exceptions.
- **OathTech/spectec-lean**, https://github.com/OathTech/spectec-lean (no licence, 0 stars, created
  2026-08-20, last push 2026-08-21) [checked]:
  - A deep embedding of SpecTec's IL in Lean with a "rule-direct" executable engine, differentially tested
    against the OCaml toolchain on the Wasm spec.
  - Its TODO says the engine is "correct on the pilot corpus but ~1s/Step". Its first client is a Go
    frontend.
  - Toolchain v4.33.0.
- **Related, P4 not Wasm:** qobilidop/p4-spectec-lean (https://github.com/qobilidop/p4-spectec-lean), a
  "P4-SpecTec to Lean 4 certifying compiler" from P4-SpecTec's AL. It shows an AL→Lean route that might be
  reused for Wasm.
- **Relevance: MEDIUM now, potentially HIGH later.**
  - A compiling, executable SpecTec→Lean output would let us state "our Lean semantics refines the official
    spec" for the NEAR fragment.
  - Today the backend is WIP, relational, non-compiling, pinned to an old toolchain, and covers all of 3.0
    (which is much larger than we need).
  - Practical plan:
    - Write our own small executable Lean semantics.
    - Use the SpecTec meta-interpreter (`--interpreter t.wast`) and the OCaml reference interpreter as
      oracles.
    - Track `lean4-wip`, and later prove (or test) per-instruction agreement with the generated relations.

### A4. Lean 4 WebAssembly formalisations
I cloned each repo shallowly and counted Lean LOC and `sorry` with grep, excluding comments roughly.

| Project | URL | Status | Coverage | Exec | Proofs | License |
|---|---|---|---|---|---|---|
| **Talos** (Cajal Technologies, YC W26) | https://github.com/cajal-technologies/talos | created 2026-05-20, very active (push 2026-10-05), 182★, Lean v4.34.1 | aims at full Wasm; `testsuite_report.txt`: 64,751 pass / 79 rejected / 27 decode_error / 18 module_unavailable / 267 skipped (assert_unlinkable, exhaustion, non-integer). Includes memory64 and GC tests, plus SIMD/IEEE754 modules | yes (`lake exe runner`, fuel) | WP calculus; Rust→Wasm verification tasks (`programs/`, ~97k LOC); migrating to one relational `Step` plus a proved-equivalent `step?` with iris-lean (`IirisMigration.md`); 6 grep hits for `sorry`, mostly codegen strings | **AGPL-3.0** |
| **linobit-corp/wasm-lean** | https://github.com/linobit-corp/wasm-lean | 2026-04-16→04-25 (dormant?), 0★, Lean v4.15.0 | Wasm 1.0 MVP, ported from WasmCert-Coq; claims 14,342/14,342 MVP spec assertions | yes (fuel) | `execBlock_sound` (interpreter ⇒ `ReduceStar`), claimed axioms only `propext`/`Quot.sound`; type system; **floats are a phantom `Unit` in `Values.lean`** (semantics via a typeclass); 1 `sorry` grep hit | MIT |
| **T-Brick/lean-wasm** ("WasmLean") | https://github.com/T-Brick/lean-wasm | 2023→2025-11, 34★, v4.25.0 | syntax, validation, partial dynamics, binary/text; no vectors, floats unimplemented | wasm→wat only | 34 `sorry` | GPL-3.0 |
| **aionescu/lean-wasm** (Utrecht MSc, "LeanWasm") | https://github.com/aionescu/lean-wasm ; thesis https://studenttheses.uu.nl/handle/20.500.12932/46861 ; talk https://www.cse.chalmers.se/research/group/security/event/2024/2024-06-12-alex | last code 2024-07 | intrinsically-typed interpreter, small subset | yes | 8 `sorry`, 1.5k LOC | GPL-3.0 |
| **pmatos/wean** | https://github.com/pmatos/wean | 2025-12-17/18 only, 1★ | claims "proved correct Wasm 3.0 runtime"; ~6k LOC, 0 `sorry` | yes | small | none |
| **argumentcomputer/Wasm.lean** (Yatima/Lurk) | https://github.com/argumentcomputer/Wasm.lean | abandoned 2023, nightly-2023-01 | WAST parser, runtime | yes | none | MIT |

- **Searched and found nothing:**
  - Wasm work by Galois, Veridise, Nethermind, ZKsync, zkLean, Lean-MLIR, or AWS.
  - "Interaction trees Wasm". (Wasm-Logic exists as Watt et al., ECOOP 2019, in Isabelle [unverified].)
  - The search-engine claim of a "Lean 4 formally-verified Wasm interpreter" traced back to LeanWasm /
    Talos.
- **Also seen** (0★, not inspected):
  - theebayuser/verified-binaries (Talos-based).
  - DaviRain-Su/ProofForgeNear, a Lean→NEAR-Wasm compiler. That is the opposite direction from ours.
- **Relevance:**
  - **Talos** is the most complete executable Lean Wasm semantics today, and its WP layer is useful.
    - **AGPL-3.0 is a blocker** for vendoring it into our certificate unless Cajal relicenses. Ask them.
    - It is a moving target (an iris-lean migration is in progress) and it runs at interpreter speed with
      no performance focus.
    - It is a good **differential oracle** (Lean-to-Lean, so it could even support proved equivalence on
      the fragment).
    - Its testsuite runner and miscast/V8 differential harness are reusable patterns.
  - **linobit wasm-lean** is MIT and has the right shape for us: executable interpreter plus relational
    semantics plus soundness theorem, Wasm 1.0. It is tiny (14k LOC) and abandoned, floats are not real, and
    there is no ref-types/bulk-memory, sign-ext, or sat-trunc. It is a plausible **starting skeleton** if
    we accept porting cost. Re-run its claims before trusting them; I did not build it.
  - The others are too partial to matter.

### A5. Takeaways for L-stack design (our inference, not a claim from the projects)
- No existing artifact gives us "Lean 4 + executable + NEAR fragment + permissive licence + maintained".
  Expect to **write the reference semantics ourselves**, at roughly 10–20k Lean LOC for the fragment plus
  host ABI plus finite-wasm metering.
  - Model the structure on WasmCert (relational `Step` plus an executable interpreter proved sound).
  - Test it against:
    - the official testsuite restricted to the NEAR features;
    - the WasmCert-Coq extracted interpreter, WasmRef-Isabelle, and the SpecTec meta-interpreter;
    - Wasmtime, which is NEAR production.
- Floats are the main semantic risk: NaN bit patterns and determinism under Wasmtime. Decide early whether
  the fragment we prove forbids floats (contract-level validation) or models IEEE fully. Talos's
  `IEEE754.lean` and linobit's bfloat-lean are possible sources.
- **Gas metering:** the semantics to prove is "Wasm semantics of the finite-wasm-instrumented module", or
  equivalently a native gas-counting semantics plus a proof that instrumentation preserves it. Nobody has
  formalised finite-wasm [unverified absence].

## B. zk proving of WASM

### B1. zkWasm (Delphinus Lab)
- **Repo:** https://github.com/DelphinusLab/zkWasm. Apache-2.0 (plus MIT badge), 544★, last push 2026-02-10.
  [checked]
- **Paper:** "ZAWA/zkWasm: A ZKSNARK WASM Emulator", IEEE Transactions on Services Computing (2024),
  https://ieeexplore.ieee.org/document/10587123. LaTeX source at https://github.com/DelphinusLab/zkwasm-paper
  (last commit 2023-09-27). [checked source]
- **Architecture** (from the paper source and the CertiK README) [checked]:
  - **Proof system:** Halo2 with KZG over BN254. Not a STARK.
  - **Execution:** Wasmi (a Delphinus fork) runs the program and also *compiles* Wasm into Wasmi's flat ISA:
    structured control flow becomes gotos, implicit returns become an explicit `return`, and locals live on
    the value stack. **The circuits prove execution of this IR, not of Wasm.**
  - **Tables:**
    - `ETable`: one execution step per block of rows. The paper says **4 rows per instruction**. 27
      opcode-class selectors.
    - `MTable`: memory, globals, locals and stack. Rows are `(eid_start, eid_end, addr, value, …)`, kept
      sorted by address then eid, with read/write consistency via lookups.
    - `JTable`: call frames.
    - `RTable`: range and byte-op tables.
    - `bit_table`: AND/OR/XOR/popcnt by bytes.
    - `image_table`: code and initial data.
  - **Uniqueness:** an ETable-vs-MTable entry **count equality** ("mops") rules out extra MTable rows.
  - **Host functions:** foreign/host circuits (https://github.com/DelphinusLab/zkWasm-host-circuits) handle
    hashes and ECC via a `call_host` op.
  - **Large traces:** continuations split the execution into segments with state columns, then batch the
    segment proofs (https://github.com/DelphinusLab/continuation-batcher).
- **Relevance: HIGH as an AIR template.** The table decomposition and the "count equality instead of a
  permutation argument" trick map well onto our L4 DSL. Our differences:
  - We use STARK/FRI over BabyBear rather than KZG/BN254, so i64 values need limb decomposition. zkWasm
    relies on the ~254-bit field to hold u64 directly.
  - We need a proof of the Wasm→flat-IR translation, which they do not have.

### B2. Formal verification of zkWasm (CertiK, Coq)
- **Repo:** https://github.com/CertiKProject/zkwasm-fv. Last commit 2026-09-19. LICENSE.txt (GitHub reports
  NOASSERTION). [checked]
- **Announcements:**
  - 2024-04-29 blog: https://www.certik.com/resources/blog/advanced-formal-verification-of-zero-knowledge-proof-blockchains.
  - Follow-up posts on instruction, memory and bugs. The "two bugs" post:
    https://www.certik.com/blog/advanced-formal-verification-of-zkp-a-tale-of-two-zk-bugs.
  - 2025-09-28 press coverage, e.g. https://coinstats.app/news/8d7064c106e4712ae6022e36736d4db62d3c456cd90e3d9b7e4bf9f7b6343a99_CertiK-Says-Coq-Proofs-Show-zkWasms-Core-Circuits-Are-Sound.
    It states ~33k lines of Coq, ~21k of them proofs, and says the public repo "replaces the proofs with
    placeholders". [web]
  - The README cites a paper, "Formal Verification of zkWasm, a General-Purpose zkVM". I could not find its
    venue [unverified].
- **What is in the public repo** [checked; I did not build it]:
  - 46.7k lines of `.v`, ~1.3k `Proof.` occurrences, and only **2 `Admitted`** (`InjectivityHelper.v:539`,
    `OpConversion.v:300`).
  - **So the public repo does contain proofs**, which contradicts the press report. Possibly the release
    changed. Building it with Coq 8.17.1 plus WasmCert-Coq@`3977eda` would settle this.
- **Main theorems** in `Wasmi.v`:
  - `knowledge_soundness`: for every enabled ETable row `i` with `state_rel 0 init_st`, there is a state
    `st_i` with `steps_list init_st … st_i ∧ state_rel i st_i`.
  - `soundness`: the corollary.
- **Spec:** `WasmiModel.v`. This is a small-step semantics of the **Wasmi IR**: pc = (fid, iid), stack of Z,
  globals, `Wasm.datatypes.memory` from WasmCert, and a call stack. It reuses WasmCert-Coq's numerics and
  memory operations.
- **Method:**
  - Each `*Model.v` hand-translates the Halo2 gates into `Axiom`s over `Parameter` tables (546
    Axiom/Parameter declarations).
  - The allocator and range-check lookups are **trusted and axiomatised**.
  - Field arithmetic is mostly treated as integers. `pgate` forces a non-overflow proof only where judged
    necessary.
  - Wasmi behaviour assumptions are axiomatised.
- **Scope:** every zkWasm instruction class except `call_host_foreign_circuit` is done.
- **Out of scope:** Halo2 itself (the proof system and the lookup/permutation arguments), Wasmi (both the
  Wasm→IR compiler and witness generation), the allocator, and the instruction decoding logic (audited
  manually instead, per press coverage).
- **Bugs found:** two soundness bugs, a missing constraint on memory load and a fake `return`.
- **Relevance: VERY HIGH. This is the closest prior art to our L6-for-Wasm.**
  - Reuse: the proof architecture (`state_rel` per row, per-opcode lemmas, MTable `gather_entries` map
    abstraction, mops counting for uniqueness, and the JTable well-formedness invariant).
  - Things we must do better to meet our admission bar:
    1. Extract constraints mechanically from the AIR rather than hand-translating them. Our L4 DSL already
       does this.
    2. No axioms for range checks or lookups. Prove them from the L4 `Holds`.
    3. Use modular field arithmetic everywhere.
    4. Cover the Wasm→IR translation, or prove directly against structured Wasm.
    5. Connect to proof-system soundness (our L2/L3).
- **Zellic involvement:** I found no evidence that Zellic formally verified zkWasm [not found].

### B3. Fluent / rWasm
- **Repos:**
  - https://github.com/fluentlabs-xyz/rwasm: Apache-2.0, active (push 2026-10-05), crates.io `rwasm` 0.4.x.
  - https://github.com/fluentlabs-xyz/fluentbase: Apache-2.0. [checked]
- **Design:** rwasm validates standard Wasm and translates it to **rWasm**, a flat, reduced instruction set.
  Structured control flow is compiled away. There are two backends: an interpreter and a Wasmtime fork. The
  fuel policy is shared, and module bytes are fully determined by the input plus a 32-byte codegen identity.
  Opcode spec: `docs/opcodes.md`. [checked README]
- **Fluent L2:** EVM and Wasm contracts both compile to rWasm, "proven by one ZK circuit". Blog claims
  (https://hackmd.io/@dmitry123/BJd62jR3lg, undated):
  - "50×–10,000× trace reduction vs SP1+Wasm";
  - floats eliminated.
  [web]
- **Which prover proves rWasm in production is not stated in the READMEs I read.** fluentbase pins
  `sp1-curves` and has a "Run Sp1" benchmark column, which suggests SP1 is involved somewhere
  [unverified].
- **Relevance: MEDIUM.**
  - rWasm is an industrial example of "flatten Wasm to a zk-friendly IR".
  - The translation is **unverified**.
  - It removes floats, which may or may not suit NEAR contracts.
  - Its opcode spec is a useful reference for our own flat IR, if we choose one.

### B4. Wasm inside RISC-V zkVMs (RISC Zero, SP1, OpenVM, Jolt)
- **RISC Zero:** official example `examples/wasm` runs a wasmi interpreter in the guest
  (https://github.com/risc0/risc0/tree/main/examples/wasm). It publishes no cycle numbers. [checked]
- **SP1:** https://github.com/succinctlabs/overhead (2025-03/04; wasmi 0.42.1, SP1 4.1.0). Measured cycles
  are in C2. [checked]
- **OpenVM and Jolt:** I found no first-party Wasm frontends [not found].
- **Soundness story of this route:** the Wasm semantics is never stated. The guarantee is "the RISC-V trace
  of wasmi is valid". You would additionally need a verified wasmi, which does not exist, or a verified
  Wasm→RISC-V compiler (B6).
- **Relevance:** a fallback route and cost baseline only. It does not fit our "AIR soundness vs Lean Wasm
  semantics" goal unless paired with a Lean RISC-V spec (sail-riscv-lean, as used by openvm-fv) **and** a
  proved Wasm interpreter or compiler to RISC-V.

### B5. Other zk-Wasm efforts
- **zkEngine** (ICME Labs): https://github.com/ICME-Lab/zkEngine_dev. Apache-2.0, last push 2025-10-28. A
  Nova/NIVC folding zkWasm, Nebula scheme (https://eprint.iacr.org/2024/1605), used as the NovaNet backend.
  No formal verification. [checked]
- **Polygon Miden compiler:** https://github.com/0xMiden/compiler (MIT, active). A Wasm frontend lowers to
  HIR, then to Miden Assembly, which is proved by the Miden STARK VM. No correctness proofs. [checked]
- **powdr:** https://github.com/powdr-labs/powdr. Now "performance and security acceleration for zkVMs"
  (autoprecompiles, formal verification of constraints). I found no Wasm frontend. [checked README; absence
  unverified]
- **Nexus zkVM:** https://github.com/nexus-xyz/nexus-zkvm. RISC-V on Stwo. I found no evidence it was ever
  Wasm-based [unverified absence].
- **Small/dead projects:**
  - orochi-network/zkWASM (2023);
  - Riemannstein/zkWasmi (2022);
  - privacy-ethereum/zkvm-ideas (zkWasm team residency notes).

### B6. Verified Wasm compilers and sandboxers (Wasm → native)
- **vWasm** (F*, verified *sandboxing safety*, not full semantic preservation, x86-64) and **rWasm** (a
  Wasm→safe-Rust transpiler, unrelated to Fluent's rWasm). Bosamiya, Lim, Parno, USENIX Security 2022:
  https://usenix.org/conference/usenixsecurity22/presentation/bosamiya. [web]
  - Relevance: low. The proved property is sandboxing, not semantics.
- **Cranelift instruction-selection verification:**
  - VeriISLE/Crocus (ASPLOS 2024): https://docs.wasmtime.dev/api/crocus/index.html.
  - **Arrival** (OOPSLA 2025): "Scaling Instruction Selection Verification against Authoritative ISA
    Semantics", https://2025.splashcon.org/details/OOPSLA/69. Covers nearly all AArch64 lowering rules
    reachable from Wasm core and is SMT-based. [web]
  - These are per-rule lowering checks and do not give end-to-end Wasm semantics.
  - Relevance: low for proofs. Wasmtime is NEAR's production engine, so this tells us about the
    trustworthiness of the thing we test against.
- **Synth** (PulseEngine): https://github.com/pulseengine/synth. Apache-2.0, created 2025-11, very active, 3★.
  [checked README]
  - A Wasm→ARM Cortex-M / RV32IMAC / AArch64 AOT compiler.
  - **Rocq proofs of i32/i64 instruction-selection result correspondence**, with existence-only proofs for
    float/SIMD.
  - Per-compilation SMT translation validation.
  - Pre-release. The proofs cover instruction selection, not whole-module semantic preservation [inferred
    from README wording].
  - **The only verified-ish Wasm→RISC-V compiler I found.** Too immature to rely on, but worth watching if we
    ever consider the "Wasm→RV32 + openvm-fv" route.
- **CertiCoq-Wasm** (CPP 2025): https://popl25.sigplan.org/details/CPP-2025-papers/9/CertiCoq-Wasm-A-verified-WebAssembly-backend-for-CertiCoq.
  A verified Coq→Wasm compiler against WasmCert-Coq. Wrong direction for us, but it shows WasmCert-Coq used
  as a compiler-correctness target. [web]
- **wasm2c / w2c2:** I found no correctness proofs [not found].
- **Searched with no hits:** CompCert-style or CakeML Wasm→RISC-V compilers, Vericert (an HLS tool,
  unrelated), and "Kaplan" [not found].

## C. Cost / scale data points

| Source | Setting | Number |
|---|---|---|
| zkWasm paper `chapters/bench.tex` [checked] | Halo2/KZG, Ryzen 7 5800X3D + **RTX 4090**, 128 GB | **4 ETable rows per Wasm instruction.** Single segment 2^22 rows ≈ 0.86–0.97 M instructions, proof ≈ 82–84 s, verify 29 ms. 2^20 rows: 150–240 k instructions, 20 s. Batching: 2^24 batch circuit with 8 segments, 192 s. Claimed steady state **≈ 2^15 ≈ 32 k Wasm instr/s** (2023 code) |
| Logos zkVM testing report (2024-09-26) [web] https://research.logos.co/rlog/zkVM-testing/ | zkWasm, CPU-only EPYC 7713 | Hept-100: 42.7 s, **18 KB proof**, 8.2 GB RAM. Vec-10000: 323 s, **334 KB proof**, 58.8 GB RAM. Rated the worst of the candidates tested |
| Search-engine summary attributed to an X post (Dec 2024) [unverified] | zkWasm, recent GPU prover | "~1 M Wasm instructions in ~14 s" (~71 k instr/s). Could not open the source (402) |
| succinctlabs/overhead [checked] | SP1 4.1.0, wasmi 0.42.1, Fibonacci loop of 18 Wasm instructions per iteration | u32, n=1000: interpreter loop 307,625 cycles ≈ **~17 RV32 cycles per Wasm instruction**; total 347 k vs native Rust 16.9 k (**~20×**). u64, n=10000: 3.87 M cycles ≈ **~21.5 cycles per instruction** (i64 on RV32); native 125 k (**~31×**). Fixed setup ≈ 37 k cycles. (EVM via revm is 130–830× native, for comparison) |
| rWasm blog [web, undated] | Fluent | "2× faster than wasmi" execution; "50×–10,000× trace reduction vs SP1+Wasm" (marketing; no methodology) |
| CertiK zkwasm-fv [checked] | Coq | 46.7 k lines `.v` public (press: 33 k internal, 21 k proofs); ~6 k lines of Halo2 circuit Rust translated |

**Back-of-envelope for us** (our inference):
- **zkWasm-style AIR:** ~4 rows × width per Wasm instruction, plus MTable rows (1–3 per instruction) and
  range/bitwise lookups.
- **wasmi-in-RISC-V:** ~17–22 RISC-V rows per Wasm instruction, plus memory/bus overhead per RISC-V row.
- So a direct Wasm AIR should be roughly 4–6× fewer rows per Wasm instruction than wasmi in a RISC-V
  zkVM, before counting width.
- BabyBear limbs for i64 will inflate width relative to zkWasm's BN254 cells. Our `W_eq ≤ 3000` budget
  (DESIGN.md §5.2) needs a separate Wasm table budget.
- The SP1 figures exclude proof time. The zkWasm figures are 2023 GPU numbers. Neither is directly
  comparable to our CPU UDR-STARK.

## D. Bottom line for nearproof
1. **Reference semantics (new lane, alongside L6):**
   - Write our own Lean 4 executable semantics for the NEAR fragment (§0), structured like WasmCert:
     relational step, executable `step?`, and a soundness proof between them.
   - Borrow the skeleton from linobit wasm-lean (MIT). Do not use Talos code unless it is relicensed
     (AGPL).
   - Oracle-test it against WasmCert-Coq's extracted interpreter, the SpecTec meta-interpreter, the OCaml
     reference interpreter, Wasmtime (production), and Talos.
2. **SpecTec→Lean:** watch `Wasm-DSL/spectec` PR #192 (`lean4-wip`). If it compiles, prove per-instruction
   agreement on the fragment, which buys "matches the official spec" for the semantics TCB.
3. **AIR:**
   - Adopt zkWasm's ETable/MTable/JTable structure and CertiK's proof architecture (state_rel, mops counting,
     gather_entries).
   - Remove every CertiK axiom (allocator, ranges, lookups, integer-vs-field) by building on L4 `Holds` and
     L2/L3.
   - Decide early: either prove against structured Wasm directly (a label/block stack in the AIR), or
     introduce a flat IR (à la Wasmi/rWasm) plus a **proved Lean Wasm→IR translation**. The latter is the
     gap that zkWasm, rWasm and wasmi-in-zkVM all leave open.
4. **Not to pursue as the primary route:** wasmi-in-SP1/OpenVM. It has no Wasm semantics theorem, and it is
   ~17–22 RISC-V cycles per Wasm instruction.
