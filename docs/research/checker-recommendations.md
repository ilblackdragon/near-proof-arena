# Checker and toolchain recommendations for formal-core

Status: research recommendation, 2026-10-03. Companion to `formal-ecosystem.md` (which has the
per-project evidence, commit hashes and hole counts). Every command below was **run on this host**
(AMD 9950X3D, 32 threads, 125 GB RAM, Linux 6.8, no GPU) unless marked otherwise. Scratch
experiments live under
`/tmp/claude-1002/-data-illia-nearproof/29f86fd5-cfb7-44c7-996e-70d81e3d17a4/scratchpad/`
(`ktest/`, `cmp/<case>/`, `xver/`, `seccalc/`, `hashchain/`), and build trees under
`/data/illia/nearproof-deps/`.

## 1. Lean toolchain to pin for formal-core

**Recommendation: pin `leanprover/lean4:v4.35.0` as soon as it is released; develop now on
`v4.35.0-rc3`** (= Mathlib master's toolchain at snapshot). Do not pin v4.34.x or older.

Reasons:

1. **v4.35.0-rc1+ bundles an entire independent-checking suite in `bin/`** (verified with `ls
   ~/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/`): `leanexport` (= lean4export 3.1.0,
   byte-identical output to the repo build), `leanchecker`, `leanchecker-paranoid`, `lean4lean`,
   `nanoda_bin` (0.4.17), `con-leche` (a new Lean-written checker whose `--verified` mode is
   accompanied by a claimed machine-checked theorem `ConLeche.no_proof_of_False`), and `con-ron`
   (Rust port). v4.34.1 ships only `leanchecker`.
2. **`lake comparator` and `lake check` are built in** (v4.35): they build/export the untrusted
   project inside a `bwrap` sandbox (read-only `/`, homes hidden, only `.lake` writable, network
   only for dependency resolution) and never load candidate `.olean`s into Lake's address space.
   `--paranoid` runs all bundled kernels. `--challenge-from-export/--solution-from-export`
   accept exports produced elsewhere (e.g. in a throwaway VM).
3. **`native_decide` changed in v4.29.0**: it no longer goes through `Lean.ofReduceBool` /
   `Lean.trustCompiler` (these constants no longer exist in 4.35); each use adds a fresh axiom
   `<decl>._native.native_decide.ax_N_M : decide (...) = true`. A strict whitelist
   `{propext, Quot.sound, Classical.choice}` rejects both old and new forms — confirmed by
   comparator test `native` below.
4. ArkLib/VCVio (v4.34.0) are one minor version behind and track Mathlib closely; Clean is on
   v4.33.1; Aeneas/hax on v4.31.0; sp1-lean v4.28.0; openvm-fv v4.26.0. None is on 4.35 yet,
   but formal-core should not *import* any of them initially (see §2); importing later means
   bumping them (ArkLib/VCVio bumps are routine; Aeneas publishes nightly tags per Lean bump).

Policy: one toolchain for formal-core + challenge files + checker. Candidate certificates must
be built with **exactly** that toolchain (`.olean` format is toolchain-specific; NDJSON export
format 3.1.0 has been stable from v4.26.0 through v4.35.0-rc3, but con-leche keeps per-toolchain
"pins" and declines unknown ones, and the bundled lean4lean's `.olean` mode fails on non-matching
headers). Toolchain bumps are an arena-governance event, re-running all admitted certificates.

## 2. Mathlib: depend or not?

**Recommendation: formal-core (the arena-owned statement layer) should NOT depend on Mathlib.
Allow candidate certificates to depend on a Mathlib revision pinned by the arena** (same rev for
everyone, the one matching the pinned toolchain), and check them via per-theorem export so the
cost does not hit the checker.

| | Without Mathlib in formal-core | With Mathlib in formal-core |
|---|---|---|
| Statement TCB (what a reviewer must read) | Init/Std + our defs; small | + every Mathlib definition the statements mention (ZMod, Polynomial, PMF/ENNReal, Finset.sum…) |
| Build | seconds | `lake exe cache get` (~1–2 min) + any non-cached deps; CertiPlonk's tiny project: 3m24s, 10 GB RSS |
| Toolchain agility | trivial bumps | Mathlib dictates the toolchain schedule (fine at 4.35, since Mathlib master is on it) |
| Checker cost | small exports | per-theorem exports still fine; whole-environment exports expensive (`lake check --paranoid` on a trivial project already took 235 s because it exports all of Init) |
| Expressiveness for crypto statements | must define our own `ZMod`-free field model, probabilities as `Rat`/`Nat` counts | VCVio/ArkLib-style `Pr[...]`, `PMF`, `ZMod p`, polynomials available |
| Independent kernels | nanoda failed on `Std` (stack overflow; >100 GB at 1 GB stacks on `Std.Time.*` `_proof_1` lemmas) — Mathlib-scale whole exports are risky for nanoda | same risk, larger |

Concretely: formal-core states the **NEAR semantics** (block/chunk application as a pure Lean
function over byte strings, state root, receipts) and the **admission theorem shape** using only
Lean core (`Nat`, `Fin`, `ByteArray`/`List UInt8`, `Rat` for ε). The cryptographic part of an
admission certificate is phrased against a small arena-owned interface (§4) whose
probability notion is elementary (exact counting over a finite oracle-table space, or a minimal
`PMF`-free distribution monad). Candidates are free to prove it using Mathlib/VCVio/ArkLib; the
checker only compares the *statement* (which mentions only formal-core constants) and replays
the proof term with the axiom whitelist. Comparator compares "every constant they mention", so
keeping Mathlib out of the statement keeps the audited surface small.

If the formal-core team later wants VCVio's `OracleComp`/`Pr` in the statement itself (more
standard, easier for candidates), import **VCVio only** (it pulls Mathlib + PolyFun + cslib) and
accept the Mathlib pin; still avoid ArkLib in statements (171 sorries, module-system quirks).

## 3. Independent re-checking of exported proofs — what works today

### 3.1 Tool status (hands-on, v4.35.0-rc3 unless noted)

| Tool | Build / source | Axiom policy | Result on adversarial suite | Scaling (Init 58k decls / Std 97k decls) |
|---|---|---|---|---|
| `leanexport` / lean4export (`66f1fb4b`) | bundled; repo `lake build` 5.6 s | – | – | full export always includes all of Init: 345 MB / 6.45 M lines / ~10 s; **per-theorem export 0.4 s, 200–10k lines** |
| `leanchecker` (formerly lean4checker repo, deprecated since v4.28) | bundled | **none** (accepts sorry/native/custom axioms) | rejects `evil` only | Init 42 s / 0.6 GB; Std 69 s |
| `leanchecker-paranoid` | bundled | none | rejects evil | Init 60 s |
| `nanoda_bin` / nanoda_lib (`3a240721`; repo `cargo build --release` 12 s) | bundled 0.4.17 / repo 0.4.19 | `permitted_axioms` + `unpermitted_axiom_hard_error` | rejects sorryAx, myAx, native axiom (exit 1), evil (panic, exit 101) | Init 4–5.5 s / 0.6 GB; **Std: fails (stack overflow)** |
| `lean4lean` (`8223d223`; repo build 33 s on v4.33.0-rc2) | bundled (use `--import FILE.ndjson`; olean mode broken on 4.35) | none | rejects evil | Init 77 s; Std 92 s |
| `con-leche` / `con-ron` | bundled | declines any non-standard axiom (exit 2) | sorry/myAx declined (2), evil invalid (1) | Init 15 s / 19 s; Std 24 s / 30 s |
| comparator (repo `fd5d5bcf`, or built-in `lake comparator`) | repo `lake build lean4export comparator` 12 s; landrun sandbox (Landlock ABI v9 wanted, kernel 6.8 has v4 → `--best-effort`) | `permitted_axioms` | see 3.3 | per-theorem: 2–21 s per case |

Exit codes to treat as reject: **any non-zero** (nanoda: 1 policy, 101 panic; con-*: 1 invalid,
2 declined, 3 usage).

**`#print axioms` inside the candidate's environment is not trustworthy**: the `evil` case
(false theorem admitted through `set_option debug.skipKernelTC true`) printed "does not depend
on any axioms" yet all six kernels rejected the export. Never rely on in-environment reporting
(this also invalidates README claims and in-build `#audit_axioms` gates as *sole* evidence).

### 3.2 Commands (tested)

```bash
# toolchain
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
elan toolchain install leanprover/lean4:v4.35.0-rc3

# per-theorem export (preferred; avoids Init's own sorryAx/trustCompiler declarations)
lake env leanexport <RootModule> -- <thm1> <thm2> > sol.ndjson     # format 3.1.0, meta header w/ Lean githash

# nanoda
cat > nanoda.json <<'EOF'
{"export_file_path":"sol.ndjson","permitted_axioms":["propext","Classical.choice","Quot.sound"],
 "unpermitted_axiom_hard_error":true,"nat_extension":true,"string_extension":true,
 "num_threads":16,"pp_to_stdout":true,"print_success_message":true}
EOF
nanoda_bin nanoda.json

# Lean kernel replay of the same export, and other independent kernels
leanchecker --from-export sol.ndjson
lean4lean --import sol.ndjson
con-ron sol.ndjson         # or: con-leche --verified sol.ndjson

# replay from oleans (same-kernel defence against environment hacking only)
lake env leanchecker --fresh <RootModule>

# full judge: arena-owned Challenge.lean + config, candidate Solution
lake update && lake comparator --config comparator.json --paranoid
# or with exports produced in an isolated VM:
lake comparator --config comparator.json --challenge-from-export ch.ndjson --solution-from-export sol.ndjson --paranoid
```

comparator config:

```json
{"challenge_module":"Challenge","solution_module":"Solution",
 "theorem_names":["NearArena.admission"],
 "definition_names":[],
 "permitted_axioms":["propext","Quot.sound","Classical.choice"]}
```

### 3.3 Adversarial comparator suite (`scratchpad/cmp/`) — both repo comparator and built-in `lake comparator --paranoid` agree

| Case | Verdict |
|---|---|
| ok | accepted by all 6 kernels (15.5 s) |
| native (`native_decide`) | `Illegal axiom detected: 'mul_small._native.native_decide.ax_1_1'` |
| sorry | `Illegal axiom detected: 'sorryAx'` |
| customax | `Illegal axiom detected: 'cheat'` |
| mismatch (different statement) | `Challenge and solution theorem statement do not match` |
| shadow (instance redefining `+`) | statement mismatch detected |
| evil (`debug.skipKernelTC` false theorem) | rejected by all 6 kernels |

### 3.4 Version compatibility for third-party certificates on older toolchains

| Toolchain | Exporter | nanoda | con-* (from 4.35) | lean4lean (from 4.35) | leanchecker |
|---|---|---|---|---|---|
| v4.28.0 (sp1-lean) | lean4export tag v4.28.0 | per-decl OK; full Init overflows | full Init declined (no pin); per-decl OK | per-decl OK | OK |
| v4.33.x (clean) | tag v4.33.0 | per-decl OK (full Init needs `Lean.trustCompiler`) | OK | per-decl OK, full fails (`Decidable.intro`) | OK |
| v4.34.0 (ArkLib/VCVio) | tag v4.34.0 | as 4.33 | OK | as 4.33 | OK |
| v4.35.0-rc3 | bundled | OK (except Std scale) | OK | OK | OK |

### 3.5 Recommended admission pipeline

1. **Arena owns** `Challenge.lean` (statements importing only formal-core), lakefile, toolchain
   and `comparator.json`. Challenge is compiled in a clean environment first.
2. **Build + export the candidate in isolation** (bwrap via `lake comparator`, preferably inside
   a disposable VM/container with no network after dependency fetch; run as unprivileged user;
   cgroup memory/time limits). Candidate tactics/plugins/elaborator extensions run only here.
3. **Per-theorem exports only** (comparator does this). Store the exported NDJSON + sha256 as
   the admission record; the record, not the `.olean`s, is what is re-checked.
4. **≥3 independent kernels on the export, outside the sandbox**: Lean C++ kernel
   (`leanchecker --from-export`), nanoda (hard-error axiom policy), con-ron or lean4lean.
   `--paranoid` runs all six. Accept only if *all* accept.
5. **Axiom whitelist enforced three times** (comparator, nanoda, con-*): exactly
   `{propext, Quot.sound, Classical.choice}`. Reject `sorryAx`, any `*._native.native_decide.ax_*`,
   `Lean.ofReduceBool`, `Lean.trustCompiler`, any other axiom. Cryptographic assumptions are
   **never** axioms: they are hypotheses of the admission theorem (§4), so they show up in the
   compared statement.
6. **Resource limits**: per-kernel `ulimit -v`/cgroup + timeout (nanoda reached 100+ GB on
   ordinary `Std` lemmas; con-* reserve ~1 GB address space per worker → size `--jobs`).
   Resource exhaustion = reject-with-retry-on-bigger-box, never accept.
7. **Human review of definitions**: comparator checks statements syntactically against
   challenge constants, but any `definition_names` hole (candidate-supplied definitions such as
   "the verifier as a Lean function") needs review or must be pinned by an artifact-binding
   theorem (§4.3).
8. Re-run the whole suite on every toolchain bump and on every candidate artifact change.

## 4. What the admission theorem must look like (informed by the survey)

### 4.1 Shape

A deterministic "`∀ π, verify vk x π = true → R x`" is **false** for any succinct argument and
must not be the target. Recommended statement (formal-core, Mathlib-free):

```
structure Candidate where
  Proof : Type; Stmt := NearTransition       -- (pre_state_root, block, post_state_root, outcomes)
  verify : OracleTable → Stmt → Proof → Bool  -- Lean model of the deployed verifier, RO-parameterized
  ...
theorem admission (c : Candidate) :
  ∀ (A : Adversary c q), Pr_{H ← uniform oracle tables}[ let (x, π) := A^H ;
      c.verify H x π ∧ ¬ NearSemantics.valid x ] ≤ c.eps q
```

plus (i) an **artifact-binding** theorem relating `c.verify` to the deployed verifier
(§4.3), and (ii) a numeric bound `c.eps q_max ≤ 2^-λ` checked by `decide` on `Rat`/`Nat`
(no `native_decide`).

* Templates: VCVio `FiatShamir.euf_cma_to_nma` / `signHashQueryBound` (query-bounded ROM
  statement) and `MerkleTreeExtractability.extractability_rom_bound`. ArkLib's
  `Verifier.soundness` with `NonInteractiveVerifier` + random-oracle `oSpec` can express this,
  but nothing in ArkLib proves it for any IOP; its FS soundness is a TODO and `fiatShamir_completeness`
  is `sorry` (see ecosystem §3.5).
* The transparent (re-execution) backend instantiates `Proof := witness`, `verify :=
  NearSemantics.apply` and needs no oracle: ε = 0 (only hash collision-resistance if state
  roots are compared via hashes — model the hash as an RO or carry collision-resistance as an
  explicit hypothesis).

### 4.2 What is reusable today

| Piece | Source | Status |
|---|---|---|
| ROM, lazy sampling, query bounds, forking lemma | VCVio | sorry-free; requires Mathlib |
| FS for multi-round public-coin IOPs (RBR ⇒ NARG soundness) | – | **must be built** (ArkLib has defs only) |
| BCS (IOP + Merkle ⇒ argument) | VCVio Merkle ROM extractability | partial; transform absent |
| FRI / STIR / WHIR soundness | ArkLib | sorry / absent; only Johnson bound, BCIKS20 UDR, DG25 proven |
| Sumcheck soundness | ArkLib new `Interaction` framework | proven |
| AIR / constraint ⇒ spec (chip level) | openvm-fv, sp1-lean, Clean, CertiPlonk | per-chip; whole-trace composition and lookup/bus soundness assumed |
| Rust verifier ↔ Lean | Aeneas (+hax) | tooling exists; no real STARK verifier bound yet |

### 4.3 Artifact binding options (ranked)

1. **Lean is the verifier** (OpenVM pattern): the deployed verifier is compiled from the Lean
   model (Lean → C via `leanc`, vendored; CI regenerates and byte-compares). Remaining trust:
   Lean compiler/runtime, wire decoders. Most robust; needs the verifier to be written in Lean.
2. **Aeneas extraction of the Rust verifier**: Charon + Aeneas at pinned commits, arena re-runs
   extraction and byte-diffs the `.lean`; certificate proves a total-correctness triple
   `verify_rs x π ⦃ b => b = true → c.verify H x π = true ⦄` (and no-panic). Must handle the
   overflow-as-failure vs release-wrap gap (require `overflow-checks = true` in the deployed
   profile or prove the model never fails) and declare `FunsExternal` axioms (hash, etc.) as
   explicit hypotheses rather than axioms. Trust: rustc MIR (nightly), Charon, Aeneas OCaml,
   std models.
3. **Differential testing only** (Kani bounded harnesses + Lean `#eval` vs Rust on corpora):
   not a certificate; acceptable only as Milestone-C "open obligation" evidence.

## 5. Backend families realistically submittable on CPU-only hardware (Milestone C)

Measured on this host (32 threads, 125 GB, no GPU). Installed into `$HOME` only:
SP1 **6.8.1** (`bash sp1/sp1up/install && ~/.sp1/bin/sp1up`, 27 s, 1.7 GB; build also needed
`protoc` 29.3 in `~/.local/protoc`), RISC Zero **3.0.6** (`bash risc0/rzup/install &&
~/.risc0/bin/rzup install`, 42 s, 3.2 GB — note the cloned `main` is 5.0.0, newer than the stable
release rzup installs), Plonky3 `3acc8b70` (plain cargo). Trial sources/logs:
`/data/illia/nearproof-deps/trials/{sp1bench,r0bench,wasmmod,wasmhost}`, Plonky3 hash-chain AIR in
the scratchpad `hashchain/`. Some large runs overlapped other jobs on the box ("contended").
Groth16/PLONK wrapping was **not** run (SP1 needs gnark docker or Go+`native-gnark` + S3 circuit
download; RISC Zero needs x86+docker or CUDA; root disk 94% full).

### 5.1 Measurements

Cycle counts (same guest source on both zkVMs; "accel" = precompile/patched crate):

| Workload | SP1 cycles | RISC Zero cycles (padded) |
|---|---|---|
| SHA-256 of 1 MB, accel | 3.7 M | 1.24 M (2.36 M) |
| SHA-256 of 1 MB, software | 69.0 M | 78.2 M (82.3 M) |
| 100 × ed25519 verify, accel | 9.0 M (~90 k each) | 89.2 M (~890 k each) |
| wasmi 2.0 interpreter running 7.08 M Wasm instrs (SHA-256 of 64 KB in Wasm) | 205 M (~29 cyc/instr) | 178 M (~25 cyc/instr; needed `portable-dispatch`) |

Interpreting Wasm costs ~36–48× more cycles than native guest code for the same computation.

| Proof run | Prove (wall) | Peak RSS | Proof size | Verify |
|---|---|---|---|---|
| SP1 core, SHA 1 MB accel | 68 s | 39 GB | 4.4 MB | 111 ms |
| SP1 compressed, same | 91 s | 43 GB | 1.27 MB | 29 ms |
| SP1 core, 69 M cycles | 305 s (~226 k cyc/s) | 99 GB | 16.7 MB | 418 ms |
| SP1 core, Wasm 205 M cycles, 2 workers, contended | 2357 s (~87 k cyc/s) | 80 GB | 86 MB | 2.0 s |
| RISC Zero composite, SHA 1 MB accel (3 segments) | 95 s | 9.6 GB | 819 KB | 38 ms |
| RISC Zero succinct, same | 120 s | 9.6 GB | 223 KB | 12 ms |
| RISC Zero composite, 21 M cycles (20 segments) | 1016 s (~20.6 k cyc/s) | 9.6 GB | 5.6 MB | 412 ms |
| Plonky3 uni-stark, Poseidon2 AIR 2^20 rows (8.4 M perms), KoalaBear, native CPU flags | 6.7 s | 11.3 GB | 710 KB | 12 ms |
| Plonky3 custom Poseidon2 hash-chain AIR, 2^18 steps | 0.67 s (+0.48 s tracegen) | – | – | 8.5 ms |
| Transparent re-execution (nearcore `validate_chunk_state_witness`) | no proving | native | witness ≤ 64 MiB (storage proof soft limit 4 MB) | = one native re-execution (not measured; ms–s per chunk) |

What a verifier must pin: SP1 — program vkey hash (bench:
`0x00182e0346fe306674ac7761a94e2292f986153cac8ca58959ff653a3f9a2114`), SP1 circuit version
string (`v6.1.0`), recursion vk root built into `sp1-verifier`, plus Groth16/PLONK vk files if
wrapped. RISC Zero — image ID (bench: `42ba4b22d2218c2243e74793085d84f4eb1d7dd310d701523443cf3406f898f8`),
`ALLOWED_CONTROL_ROOT = a54dc85a…1f56`, circuit version (`risc0-circuit-rv32im` 4.0.5), Groth16
control ID + BN254 vk if wrapped. Plonky3 — the AIR itself is fixed by the verifier binary (the
transcript binds shape, not constraints), so pin the verifier code hash + FRI parameters.

Verifier code size to model/bind: SP1 compressed path ~10–15 k LOC Rust (`sp1-verifier` 2.2 k,
hypercube verifier+GKR 3.3 k, jagged PCS 2.6 k, multilinear 1.6 k, recursion constraints 3.5 k);
RISC Zero ~4 k LOC hand-written verifier + ~9.4 MB (rv32im) / 0.9 MB (recursion) of generated
constraint code; Plonky3 uni-stark+FRI+MMCS+challenger: a few k LOC, and the AIR is ours.

### 5.2 NEAR chunk extrapolation (order of magnitude)

Chunk gas limit 1000 Tgas / Wasm regular-op cost 822,756 gas ⇒ ≤ ~1.2e9 Wasm instructions; a busy
real chunk maybe 1e7–2e8. At 25–30 cycles/Wasm instr plus storage-proof hashing (accelerated: a few
M cycles), ed25519 (~90 k cycles/tx SP1, ~890 k RISC Zero), and runtime logic (guess 1e8–1e9
cycles): **~1e9–4e10 cycles per chunk**. On this box: SP1 ≈ 1.4 h per 1e9 cycles (a light ~1e8
chunk ≈ 10 min at 80–100 GB RSS — near the RAM ceiling); RISC Zero ≈ 14 h per 1e9 cycles, and its
32-bit address space (~3 GB guest) may not fit the NEAR runtime. Both are **offline per-chunk**
proving, 3–5 orders of magnitude from real time on this hardware.

### 5.3 Backend families for Milestone C ("materially different")

| Family | Install effort here | Realistic on CPU? | Formal obligations still open (beyond NEAR-semantics model, which all share) |
|---|---|---|---|
| **T. Transparent re-execution** (witness = proof; verifier = deterministic re-execution against pre-state root) | none beyond nearcore (or a Lean-native re-executor) | yes, native speed | Verifier ↔ NEAR-semantics refinement (the hard part: runtime, Wasm, gas, trie); SHA-256 collision resistance as an explicit hypothesis; **no FS/IOP soundness needed (ε from hashing only)**. Best fit for "Lean is the verifier" binding: the Lean semantics *is* the checker, compiled. |
| **P. Custom Plonky3 STARK** (hand-written AIR for a restricted statement, e.g. state-root/hash-chain/receipt-Merkle transitions, or a small NEAR-specific VM) | low (cargo; ~1–2 min builds) | yes, very fast (seconds for 2^18–2^20 rows) | AIR ⇒ spec faithfulness (CertiPlonk/Clean-style, but we write it; needs bus/lookup soundness if multi-table); STARK/DEEP-ALI + FRI + MMCS + duplex-sponge FS soundness in ROM (**nothing proven publicly — ArkLib FRI is sorry**); concrete ε (use proven-regime params: blowup ≥ 8, ~120 queries, 16–20-bit PoW; Plonky3's own calculator rates default examples at only 50–57 proven bits); Rust verifier binding (Aeneas). Expressiveness: cannot run Wasm without building a zkVM. |
| **Z1. SP1 zkVM** (nearcore runtime/Wasm interpreter as RISC-V guest) | low (27 s install + protoc + 2 min build) | only for light chunks / offline; RAM-bound (40–100 GB) | Guest faithfulness (wasmi/nearcore compiled to RV64 vs our Wasm/NEAR semantics); RV64IM circuit faithfulness (sp1-lean partial: 25 chips, machine theorem depends on `sorry`, precompiles out of scope, extraction not reproducible from main); precompiles (SHA-256, ed25519) unverified; Jagged PCS + LogUp-GKR + FS soundness (conjectured 100 bits, unformalized); recursion circuit + vk root; Groth16/PLONK trusted setup if wrapped; Rust verifier binding (10–15 k LOC). |
| **Z2. RISC Zero zkVM** | low (42 s + 14 min first build; crypto-bigint patch for ed25519) | slower (~20 k cyc/s) but low RAM (~10 GB); 32-bit guest memory limit | Same shape as SP1 but with **no** public Lean chip proofs at all (only proprietary Picus determinism runs), ~10 MB generated constraint code, FRI under ethSTARK Toy Problem Conjecture (97 bits conjectured), recursion + control root, Groth16 setup. |
| Z3. OpenVM (not tried here) | moderate (`cargo +1.91 install … cargo-openvm`, nightly) | CPU backend exists | Best public chip-level proofs (openvm-fv RV32IM + SHA-2/Keccak, axiom-clean, comparator-gated, pinned to v2.0.0) and a Lean-extracted verifier (theorems private); proof-system soundness assumed (I2). Strongest zkVM candidate *if* openvm-fv's guarantees are re-checked by our pipeline. |
| Z4. Jolt (not tried) | low | CPU default | Alpha/unaudited; extraction but no Lean theorems. Not recommended for Milestone C. |

**Recommendation for Milestone C on this hardware:** submit **T (transparent re-execution)** as
the reference backend and **P (custom Plonky3 STARK over a deliberately narrow statement)** as
the "materially different" cryptographic backend. They differ in every relevant axis
(no-crypto vs FS-STARK; witness-size vs succinct proof), both run comfortably on 32 cores, and
both keep the open obligations *enumerable*: for P the open items are exactly {AIR faithfulness
(provable by us), STARK/FRI/FS soundness in ROM (open research; carried as an explicit named
hypothesis in the admission statement, never as an axiom), Rust-verifier binding (Aeneas)}. A
zkVM backend (SP1 for speed, or OpenVM for the best existing chip proofs) is installable today
and is a credible *third* entry, but its open-obligation list (guest Wasm interpreter + nearcore
on RISC-V + ISA circuits + precompiles + recursion + wrapper) is far larger, and full NEAR chunks
are hours-to-days per chunk on this CPU at 40–100 GB RAM.

## 6. Summary of decisions

1. Toolchain: **Lean v4.35.0** (rc3 now). One pin for formal-core, challenges, checkers.
2. Mathlib: **not in formal-core statements**; allowed (pinned rev) in candidate proofs.
3. Checker: `lake comparator --paranoid` on arena-owned Challenge + per-theorem exports, built in a
   sandbox/VM; independent kernels outside (leanchecker `--from-export`, nanoda hard-error
   policy, con-ron/lean4lean); whitelist `{propext, Quot.sound, Classical.choice}`; any non-zero
   exit or resource exhaustion = reject; never trust in-environment `#print axioms`.
4. Admission theorem: query-bounded ROM soundness bound (VCVio-style) + artifact-binding theorem
   + decidable numeric ε check; crypto assumptions as hypotheses, not axioms.
5. Backends for Milestone C: transparent re-execution + narrow custom Plonky3 STARK; zkVM
   (SP1/OpenVM) optional third.
6. Reuse priorities: VCVio (ROM/FS machinery), openvm-fv (chip-proof + CI-gate pattern), Clean
   (DSL vocabulary), Aeneas (Rust binding), ArkLib (definitions; Sumcheck; proximity-gap lemmas)
   — and treat every other "verified" claim as unverified until it passes our pipeline.
