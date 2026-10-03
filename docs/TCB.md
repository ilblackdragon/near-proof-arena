# Trusted computing base

Everything listed here must be correct (or honest) for an `ADMITTED` result
under a `formal` challenge to mean what `docs/THREAT_MODEL.md` §1 says. Each
component is pinned by version and digest **inside the challenge definition
or the deployment manifest**; `TBD` marks values that do not exist yet.
Reports render these as `tcb_component` nodes in the evidence graph with
edge status `trusted`.

Legend for *status*: **pinned** (value exists and is enforced),
**planned** (design fixed, value TBD), **aspirational** (not designed in
detail / not built).

## 1. Trusted components

| # | component | what we trust it for | pin (version / digest) | where pinned | status |
|---|-----------|---------------------|------------------------|--------------|--------|
| 1 | **Lean 4 kernel** (type checker) | Accepting only well-typed terms; the certificate's type equals the arena-constructed admission theorem | `leanprover/lean4:v4.34.1` (all `lean-toolchain` files); checker image digest pinned per challenge (e.g. `sha256:2de5b684…` in `chl_5ef2bc7d…`) | `toolchain_policy.lean_toolchain`, `toolchain_policy.checker_image` | pinned (toolchain) / planned (reproducible image) |
| 2 | **Independent recheckers** (e.g. `lean4checker`, `nanoda`, `lean4lean`) | Re-validating the exported environment without the elaborator; at least one must be independent of the Lean C++ kernel | names in `toolchain_policy.recheckers` (`leanchecker`, `nanoda`, `lean4lean`); commits in `runners/formal-checker/tools.toml` | challenge + checker image | implemented (Stage B, `runners/formal-checker/src/pipeline.rs`); `lean4lean` optional at runtime |
| 3 | **Environment export** (`lean4export` or equivalent) | Faithfully serialising declarations for the recheckers | `lean4export` commit `076e8e57…` (`runners/formal-checker/tools.toml`) | checker image | pinned (commit) |
| 4 | **formal-core** (admission theorem type, game definitions, adversary/cost model, assumption hypotheses) | That the theorem the judge demands really expresses soundness/completeness/ZK with concrete bounds | tree digest `TBD` (part of `formal_spec.tree_digest`) | challenge | planned |
| 5 | **NEAR spec definitions** (`spec/lean`, `NearRelation`, claim encoding) | That they describe nearcore's behaviour on the challenge scope | `formal_spec.tree_digest`, `spec_doc_digest`, `claim_encoding.spec_digest` | challenge | planned (spec lane) |
| 6 | **Assumption set** (`security/assumptions/*.json` + their Lean declarations) | That SHA-256 collision resistance holds at the stated concrete bound; that the ROM is an acceptable heuristic for Fiat–Shamir at the stated query budget | file digests (git) + `lean_decl_digest` (both set in `security/assumptions/*.json`) | `security/`, embedded profile in challenge | pinned. Note: the Lean definitions take arbitrary `num/den`; the birthday / q_H bound stated in the JSON is not itself in Lean |
| 7 | **Security profiles** (`security/profiles/*.json`) | Parameters (128 bits, 2^64 hash queries, …) chosen sensibly | embedded verbatim in each challenge, checked by `arena-admin` | challenge | pinned |
| 8 | **Bytecode interpreter** (`runners/npai`: `arena-npai` `interp.rs` + `npai-verify`) for the conservative verifier route, and its formal model `formal-core/ArenaCore/Interp.lean` | That executing the candidate's verifier bytecode means exactly what `ArenaCore.Interp.interpVerify` says. Evidence: differential testing against the compiled Lean definition (vectors + ~1.2M generated cases, 0 disagreements) — **tested, not checked**; see `runners/npai/README.md` | `npai-verify` binary digest `TBD` (worker image) | deployment manifest | planned (implemented, tested) |
| 9 | **Compilers** for the native verifier route: today the Lean compiler (`lean -c`, `leanc`, Lean runtime, C toolchain) for `verify_route = "native-lean"`; rustc/LLVM or a verified compiler / translation validator for any future native route | That the judge-built native `verify` implements the Lean verifier model (`FORMAL_IMPL_CONNECTION` edge recorded as `trusted`) | Lean toolchain v4.34.1 (via `lean_toolchain`); C toolchain in checker image `TBD` | challenge | trusted, in use (native-lean); others aspirational |
| 10 | **Sandbox / hypervisor** (Firecracker + KVM + host kernel; `bwrap-dev` for dev only) | Isolation of untrusted code; no network; resource limits | Firecracker version `TBD`, rootfs digest `TBD`, host kernel `TBD` | deployment manifest | planned (runners-vm) |
| 11 | **Oracle nearcore build** | Computing `expected_claim(request)` and conformance outputs | nearcore repo + tag + **full commit** (e.g. `2.13.4` = `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`), oracle binary digest `TBD`, `runtime_config_digest` | challenge (`nearcore`, `runtime_config_digest`) + oracle image | pinned (commit) / planned (binary) |
| 12 | **Workload generators and held-out set** | Representative, unpredictable inputs | `classes[].generator`, `public_fixtures`, `heldout_commitment` | challenge | planned |
| 13 | **Measurement harness** (supervisor timing, hardware profile) | Honest timings; correct median/MAD/score arithmetic | harness binary digest `TBD`; `hardware_profile` | challenge + deployment manifest | planned (bench lane) |
| 14 | **Control plane** (server, decision engine `arena_types::decide`, DB) | Running every mandatory gate, recording results faithfully, computing decisions | server build digest `TBD`; `arena-types` `SCHEMA_VERSION = arena-contracts-v1` | deployment manifest | planned |
| 15 | **Workers** | Executing gates honestly and reporting results | worker image digest `TBD` | deployment manifest | planned (see THREAT_MODEL §4.11) |
| 16 | **Governance signing keys** | Only authorised challenges load | prod key: `TBD` (offline/HSM). Dev key `gov_8292e8f55c257fcc` (**dev-only, untrusted for production**) | `challenges/*.pub` | dev pinned, prod TBD |
| 17 | **Governance tooling** (`tools/arena-admin`, `tools/upgrade-monitor`) | Correct policy checks; correct closure computation | git commit of this repo | repo | pinned (by commit) |
| 18 | **JCS canonicalisation + SHA-256 + ed25519** implementations (`arena-types::canonical`, `sha2`, `ed25519-dalek` `verify_strict`) | Content addressing and signatures | `Cargo.lock` | repo | pinned |
| 19 | **Cargo/Lean dependency trees** of the above | Not being malicious | `Cargo.lock`, Lake manifest | repo | pinned (not audited) |

## 2. What is NOT trusted

* **Anything in a candidate package**: source, build recipe, Lean project
  (including tactics, macros, `#eval`, environment extensions), binaries,
  stdout/stderr, self-reported timings, `security_profile_request`,
  `backend_family`, README. Only *checked* statements about exact built
  artifacts are used.
* **The Lean elaborator / front end**: only the kernel and recheckers on the
  exported environment count.
* **Candidate-supplied keys/parameters/SRS**: `prepare` is run by the judge.
* **The manifest's security claims**: the bound is recomputed by the kernel
  at the challenge's parameters.
* **Agent identity strings** in manifests: the server uses the authenticated
  principal.
* **Previous results across challenges**: a result under one challenge id
  says nothing about another.
* **The `bwrap-dev` sandbox**: results through it are capped at `demo` tier.
* **The dev governance key** (`challenges/governance-dev.pub`): it may sign
  only demo/experimental challenges and must not be trusted by production.
* **Old Lean proofs after an upstream change**: "still compiles" is not
  evidence; the upgrade monitor reopens obligations.

## 3. How to reduce the TCB (roadmap)

1. Two independent recheckers, one not sharing code with the Lean C++
   kernel (e.g. `nanoda`/`lean4lean`) — planned.
2. Conservative verifier route via a small, formally specified bytecode
   interpreter, so no compiler is trusted — implemented (`runners/npai`),
   interpreter↔Lean agreement is *tested*; making it *checked* needs an
   extraction + equivalence proof or a proved-equivalent fast Lean
   interpreter (see `runners/npai/README.md`).
3. Per-worker signed gate results and random independent re-execution —
   aspirational.
4. M-of-N governance signatures (threshold or multi-sig) — aspirational;
   v1 is a single ed25519 key.
5. Reproducible checker/oracle images with published SBOMs — aspirational.
