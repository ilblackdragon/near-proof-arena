# zkvm-sp1 — evidence matrix

Statuses follow `docs/CONTRACTS.md` §8: **checked** (machine-checked proof or
judge-checked artifact property), **trusted** (named component in the TCB),
**tested** (differential or adversarial testing only), **missing** (no
evidence). A missing edge is listed, not hidden.

Bottom line: this backend has strong **tested** evidence and a working
succinct proof pipeline. It has **no** discharged formal obligation that
says anything about SP1. It must be ranked **EXPERIMENTAL**. Under the strict
(formal-tier) profile the judge must reject it:

* `formal/` defines no `Candidate.certificate`, so the judge reports
  `CERTIFICATE_MISSING` / `OBLIGATION_UNDISCHARGED`. We did not fake one with
  `sorry` or an axiom.
* `FORMAL_CRYPTO_SOUNDNESS` also cannot be stated with the approved
  assumptions. SP1's Fiat–Shamir transcript and its Merkle commitments use
  Poseidon2 over KoalaBear, while the profile allows only `sha256_cr` and
  `sha256_rom`. That alone gives `UNAPPROVED_ASSUMPTION`.
* SP1 v6.8.1's own parameters target **100 bits**
  (`SP1_TARGET_BITS_OF_SECURITY`, conjectured/unique-decoding query count).
  The profile requires 128, which gives `SECURITY_BOUND_INSUFFICIENT` even if
  everything else were proved.

## Statement chain

`verify(pub, claim.bin, proof.bin) = accept` should imply that `claim.bin`
is in the language of `NearSpec.TransferV1.NearRelation`. The chain below is
formalised abstractly, with every link as a hypothesis, in
`formal/Candidate/Pipeline.lean` (`sound_or_forged`, kernel-checked, axioms ⊆
{propext, Classical.choice, Quot.sound}).

| # | link | status | evidence / reference |
|---|------|--------|----------------------|
| 1 | **IMPL**: `out/verify` (native Rust: our framing + `sp1-verifier` 6.8.1 `SP1CompressedVerifier`) computes the modelled verifier | **missing** (best case: *trusted* via `.nativeTrusted`) | No Lean model of SP1's verifier exists. Aeneas/hax could extract the Rust verifier (~10k+ LOC incl. `sp1-hypercube`, `slop-*`); nobody has done it. OpenVM's "certified verifier" (Lean→C) is the only comparable effort, and its theorems are private (`docs/research/formal-ecosystem.md` §3.8). |
| 2a | **STARK/PCS soundness** of each shard proof (KoalaBear, deg-4 ext., Jagged PCS / BaseFold-style multilinear PCS, LogUp-GKR, sumcheck, 124 queries at blowup 4, 16-bit PoW) | **missing** | ArkLib: FRI/STIR relations and soundness admitted, sumcheck soundness proved in its new framework, BCIKS20 unique-decoding regime proved (formal-ecosystem §3.5). Nothing covers SP1's protocol. SP1's own security argument is a paper argument with a 100-bit target. |
| 2b | **Fiat–Shamir** (non-interactive soundness in the ROM) | **missing** | ArkLib FS soundness is not even stated, and VCVio covers FS only for Σ-protocols (§3.5–3.6). Also needs a Poseidon2-as-RO assumption, which is not approved. |
| 2c | **Recursion / compression**: the compressed proof attests that every core shard proof verifies, recursion vk ∈ pinned vk Merkle root, `is_complete = 1`, `sp1_vk_digest = vkey`, committed-values digest chained | **missing** | Recursion circuits are not formalised anywhere. sp1-lean puts "recursion/compress/shrink/wrap" explicitly out of scope (§3.1). |
| 2d | public-values binding: committed digest = SHA-256(claim.bin) **or BLAKE3(claim.bin)** (SP1 accepts either) | **trusted** | Needs SHA-256 *and* BLAKE3 collision resistance, plus the absence of a cross-hash collision. BLAKE3 is not an approved assumption. |
| 3 | **VKEY**: the vkey in `public.bin` is SP1 `setup` of the pinned guest ELF | **tested** + judge-controlled | `prepare` is judge-run. It derives the vkey from the ELF embedded in the judge-built `prepare`. `verify`, `prove` and `prepare` all pin the ELF's SHA-256 at compile time (`zk-artifacts` build.rs), and `public.bin` must name that digest. `prove` re-derives the vkey and refuses on mismatch. Not proved: that SP1 `setup` is a function of the ELF only (determinism observed across runs). |
| 4 | **CONSTRAINTS**: a satisfying SP1 RV64IM execution record for vkey(elf) with public values `pv` implies the ELF halts with exit 0 having committed `pv` | **missing** | sp1-lean (`512e944`): per-chip soundness for 25 RV64IM chips against Sail. Its machine theorem `sp1_machine_soundness` depends on an admitted step (`sp1_witness_decode`) and on `Lean.ofReduceBool`, and its spec constrains only clk/pc. **Out of scope there:** the SHA-256 precompiles (which this guest relies on for every hash), syscalls (`read_vec`, `commit`, `halt`), memory init/finalize, global chip, the bus/LogUp argument (assumed as an axiom). Its extraction targets SP1 ≈ v6.2.2 on a branch, not the v6.8.1 we run. |
| 5 | **COMPILER**: the ELF implements `transfer-core::derive_claim` (succinct rustc 1.96.0-dev, `sp1-zkvm` 6.8.1 entrypoint/ABI, patched `sha2` = SP1 SHA-256 precompile) | **tested** | The guest's committed public values equal the native `derive_claim` output (and the oracle's claim) on every case executed or proved (`zkexec`, bench). No verified compiler, no Lean semantics of the Rust guest. The guest ELF is reproducible from source (two builds at different paths give the same SHA-256, pinned in `dependency-locks/guest-elf.sha256`). |
| 6 | **GUEST**: `derive_claim(req, wit) = cb` implies `cb ∈ InLang(NearRelation)` | **tested** | Written only from `spec/claim-v1.md` and `spec/near-transfer-receipt-v1.md`. **Byte-identical claims** to the nearcore-backed oracle on all 20 public fixtures and on 1500 generated in-domain cases (seed 4242, plus 40 large cases with seed 777). **All 210 generated out-of-domain cases and all 14 rejection fixtures are refused**, each with the same reason family as the oracle. Not proved in Lean. A route exists: model `derive_claim` in Lean (or extract it with Aeneas) and prove refinement to `NearSpec.TransferV1.runBatch` plus the `PTrie` hashing. This is the most tractable missing link. |
| 7 | SHA-256 collision resistance (trie / commitment binding to the real chain state) | **trusted** (approved: `sha256_cr`) | Same as for every backend. |

## Obligation rows (arena gate ids)

| ObligationId | status | why |
|---|---|---|
| `PKG_WELLFORMED` | tested | Manifest uses only `arena-candidate-v1` fields. The archive must include the vendored dirs (`build-recipe/vendor.sh`): 28k files, about 61 MB with zstd -19, 770 MB expanded. |
| `BUILD_REPRODUCIBLE` | tested (locally) | Two offline builds in fresh `$HOME`s at **different paths**, with no network (`unshare -n`), give bit-identical `out/{prepare,prove,verify}`. The guest is rebuilt from source and checked against its pin. **Caveat:** this needs the `succinct` toolchain in the build image. Without it the build falls back to the shipped pinned ELF and prints `GUEST-NOT-REBUILT`, so the gate then does not cover the guest. |
| `ARTIFACT_BINDING` | missing | There is no certificate to bind digests to. The artifacts bind each other (ELF digest compiled into all three binaries; vkey in judge-produced `public.bin`). |
| `FORMAL_SEMANTIC_SOUNDNESS` | checked, but vacuous | `Candidate.backend_semSound` with `B := Rel`. Every zkVM-specific step moves into rows 1–6. |
| `FORMAL_SEMANTIC_COMPLETENESS` | checked, but vacuous | `Candidate.backend_semComplete`, same caveat. |
| `FORMAL_CRYPTO_SOUNDNESS` | **missing** | Rows 2a–2d. Also blocked by unapproved assumptions (Poseidon2 RO, BLAKE3) and by SP1's 100-bit target being below 128. |
| `FORMAL_IMPL_CONNECTION` | **missing** | Row 1. |
| `FORMAL_ZK` | not applicable | validity-only profile. SP1 compressed proofs are not claimed to be ZK. |
| `AXIOM_AUDIT` | checked (for what exists) | `#print axioms` of every theorem in `formal/` ⊆ {propext, Classical.choice, Quot.sound}. No holes, no `native_decide`. |
| `CONFORMANCE_DIFFERENTIAL` | tested | See row 6. Inside the zkVM, the guest's public values equal the oracle claim on every executed or proved case. |
| `ADVERSARIAL_PROOFS` | tested (locally) | `bench/adversarial.py`: 715 hostile inputs, all rejected with exit 1. They cover proof bit flips (structured and random), truncation and extension, garbage, every claim byte flipped, claim/proof cross-swaps and a tampered vkey. Tampered `public.bin` params/ELF digest gives exit 2, never accept. Verify was deterministic across repeats. Hostile decoding is bounded: 8 MiB cap, bincode size limit, trailing bytes rejected, panics caught and turned into reject. |
| `PROVER_RELIABILITY` | tested | Every proved case verified (see README numbers). Out-of-domain inputs are refused before proving (exit 3). |
| `RESOURCE_LIMITS` | **fails the reexec dev challenge limits** | Peak RSS is about 16 GB per proof against a 4 GiB cap. Wall time is about 90–110 s per proof against a 60 s `max_prove_ms`. Proof size (1.27 MB) and verify time (≈30–50 ms) are well within limits. |
| `BENCHMARK` | local only | README §Measurements. These are not judge measurements, and the host load average was 40–65 on 32 cores during the runs. |

## TCB of an *accept* today

* The SP1 v6.8.1 proof system: protocol soundness at its 100-bit target, the
  recursion circuits, the AIR constraints including the SHA-256 precompile
  chips, and the `sp1-verifier` implementation.
* The `succinct` rustc toolchain and the `sp1-zkvm` runtime.
* Our guest (`transfer-core`), which is tested but not proved.
* Poseidon2 (as a random oracle / ideal permutation), BLAKE3 and SHA-256.
* The judge-run `prepare` (vkey derivation) and the host Rust toolchain.

## Upstream formal work and its scope (2026-10-03 snapshot)

| project | what it proves | relevance here |
|---|---|---|
| sp1-lean (`512e944`, Lean v4.28) | Per-chip RV64IM soundness and completeness against Sail. The capstone machine theorem has one admitted step and `ofReduceBool`. | Row 4, partially. Precompiles, syscalls, memory and the proof system are out of scope. Extraction pinned to a v6.2.x branch. |
| openvm-fv | 45 RV32IM opcodes and SHA-256/Keccak chips, axiom-clean, CI-gated | A different zkVM. Shows that row 4 for SHA chips is doable. |
| RISC Zero + Picus / zirgen | Determinism / under-constraint checks for some circuit blocks via a proprietary SMT service | A different zkVM. Gives no Lean artifact. |
| ArkLib / VCVio | IOP / ROM definitions, sumcheck soundness, FS for Σ-protocols, Merkle extractability | Rows 2a–2b foundations only. |
| Aeneas / hax | Rust → Lean extraction | The plausible route for rows 1, 5 and 6. Not attempted. |
