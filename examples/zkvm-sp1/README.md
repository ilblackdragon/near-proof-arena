# zkvm-sp1: succinct-proof backend (SP1 zkVM), EXPERIMENTAL

This candidate targets the same registered statement as the reference
candidate, `near/pv86/receipt-transfer-batch/v0` (`spec/claim-v1.md`,
`spec/near-transfer-receipt-v1.md`). It belongs to a different backend family:
a **succinct cryptographic proof**. The proof does not contain the witness,
and the verifier does not re-execute NEAR semantics. It checks a constant-size
(~1.27 MB) recursively compressed STARK proof from the
[SP1](https://github.com/succinctlabs/sp1) v6.8.1 RISC-V zkVM. The proof
attests that the pinned guest program ran on *some* (request, witness) and
committed exactly `claim.bin`.

**Tier expectation: EXPERIMENTAL.** None of the strict formal obligations
about SP1 are discharged, and `formal/` deliberately defines no
`Candidate.certificate`. The judge must not admit this candidate under the
formal profile. See [`EVIDENCE.md`](EVIDENCE.md).

## Why SP1

We needed a CPU-capable succinct system that works end to end and offline.
Trials on this host (32 cores, 125 GB, no GPU):

* **SP1 v6.8.1** (chosen). Proving runs fully offline: compressed proofs need
  no downloaded circuit artifacts; only Groth16/PLONK wrapping would. The
  toolchain is ~1.7 GB under `~/.sp1`. The verifier is a separate small crate
  (`sp1-verifier`, `compressed` module), giving a 1.5 MB standalone `verify`
  binary that runs in ~30–110 ms with 5 MB RSS. SHA-256 is a precompile
  (patched `sha2`).
* **RISC Zero 3.0.6**: installed fine, but the trial guest failed to build
  (precompile-patched `curve25519-dalek` vs `crypto-bigint` mismatch) after
  14 min. Dropped for time.
* **Hand-rolled Plonky3 AIR**: the fastest prover and the smallest TCB in
  principle. It would mean writing AIRs for SHA-256, trie walking and u128
  arithmetic, which is weeks of work.

We did **not** use SP1's Groth16/PLONK wrap. It needs a BN254 trusted setup,
which the `transparent` setup model forbids, plus gnark/Go artifacts.
Compressed STARK proofs are transparent.

## Pipeline

```
request.bin, witness.bin ──► prove ──► native pre-check (transfer-core)  → refuse out-of-domain (exit 3)
                                   └─► SP1 CPU prover: execute guest ELF, prove shards (core),
                                       recursively compress → SP1RecursionProof
                              claim.bin = guest public values (exactly the canonical claim bytes)
                              proof.bin = "nearproof-sp1-compressed-v1" ‖ bincode(SP1RecursionProof)

params.bin ──► prepare (judge-run) ──► public_dir/public.bin =
               statement id ‖ sha256(params) ‖ sha256(guest ELF) ‖ SP1 program vkey hash ‖ circuit version

verify(public.bin, claim.bin, proof.bin):
  public.bin well formed, right params, ELF digest == digest compiled into verify   (else exit 2)
  claim.bin structurally well formed                                               (else exit 1)
  SP1CompressedVerifier: shard proof ok, recursion vk ∈ pinned vk Merkle root,
    is_complete = 1, program vkey == public.bin vkey,
    committed public-values digest == SHA-256(claim.bin) [or BLAKE3, SP1 accepts both]
  guest exit code == 0                                                             (else exit 1)
```

* **Guest** (`source/guest`, `source/core`): `transfer-core::derive_claim` is a
  `no_std` re-implementation of the relation, written from the spec documents
  only. It decodes `request.bin`/`witness.bin` strictly. It resolves every
  receiver's `Account` value by walking trie nodes looked up **by SHA-256
  from `pre_state_root`**, and checks the full domain (spec §3). It then
  applies transfers, refunds and burns, recomputes the post root by in-place
  value replacement along the revealed paths (spec §4), builds outcome
  leaves and merklizes them, and encodes the claim. The same crate runs
  natively in `prove` as a fail-fast check.
* **Keys**: SP1 `setup` derives the program vkey deterministically from the
  ELF. `prepare` is run by the judge, from the judge-built binary that embeds
  the ELF, so no candidate-chosen key exists. All three binaries pin the
  ELF's SHA-256 at compile time (`source/artifacts/build.rs`).
* **Proof contents**: the proof carries no witness bytes. The claim is not
  inside `proof.bin`: `verify` hashes `claim.bin` itself and compares the
  result with the digest committed in the proof.

## Layout

| path | what |
|---|---|
| `source/core/` | `transfer-core`: relation check (guest + host), fixture tests, `examples/check.rs` differential driver |
| `source/guest/` | SP1 guest crate (separate workspace, `riscv64im-succinct-zkvm-elf`) |
| `source/guest-elf/transfer-guest.elf` | pinned guest ELF (sha256 in `dependency-locks/guest-elf.sha256`); rebuilt and compared by `build.sh` |
| `source/artifacts/` | `public.bin` / `proof.bin` formats, ELF digest pin |
| `source/prover/` | `prepare`, `prove`, `zkexec` (dev: cycle counts) |
| `source/verifier/` | `verify` (depends on `sp1-verifier` only, no prover code) |
| `source/patches/` | two minimal crate patches for offline, reproducible builds (see their `README.nearproof`) |
| `source/vendor*/` | vendored crates, **not in git**: create with `build-recipe/vendor.sh` before packing |
| `formal/` | Lean project: partial certificate structure (no certificate), see EVIDENCE.md |
| `bench/` | `run-bench.sh` (local measurements), `adversarial.py` (local hostile-input test), results |

## Build

`build-recipe/vendor.sh` is the packager step and needs network. It vendors
both workspaces and stubs Windows/wasm-only crates.
`build-recipe/build.sh` is the judge step and runs offline with a fresh
`$HOME`:

1. If the SP1 `succinct` toolchain is present (`$SP1_RUSTC` or
   `rustup run succinct`), it rebuilds the guest with sp1-build's flags plus
   path remapping and stripped symbols, and requires SHA-256 equality with the
   pin. Otherwise it uses the shipped ELF and prints `GUEST-NOT-REBUILT`.
2. It builds the host binaries with `--locked --offline`, path remapping and
   stripped symbols.

Local result: two builds at **different paths**, in fresh `$HOME`s, under
`unshare -n`, produce bit-identical `out/{prepare,prove,verify}` (and guest
ELF). One build takes about 6.5 min of wall time on the loaded host.

Patches (both are build-script-only changes):

* `sp1-prover-types`: the upstream build script needs `protoc` and embeds
  wall-clock time. The patch replaces them with the pre-generated tonic/prost
  output.
* `sp1-core-executor-runner`: the upstream build script builds its embedded
  helper binary as a standalone package with the published crates.io lock,
  which fails offline. The patch builds it from our locked workspace instead.

## Measurements (local, NOT judge-measured)

Host: 32 cores, 125 GB, no GPU. **The host was shared**: load average was
40–70 throughout, so absolute times are pessimistic and noisy. Binaries are
the reproducible `out/` build. Prove = full `prove` process (client init +
setup ≈ 18–28 s, then execute, core proving and compression). Verify = median
of 5 runs of the `verify` process.

| case | receipts | witness B | RISC-V cycles | prove s | prove peak RSS | proof B | verify ms | verify RSS |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| example-tierA | 2 | 534 | 107,560 | 110.8 | 15.9 GB | 1,272,573 | 30 | 5 MB |
| example-tierB | 2 | 534 | 120,153 | 90.5 | 15.9 GB | 1,272,573 | 50 | 5 MB |
| s20261003-v4 | 3 | 628 | 141,866 | 99.4 | 15.9 GB | 1,272,573 | 30 | 5 MB |
| s20261003-v0 | 11 | 1,909 | 481,638 | 110.8 | 16.3 GB | 1,272,573 | 50 | 5 MB |
| s20261003-v3 | 28 | 2,555 | 802,590 | 110.8 | 17.2 GB | 1,272,573 | 110 | 5 MB |
| s777-v12 (gen.) | 68 | 11,344 | 2,985,303 | 143.1 | 22.5 GB | 1,272,573 | 100 | 5 MB |
| s20261003-v17 | 117 | 20,754 | 5,245,569 | 218.9 | 32.4 GB | 1,272,573 | 50 | 5 MB |
| s20261003-v11 | 164 | 8,231 | 3,952,379 | 131.8 | 25.7 GB | 1,272,573 | 60 | 5 MB |
| s20261003-v5 | 233 | 16,511 | 6,526,957 | 158.3 | 34.5 GB | 1,272,573 | 30 | 5 MB |
| s777-v19 (gen.) | 256 | 20,936 | 8,084,780 | 186.9 | 37.8 GB | 1,272,573 | 40 | 5 MB |

* Cost is roughly 25–30 k cycles per receipt plus about 100 k fixed. Cycles
  scale with receipts and witness size; SHA-256 runs as a precompile.
* Proving has a large fixed floor: about 90–110 s and 16 GB even for 2
  receipts (prover init and recursion dominate). It grows to about 190 s and
  38 GB at the 256-receipt maximum.
* The proof size is constant at 1,272,573 bytes. Verify cost is constant:
  30–110 ms (noise from host load), 5 MB RSS, 1.5 MB binary.
* `prepare` takes 2.4 s (light prover setup), and `public.bin` is 154 bytes.
* Raw data is in `bench/results-2026-10-03.tsv`; the cycle column comes from
  `zkexec`.
* A later full run of `arena check-local` (all 20 public fixtures, offline,
  under lower host load; packer exclusion patched locally, see below) passed
  PKG_WELLFORMED, BUILD_REPRODUCIBLE (two builds with identical digests in an
  earlier run), CONFORMANCE_DIFFERENTIAL, PROVER_RELIABILITY,
  ADVERSARIAL_PROOFS and RESOURCE_LIMITS (informational). Timings from that
  run: prove **46–50 s** for 2–28 receipts and **58–83 s** for 117–233
  receipts; verify **35–42 ms**; prepare 1.0 s. The table above therefore
  overstates prove time by about 2× because of host contention.

Correctness:

* `transfer-core`, both native and inside the zkVM, gives claims
  byte-identical to the oracle's `expected_claim` on all **20 public
  fixtures**, on **1500** generated in-domain cases (oracle `gen --seed 4242`)
  and on **40** large ones (seed 777).
* All **210** generated out-of-domain cases and all **14** rejection fixtures
  are refused, with the same reason family as the oracle.
* Inside SP1, the committed public values equal the expected claim on every
  executed fixture (20/20) and on every proved case (10/10).

Adversarial (`bench/adversarial.py`, local): 715 hostile `(claim, proof)`
variants are all rejected with exit 1. They cover bit flips across the proof,
truncation and extension, garbage, every claim byte flipped, cross-case swaps
and a flipped vkey. A tampered params/ELF digest in `public.bin` gives exit 2
(never accept). Honest proofs are accepted deterministically.

## Comparison with `examples/reexec-witness` (backend-reexec lane)

Same cases, same host, same load conditions. The reexec numbers come from that
lane's built `out/` binaries.

| | reexec-witness (re-execution, witness in proof) | zkvm-sp1 (succinct STARK) |
|---|---|---|
| proof size | 614 B (2 receipts) → 74.5 KB (256); linear in witness, ≤ 3.09 MB by bound | **constant 1.27 MB** |
| verify | 10–270 ms, grows with batch (Lean verifier, `List UInt8` SHA); 4–8 MB RSS | **30–110 ms constant**, 5 MB RSS |
| prove | **< 10 ms**, 2 MB RSS | 46–83 s (quiet host) / 90–220 s (loaded), 16–38 GB RSS |
| setup / keys | none (`public.bin` = params) | program vkey from judge-run `prepare` (transparent) |
| privacy of witness | witness revealed in the proof | witness not in the proof (validity only, ZK not claimed) |
| formal evidence | **full admission certificate**: `DeterministicSound` (ε = 0, no assumption), completeness, codec round trip, native-lean impl edge *trusted* | semantic layer vacuous; **crypto, constraint, compiler, guest and impl links missing**; SP1 targets 100 bits; FS hash (Poseidon2) not an approved assumption |
| TCB | Lean kernel + Lean compiler/runtime (verify) | SP1 protocol + recursion circuits + AIRs incl. SHA precompile + sp1-verifier + succinct rustc + guest |
| tier | formal-admissible (pending judge native-lean route) | EXPERIMENTAL |

In this slice the witness is small (≤ 3 MB by the domain, at most 75 KB in
practice). So re-execution wins on every axis except proof size beyond about
1.3 MB of witness. That never happens in this domain: the largest measured
reexec proof is 75 KB, against SP1's fixed 1.27 MB. Succinctness pays only
when witnesses grow, for example to full chunks, Wasm execution or many
shards, or when the witness must not be revealed. Even then the evidence gap
is the blocker, not performance.

## Limits against the dev challenge

The reexec lane's dev challenge sets `max_prove_ms` = 60 000 and
`max_ram_bytes` = 4 GiB. **On the CPU prover this candidate fails the RAM limit everywhere** (≥ 16 GB
even for 2 receipts). It meets the time limit only for small batches on a
quiet host: 46–50 s for ≤ 28 receipts, but 58–83 s for 117–233 receipts. Proof size (≤ 8 MiB) and verify time
are fine. Any SP1 configuration change to reduce memory (smaller shards,
fewer prover workers) is untested here. A GPU prover would change the
picture but is not available on this host.

## Known gaps / TODO

* No Lean model of the guest. Refining `derive_claim` to `NearSpec` is the
  most tractable missing proof (EVIDENCE row 6).
* The arena SDK packer (`sdk/arena-cli/src/pack.rs`) drops every directory
  named `target` at any depth. That deletes `cc-1.6.0/src/target/` from the
  vendored `cc` crate and breaks the offline build of any package that
  vendors `cc` ≥ 1.2. `arena pack` / `check-local` therefore cannot build this
  package as-is. Our own two-build reproducibility check copies the package
  without that exclusion. The fix belongs in the SDK lane: exclude only
  top-level `source/target` or directories with `CACHEDIR.TAG`.
* `arena pack` writes plain tar. The vendored tree is ≈ 250 MB, just under the
  256 MiB archive cap; tar.zst would be ≈ 60 MB.
* The challenge id is the reexec lane's dev (unsigned) id.
