# RESTRICTED: NF-1 / NF-2, which deployed systems use the pattern

**Restricted. Do not circulate, post, or open issues.** Whether and how to tell maintainers is
the user's decision. Written 2026-10-18 by the novelty-prior-art lane. Summary form only.

## Bottom line

* **We found no attack**, classical or quantum. PRIOR-ART.md §1.3 gives the arguments:
  * Classical ROM: the chained pattern gives the full grinding credit, T·2⁻ᶻ·ε + O(T²/2ⁿ).
  * QROM, fixed prefix: a reduction to unstructured search gives O(t²·2⁻ᶻ·ε).
  * QROM, under state restoration: what is missing is a proof, not security.
* So for the systems below, the finding is a **gap between the security proof and the code**,
  and it matters only to a system that claims *proven* QROM security that includes grinding
  credit.
* None of the four claims that, as far as we saw. They claim classical, conjectured or
  calculator-level security (100–128-bit, rbr in the ROM).
* Three of the four run a duplex sponge over a permutation (Poseidon2). No QROM Fiat–Shamir
  theorem exists for that construction even without grinding (Chiesa–Orrù 2025/536 §1.3;
  HHMRS 2026/146 covers only 3-round protocols with one-block challenges). So NF-1 adds nothing
  to their existing quantum gap.
* **Our recommendation: no coordinated disclosure is needed.** It is a theory remark that can
  be published with the systems named. As a courtesy, consider giving a short heads-up to the
  WHIR and spongefish authors, whose pattern is already the safe one, and to Plonky3 before
  publishing. That is the user's call.

## Code survey (clones at the commits listed; details in the lane scratchpad)

Patterns:
* **A, chained:** the PoW bits are bits of s′ = Absorb(σ, w), and some or all query indices
  come from later calls on s′.
* **C, separate PoW hash:** the PoW hash and the index stream are two different functions of
  (transcript, nonce). This is equivalent to one long-output call, so it is covered.

| system @ commit | primitive | pattern | where |
|---|---|---|---|
| Plonky3 @576717ee9 (all challengers: Duplex, Hash, Serializing32, MultiField32; FRI and WHIR) | Poseidon2 duplex, or Keccak hash chain | **A, partial**: the PoW comes from rate element 7 of s′; elements 6..0 of the same s′ give 7 indices; the rest come from π(s′), π²(s′)… or H(o), H(H(o))… | `challenger/src/grinding_challenger.rs:48-54`; `duplex_challenger.rs:86-112, 253-288`; `hash_challenger.rs:59-67`; `fri/src/transcript.rs:547-580`; `whir/src/transcript/mod.rs:904-922` |
| OpenVM stark-backend v2 (WHIR) @362c7ad8c | Poseidon2 BabyBear duplex, overwrite mode | **A, partial** (same shape) | `transcript/traits.rs:46-89`; `verifier/whir.rs:160-166`; `transcript/duplex_sponge.rs:62-83` |
| SP1 Hypercube @02fa30185 (native, and the in-circuit recursion verifier) | p3-challenger 0.4.3-succinct, KoalaBear duplex | **A, partial** | `slop/crates/whir/src/verifier.rs:321-331`; `crates/recursion/circuit/src/challenger.rs:237-243` |
| Winterfell @2f78ee9bf | hash (`merge_with_int`, Blake3 / RPO) | **A, pure**: s′ = H(seed‖nonce) carries the PoW bits and becomes the seed; indices come from H(s′‖1), H(s′‖2), … | `crypto/src/random/default.rs:141-146, 210-221, 81-85` |
| Stwo @826591c6c | Blake2s / Poseidon252 channel | C, not affected | `core/channel/blake2s.rs:124-140`; `core/pcs/verifier.rs:73-79` |
| WHIR reference @afec1fac2 | SHAKE128 XOF, Blake3 PoW | C, not affected | `src/protocols/proof_of_work.rs:208-231` |
| spongefish @52ec5f388 / nimue-pow @0e584985d | TurboSHAKE / Keccak duplex | C, not affected | `pow/src/protocol.rs:77-94`; `nimue-pow/src/lib.rs:46-70` |
| RISC Zero @3bbcd44d6 | Poseidon2 RNG | no PoW at all | `risc0/zkp/src/verify/fri.rs:131-142` |

**Count:** 4 deployed codebases use pattern A: Plonky3, OpenVM v2, SP1 Hypercube and
Winterfell. Many downstream zkVMs inherit pattern A from Plonky3. Our own pre-T\* code had it
too; commit 46b7e62e2 fixed it.

## NF-2 (multi-call squeezing) in the same systems
* Every hash-chain or duplex system above squeezes long index vectors across several sequential
  calls. That includes ours before T\*, Plonky3, OpenVM, SP1 and RISC Zero.
* Winterfell and Stwo use counter mode from one seed, which matches T\*-1. The WHIR reference
  and spongefish use one XOF stream, which is equivalent to one long-output call when SHAKE is
  modelled as an RO.
* Same status as NF-1: a proof gap, with no attack known or expected.

## Side observations (not security issues)
* nimue-pow stores the nonce big-endian in the transcript but hashes it little-endian. This is
  harmless.
* SP1's p3 fork has no early return at bits = 0, so the witness is always absorbed. Upstream
  Plonky3 and OpenVM skip it, which is malleability only. That matches our G-11.
* The `sample_bits` 1/p bias in Plonky3 is already public (issue #613).
