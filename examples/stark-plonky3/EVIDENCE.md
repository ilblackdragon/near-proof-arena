# stark-plonky3 — evidence matrix

Statuses follow `docs/CONTRACTS.md` §8:

* **checked**: a machine-checked proof, or an artifact property the judge checks;
* **trusted**: a named component of the TCB;
* **tested**: differential, adversarial or mutation testing only;
* **missing**: no evidence.

A missing edge is listed, not hidden.

**Bottom line.** This backend proves the full transfer-batch relation inside
a custom STARK. That covers SHA-256 compression and padding, the trie paths
for the pre and post roots, u128 balances with range checks, gas and refund
arithmetic, the receipts, refund and outcome commitments, and the domain
predicates. The public values are the claim bytes. The supporting evidence is
strong but **tested** only. No formal obligation about the AIR, the proof
system or the Rust verifier is discharged, so the candidate is
**EXPERIMENTAL**. Under the formal profile the judge must reject it:

* `formal/` defines no `Candidate.certificate`, giving `CERTIFICATE_MISSING` /
  `OBLIGATION_UNDISCHARGED`. We did not fake a certificate with holes or
  axioms.
* Even if every proof obligation were discharged, the soundness bound at our
  parameters is below the profile's 128-bit target:
  * Plonky3's calculator gives 102.5 bits per proof in the unique-decoding
    regime.
  * Under the profile's FS accounting with q_H = 2^64 it gives only 38.5
    bits (unique decoding) or 107 bits (Johnson regime).
  * That gives `SECURITY_BOUND_INSUFFICIENT` unless parameters change, and
    stronger parameters do not fit the 8 MiB proof cap with the current
    trace width (README §Security).
* Unlike SP1, the cryptographic obligation **is** expressible with the
  approved assumptions. Every Merkle commitment and every Fiat–Shamir
  challenge uses SHA-256 (`sha256-collision-resistance`,
  `random-oracle-fiat-shamir-sha256`).

## Statement chain

`verify(pub, claim.bin, proof.bin) = accept` should imply that `claim.bin` is
in the language of `NearSpec.TransferV1.NearRelation`.

`formal/Candidate/Pipeline.lean` formalises the chain abstractly, with every
link as a hypothesis: `sound_or_forged`, kernel-checked, axioms ⊆ {propext,
Classical.choice, Quot.sound}.

| # | link | status | evidence / reference |
|---|---|---|---|
| 1 | **IMPL**: `out/verify` computes the modelled verifier | **missing** | See the IMPL detail below the table. |
| 2 | **AIR-ID**: `public.bin` names the constraint system compiled into `verify` | **tested** | See the AIR-ID detail below the table. |
| 3a | **STARK soundness** (DEEP-ALI + FRI round-by-round, batch over 9 instances) | **missing** (bound computed, not proved) | See the STARK detail below the table. |
| 3b | **LogUp** soundness (one `(α, β)` over KoalaBear⁸) | **missing** (bound computed) | `ε ≤ N(W+2)/|EF|`, which gives 221.8 bits at the batch-256 shape. Plonky3 enforces the multiplicity height bound `Σ wᵢhᵢ < p` in the verifier. The design keeps all query counts boolean; checked by inspection and by the concrete evaluator. |
| 3c | **Fiat–Shamir** in the ROM, query-bounded (`q_H = 2^64`) | **missing** | Transcript = `SerializingChallenger32<HashChallenger<SHA-256>>` with the domain separator `near-arena/stark-plonky3/v1`. The public values are observed by batch-stark. The bound `(q_H+1)·ε_rbr + q_H²/2^256` gives 38.5 (UDR), 107 (LDR) and 128 (conjectured) bits. No formal FS theorem exists for multi-round IOPs: VCVio covers FS only for Σ-protocols (formal-ecosystem §3.5–3.6). |
| 3d | **Merkle binding** | **trusted** (`sha256-collision-resistance`, approved) | Leaves are SHA-256 of the canonical u32 serialisation, nodes are `SHA-256(l ‖ r)`. The birthday term is `(2^64)²/2^256 = 2^-128`. |
| 4 | **AIR ⇒ RELATION** (semantic soundness of the hand-written AIR) | **tested** | See the [AIR detail table](#air--nearspec-semantic-soundness-link-4-detail) below. No Lean model of the AIR exists. A route: extract constraints with Plonky3's symbolic builder (the CertiPlonk / LeanZKCircuit pattern, formal-ecosystem §3.3), then prove refinement to `NearSpec.TransferV1.runBatch` and `PTrie.hashOf`. |
| 5 | **COMPLETENESS** (`NearRelation ⇒` the honest prover's traces satisfy the AIR) | **tested** | All 1502 generated in-domain cases, the 20 public fixtures and the 24 workload requests were checked natively: every constraint holds and every bus balances. All 20 + 24 were also proved and verified. Not proved. Proving it requires `runBatch ⇒ trace satisfiability`. |
| 6 | **SHA-256 = FIPS 180-4** inside the AIR | **tested** | See the SHA detail below the table. |
| 7 | **Collision resistance** binding the revealed trie paths to the real `pre_state_root` | **trusted** (approved: `sha256_cr`) | Same as for every backend (spec §4). |

**IMPL detail (link 1).** `out/verify` is native Rust:

* our framing and strict claim decoding: `source/src/proof.rs`, `spec.rs`,
  `wire.rs`;
* the AIR definitions: `source/src/air/*.rs`, about 3.0 k LOC;
* Plonky3 `p3-batch-stark` `verify_batch`, `p3-uni-stark`, `p3-fri`,
  `p3-merkle-tree`, `p3-challenger`, `p3-lookup`, `p3-field` and others at
  rev 3acc8b70, about 70 k lines including tests.

There is no Lean model of any of it. The best route is Aeneas / hax
extraction of the verifier path (formal-ecosystem §4.3). Note that the
Plonky3 transcript binds the *shape* of the AIR but not its constraints, so
the AIR is fixed only by the verifier binary.

**AIR-ID detail (link 2).** `prepare` writes the AIR/config digest: the
config string, plus per table its widths, budgets and preprocessed trace,
plus a Schwartz–Zippel fingerprint of every constraint and interaction at a
fixed point of KoalaBear⁸. `verify` and `prove` recompute it and exit 2 on a
mismatch. The digest is deterministic: identical across builds and runs.
It does not bind the Rust code of the verifier, only the polynomials it
evaluates.

**STARK detail (link 3a).**

* Nothing is proven formally: ArkLib's FRI soundness is still a hole and the
  BCS transform is absent (formal-ecosystem §3.5).
* Plonky3's unverified calculator on the real shapes gives the following
  per-proof bits:
  * proven unique-decoding regime: **102.5**;
  * proven Johnson regime: 128 (CR cap; 171 uncapped);
  * conjectured: 128 (CR cap; 215 uncapped).

  Source: `bench/results-2026-10-03/security-calculator-*.txt` and
  `source/src/security.rs`, with the formulas and references in its module
  docs.
* Parameters: KoalaBear⁸, rate 1/8, 104 queries, 20-bit query PoW.

**SHA detail (link 6).**

* The compression constraints are vendored verbatim from Plonky3
  `sha256-air`, which has proptests against the `sha2` crate upstream and no
  formal proof.
* Our padding and chaining are ours. On every hashed message of every case,
  the digests equal the `sha2` crate's: the native self-check recomputes
  them, and the oracle claims, which use nearcore's SHA-256, match.
* openvm-fv has a proven SHA-256 chip for a different AIR. Clean's SHA-256
  gadget needs `p > 2^33`, which excludes KoalaBear.

### AIR ↔ NearSpec semantic soundness (link 4, detail)

Each row names the part of `NearRelation` (spec §1–§4, claim §3), how the AIR
enforces it, and the evidence for it. Every row's status is **tested**,
meaning: claim conformance (20 + 24 + 1502 cases), forced-witness rejection,
the single-cell probe and design review. None is proved.

| relation component | AIR mechanism | evidence |
|---|---|---|
| claim fields bound | Public values = the 232 fixed-width claim bytes. `verify` checks the tags, protocol version, chain, `n` range, compute limit and `gas_burnt_total = n·G` natively. | 1236 claim byte flips rejected |
| `receipts_commitment` | RCPT emits the header and the exact borsh layout at running offsets. The SHA chain consumes exactly these bytes, and its digest is looked up against the public value. | conformance |
| receipt shape | Constant bytes are emitted for the enum, the counts and the action tag. Key type ∈ {0, 1} with 32/64-byte keys. | forced witnesses for multi_action / non_transfer_action are unrepresentable |
| valid account ids, `not_system_predecessor`, `named_receiver` | Per-char class lookup. Separator rules use degree-4 products. Len 2..64. Sum-of-squares inequalities with inverse witnesses. | forced witnesses rejected (system_predecessor, implicit_receiver) |
| `distinct_receipt_ids` | SORT: a permutation of the ids that is strictly increasing as 256-bit integers. | forced witnesses rejected (duplicate_receipt_id) |
| `receiver_exists_v1` | The walk must end at a touched value slot with `len = 72`. The AccountV1 pre amount ≠ `u128::MAX`. | receiver_missing and account_v2 are unrepresentable |
| per-receipt balance update, `no_balance_overflow`, `storage_stake` | Memory-argument chain per account in receipt order (`t_prev ≤ r`, each write consumed once). Byte adders with boolean carries and no carry-out. Range-checked results. The `u128::MAX` sentinel is excluded. The storage disjunction uses a flag and a range-checked difference. | forced witnesses rejected (balance_overflow, sentinel_balance, storage_stake) |
| burn, refunds, `burn_fits_u128` | Min / refund flag via a range-checked signed difference. `G·p` and `G·D` by byte convolution with range-12 carries and zero overflow bytes. A running u128 total with no carry-out. | forced witnesses rejected (tokens_burnt_overflow) |
| outcome root | Per-receipt outcome and leaf messages. MRK reproduces nearcore `merklize` from `n`, which is forced by the integrality of the level sizes. The root digest equals the public value. | conformance |
| refunds commitment and count | Refund receipts emitted in receipt order behind the public `u32` count header. A running count equals the public value. | conformance |
| pre / post trie, value replacement (spec §4) | NODE: both serializations, which differ only in child and value windows. Child digests are looked up by node id. Node 0 equals the public roots. Unrevealed windows: post = pre. Every `memory_usage` is kept. | conformance; probe |
| key path `0x00 ‖ id` | ACCT sends nibbles (`hi`/`lo` from a fixed table). PATH consumes each exactly once along edges derived from node bytes. Branch slots, hex-prefix nibbles and extension ε-moves are handled. | conformance; probe |
| one slot per account, repeated receivers | `vslot` permutation (each touched slot is offered once). Account rows are unique per key because the walk is deterministic under CR. | design review |
| `witness_size ≤ 3,000,000` | Running sum of revealed node bytes + 72 per touched value, range-checked slack. | design review (never near the limit in tests) |
| SHA-256 padding / no shadow chains | Minimal FIPS padding forced. The first block must contain data. Chaining is by a permutation bus, and `(kind, msg)` ids are consumed exactly once. | probe |

**Soundness review.** We did a manual adversarial pass over every bus and
column. It found one real hole, now fixed (commit "message ids as (kind,
index) tuple pairs"):

* **The hole.** Message ids were encoded as one field element,
  `kind·2^20 + index`. NODE's child-id column is otherwise free, so
  `K_NPRE·2^20 + cid` could alias another kind's message: a post-state node,
  or an account value. A prover could then splice foreign digests into
  post-state windows, i.e. prove a false `slice_post_root` (bounded by which
  digests exist, but still a forgery).
* **The fix.** Kind and index are now separate tuple entries on every bus.

We also checked these and found them sound:

* field-element wrap-around in counters, offsets and level sizes: all are
  forced to be small integers;
* that every lookup/permutation gate is boolean (LogUp height bound);
* that every digest byte consumed by a lookup is range-checked through
  emission to the SHA table;
* SHA "empty message" shadow chains;
* that a walk cannot leave the revealed trie;
* that duplicate account rows cannot share a slot.

### Under-constraint analysis (witness mutation)

`source/src/bin/mutwit.rs`. Starting from an honest trace set, the tool
picks, for every non-multiplicity column of every table, up to 4 random
active rows and 1 padding row. For each, it adds 1 to that single cell.
The mutant is **detected** if one of the following holds:

* (a) some constraint of the affected rows (r−1, r) is non-zero;
* (b) some permutation bus no longer balances;
* (c) some lookup query has no table entry left.

Provider multiplicities are treated as attacker-chosen, so they never count
as kills, and multiplicity columns are skipped.

Results: 8 cases (two tiny, 117, 164, 233 and 256 receipts, 16 receipts),
422,319 mutants:

| table | mutants | by constraint | by perm bus | by lookup | **undetected** |
|---|---:|---:|---:|---:|---:|
| sha | 312,080 | 311,989 | 91 | 0 | **0** |
| rcpt | 36,822 | 29,477 | 5,653 | 1,692 | **0** |
| node | 54,520 | 50,622 | 3,864 | 34 | **0** |
| acct | 12,285 | 8,071 | 3,508 | 706 | **0** |
| mrk | 2,754 | 1,050 | 1,603 | 101 | **0** |
| sort | 3,298 | 3,298 | 0 | 0 | **0** |
| path | 560 | 494 | 32 | 34 | **0** |

The first run of the probe (2 cases, 2 rows per column) found **3,030
undetected mutants**: 1,313 in active rows and 1,717 in padding rows. All of
them were in cells that the semantics never read: chars beyond the string length,
unused carries, `e` when `storage ≤ 770`, `refund_id` without a refund, the
digest windows of unused slots, and padding rows. None was a soundness hole.
We then added canonicalisation constraints (unused cells must be zero,
padding rows zero) so the probe is sharp. The count is now 0.

**What this does and does not show.** It is *tested* evidence that no
single cell is free. It does **not** show that the constraint system is
complete with respect to multi-cell attacks. A coordinated change of many
cells that keeps every local constraint and every bus balanced is exactly
what a soundness proof (link 4) must rule out. For example, a consistent
change of a receipt's deposit together with the dependent amounts would have
to be re-hashed, and is stopped only by the hash/bus structure. The
forced-witness conformance (out-of-domain families) and the design review
are the evidence for those cases.

## Obligation rows (arena gate ids)

| ObligationId | status | why |
|---|---|---|
| `PKG_WELLFORMED` | tested | `arena check-local` PASS. Manifest uses only `arena-candidate-v1` fields. Archive 41.9 MB, 3199 files. |
| `BUILD_REPRODUCIBLE` | tested (locally) | Two offline builds (`unshare -n`) at different paths with fresh `$HOME`s gave bit-identical `out/*`. `check-local` repeated it. Needs Rust 1.96.0 in the build image. |
| `ARTIFACT_BINDING` | missing | No certificate to bind digests to. `public.bin` carries the AIR/config digest, which `verify` recomputes. |
| `FORMAL_SEMANTIC_SOUNDNESS` | checked, but vacuous | `Candidate.backend_semSound` with `B := Rel`. The STARK content is in links 1–6. |
| `FORMAL_SEMANTIC_COMPLETENESS` | checked, but vacuous | `Candidate.backend_semComplete`, same caveat. |
| `FORMAL_CRYPTO_SOUNDNESS` | **missing** | Links 3a–3d. The assumptions are approved ones (SHA-256 CR + SHA-256 ROM), but there is no proof, and the computed bound is below 128 under the profile accounting. |
| `FORMAL_IMPL_CONNECTION` | **missing** | Link 1 (native route; no extraction). |
| `FORMAL_ZK` | not applicable | Validity-only profile. ZK is not claimed: the PCS is non-hiding. |
| `AXIOM_AUDIT` | checked (for what exists) | `#print axioms` of every theorem in `formal/` is ⊆ {propext, Classical.choice, Quot.sound}. No holes, no native evaluation. The lexical scan is clean. |
| `CONFORMANCE_DIFFERENTIAL` | tested | Byte-identical claims on 20 public fixtures, 24 workload requests and 1502 generated in-domain cases. |
| `ADVERSARIAL_PROOFS` | tested | `proof-mutators` `run-mutants`: 360 mutants on 9 cases, all rejected (semantic, binding and packaging kills). `mutproof`: 232 field-level mutants over 22 proof-field patterns, 1236 claim byte flips and cross-case swaps, all rejected. Panics are caught (exit 1). `verify` is deterministic. |
| `PROVER_RELIABILITY` | tested | Every in-domain public fixture and workload request was proved and verified. Out-of-domain requests are refused before proving (exit 3). |
| `RESOURCE_LIMITS` | tested (within limits) | Proof 7.14 MB ≤ 8 MiB (85%). Verify ≤ 0.3 s ≤ 10 s. Prove ≤ 1.3 s ≤ 600 s. RSS ≤ 1.3 GB ≤ 16 GiB. |
| `BENCHMARK` | local only | README §Headline numbers (8 pinned CPUs, shared host). |

## TCB of an accept today

* The Plonky3 proof system at rev 3acc8b70: batch-STARK / DEEP-ALI / FRI /
  LogUp soundness at our parameters (an unproven bound), and its verifier
  implementation.
* SHA-256 as collision-resistant hash and as random oracle (both approved
  assumptions).
* Our AIR (`source/src/air/`) as a faithful encoding of `NearRelation`
  (tested, not proved), including the vendored SHA-256 compression
  constraints.
* Our verifier glue: claim decoding, static domain checks, proof framing,
  height caps and AIR-digest check.
* The Rust toolchain (rustc 1.96.0) and the vendored crates (pinned by
  `Cargo.lock` checksums and `dependency-locks/vendor-digest.txt`).

## Upstream formal work and its relevance

| project | relevance here |
|---|---|
| ArkLib (`ace55c3`) | FRI/STIR soundness and the BCS transform are holes or absent. Proven: BCIKS20 unique-decoding proximity gaps and the Johnson bound. These are the building blocks for link 3a. |
| VCVio (`f5119c6`) | Has ROM machinery and Merkle extractability. Fiat–Shamir only for Σ-protocols. Building blocks for 3c / 3d. |
| LeanZKCircuit-Plonky3 / CertiPlonk | Pattern for link 4: print `SymbolicExpression` constraints into Lean. Its bus/LogUp soundness is not proven. |
| openvm-fv | Proves SHA-256 chips against a FIPS model for a different AIR. Shows link 6 is doable. |
| Aeneas / hax | Route for link 1. No STARK verifier has been bound yet. |
