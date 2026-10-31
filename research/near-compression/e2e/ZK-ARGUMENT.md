# Zero-knowledge argument for the chunk proof: status, construction, simulation sketch

Status (2026-10-31): **not zero-knowledge.** The delivered packet (`FINAL.bundle`) is a
proof of knowledge of a valid chain, and the e2e runs keep `zero_knowledge_established=false`.
Nothing in the main PQ stack (`stark-backend-unified` SWIRL prover, the NV recursion circuit) masks
anything today. This file records what leaks, what each component needs, which published
constructions give HVZK, how the simulator would go, what was measured, and the gap.

## 1. What the verifier sees

| item | source | public by design? | leaks witness information today? |
|---|---|---|---|
| `claim.bin` | chunk-header outputs + the claim's trusted facts | yes | no (it is the statement) |
| hint (16–155 B) | refund receipts the chunk produced; `statepublic` checks it against the claim | yes (derived output) | no, provided the hint is a function of the claim's outputs; it is checked, not trusted |
| `SETUP.json` (pinned) | final vk, program, level, base params | yes (trusted setup) | reveals the chunk *shape* class (trace heights fixed per setup) — a size leak any per-shape setup has |
| base stacking point `u` (v2 packets, 19 x 48 B) | Fiat–Shamir output of the base transcript | yes (needed to evaluate the public TAPE) | **yes**: `u` is a hash of the base proof's commitments, i.e. a deterministic function of the base witness. Without hiding base commitments it is a witness fingerprint (it lets anyone test a guessed witness). |
| `common_main_commit` (final) | Merkle root of the final NV trace codeword | — | yes: unsalted leaves, so the root is a deterministic function of the trace |
| GKR proof | layer claims + sumcheck round polynomials | — | yes: every round polynomial is a fixed polynomial function of the trace |
| batch-constraint proof | univariate-skip and zerocheck rounds, **column openings at r** | — | yes: openings are trace MLE evaluations |
| stacking proof | round polynomials, stacked openings at u_F | — | yes |
| WHIR proof | sumcheck rounds, OOD answers, **opened codeword rows** (~131 queries per round 0 commit), final polynomial | — | yes: opened rows are raw codeword symbols of the trace |
| public values of the final proof | level + statement digest | yes | no |

The final trace is the NV verifier's execution on the L5 proof, so leaking it leaks L5, which is a
proof about L4, and so on down to the base witness. There is no argument that the leakage
attenuates with depth; a ZK statement needs the final layer to be ZK.

## 2. What ZK needs, by component (final layer only; plus one base-layer item)

Inner layers (base, L1–L5) are never published, so they need no ZK — with one exception created by
this run's verifier fix: the base point `u` is now public (item Z6).

| # | component | construction | HVZK basis | status |
|---|---|---|---|---|
| Z1 | Merkle commitments of the final trace and every WHIR fold oracle | salted leaves: each leaf hashes `salt_i ‖ row_i` with a fresh λ-bit salt; the salt is sent with each opened leaf | hiding of a salted RO commitment (statistical, ≤ q·2^-λ_salt for q RO queries) | not implemented. Cost estimate: one 32-B salt per opened leaf; with `multiproof` openings ≈ (sum of queries) x commitments ≈ 131 x 2 + 90 ≈ 350 leaves ≈ **11 KB** |
| Z2 | trace evaluations (column openings at r, GKR input claims, stacked openings) | randomize every final-layer column off the hypercube: commit f̂ = f + Z·m, Z vanishing on {0,1}^n (e.g. X_1(1-X_1)), m uniform with at least as many coefficients as evaluation claims made about f̂; or append random rows gated out by a selector column | an opening of f̂ at a point outside the hypercube is uniform given fewer claims than mask coefficients (linear independence of the evaluation functionals) | not implemented; needs prover kernels for a degree-2 first variable (the fast `cpu-backend` zerocheck/GKR kernels assume multilinear columns) |
| Z3 | sumcheck round messages: GKR (≈ 30 layers), zerocheck, stacking | Libra / Chiesa–Forbes–Spooner masking: prover commits a random g = Σ_i g_i(X_i) per sumcheck (hiding commitment), sends σ = Σ g, verifier sends ρ, the sumcheck runs on F + ρ·g; g(r) is opened at the end through the PCS | round messages are simulatable from F(r) (Libra Thm. 3; CFS17) and F(r) is uniform by Z2 | not implemented |
| Z4 | WHIR (the PCS) | HVZK-WHIR, eprint 2026/391: masked WHIR sumcheck (Constr. 6.3), zero-evader pad on OOD answers, ZK Reed–Solomon encodings with a randomness budget ≥ queries per oracle, masked base case (Constr. 7.2), code switching (Constr. 9.7) | the paper's simulator (implemented in Plonky3 `sumcheck/src/zk/simulator.rs`, `whir/src/pcs/zk`) | not ported; overhead measured in Plonky3 (§4) |
| Z5 | Fiat–Shamir | the HVZK interactive protocol with salted commitments, compiled in the (Q)ROM | standard: NIZK in the programmable ROM from HVZK + hiding commitments (simulator programs the oracle) | follows once Z1–Z4 exist |
| Z6 | the published base point `u` | either (a) salt the base layer's commitments (main and TAPE) so `u` is a fresh RO output on high-entropy input, simulatable as uniform; or (b) move the TAPE-evaluation check into the final circuit so `u` is never published | (a) RO output on an unpredictable input is uniform and independent of the claim; the simulator samples `u` and computes the public TAPE opening itself | not implemented; (a) costs nothing in the packet |

Public inputs after Z1–Z6: exactly `claim.bin` (chunk-header outputs + trusted facts), the hint
(derived outputs checked against the claim), and the pinned setup. `u` would be part of the proof
string, not a public input.

## 3. Simulation sketch (for the construction of §2)

Sim(claim, hint, setup):
1. Sample `u` uniform in EF^19 (Z6a). Compute y = TAPE_pub(u) from the claim (as the verifier does).
   The statement digest d = node(G1(pvs), H(u, y)) is then a public function of (claim, u).
2. Final layer: run the HVZK simulators in transcript order, programming the random oracle:
   * commitments (Z1): output uniform roots; salts make the real roots RO outputs on unpredictable
     inputs, so the two are identical except with probability ≤ q·2^-λ_salt;
   * PIOP (Z2+Z3): sample the masked column openings uniform (Z2), sample each masked sumcheck's
     round polynomials uniformly subject to the round-consistency equations, set the final value to
     match the (uniform) openings; this is the Libra simulator;
   * PCS (Z4): the HVZK-WHIR simulator given the claimed evaluations (it needs only the
     evaluations, which step 2 fixed).
3. Output (hint, u, π_F). The verifier's checks pass by construction; indistinguishability is
   statistical, error ≤ q·2^-λ_salt + Σ (per-component masking failure: e.g. a challenge landing in
   the hypercube coordinate set {0,1}, or more evaluation claims than mask coefficients).

The per-component failure terms have not been computed; that is part of the obligation below.

## 4. Measured cost of the PCS part (Plonky3 HVZK-WHIR, this host)

`results/zk128-sweep.txt`, from `whir/examples/zk128.rs` (patch `patches/plonky3-zk128-example.patch`
against Plonky3 `3acc8b7`), KoalaBear^8, SHA-384 Merkle with an 11-element (341-bit) digest — the
closest serializable analogue of the PQ track's 42-byte truncation — one committed column.

| n (vars) | target | regime | rate | grinding | ell_zk / mask rate | plain B | HVZK B | **ZK delta** |
|---:|---:|---|---:|---:|---|---:|---:|---:|
| 16 | 100 | capacity | 1/4 | 16 | 16 / 1/32 | 44,966 | 149,439 | +104,473 |
| 18 | 100 | capacity | 1/4 | 16 | 16 / 1/32 | 52,086 | 156,563 | +104,477 |
| 18 | 128 | Johnson | 1/2 | 0 | 3 / 1/8 | 187,534 | 480,858 | +293,324 |
| 18 | 128 | Johnson | 1/64 | 30 | 16 / 1/32 | 71,512 | 293,598 | **+222,086** |
| 20 | 128 | Johnson | 1/64 | 20 | 16 / 1/32 | 99,847 | 412,254 | **+312,407** |

Readings:
* The 100-bit point reproduces `bench/RESULTS.md`'s *additive, size-independent* overhead; with
  341-bit digests instead of 8-element Poseidon2 digests it is 104 KB instead of 72.6 KB.
* **At the PQ track's level (128-bit Johnson, rate 1/64) the overhead is 222–312 KB, not the
  model's 92.9 KB.** The mask oracles are spot-checked without grinding at the full security level
  (`mask_queries = queries(λ + log(2·rounds+2), mask rate)`), so they do not get the z-bit discount
  the main oracle gets, and Johnson-regime bits per query are about half of capacity's.
* Applied to this run's 306–307 KB non-ZK packets, a ZK final layer would be ≈ 530–620 KB, over
  the ~400 KB the owner accepted. Levers, none measured here: grinding on mask spot checks (a
  Plonky3 change), a lower-rate mask code, fewer WHIR rounds in the wrap (fewer mask oracles), or a
  ZK layer over a smaller (compressed) inner proof.
* Prover time: 1.03–1.6× at 100-bit; the 128-bit rows' single-core times are dominated by grinding
  and are not comparable. The 128-bit Johnson-bound octic configuration that panicked in
`bench/RESULTS.md` constructs and proves at this Plonky3 revision (`zk128 18 128 1 0 3 3`), so the
"crash" is resolved upstream; the remaining ZK overhead number is the one in the table.

## 5. Machine-checkability

The repo's zk-formal pattern (Lean, `docs/zk-formal`) specifies and proves *the relation* (what a
valid chunk is) and the checker; it does not model the proof system, let alone its zero-knowledge.
There is no Lean model of SWIRL, WHIR, or a sumcheck here to state HVZK against. The pieces that
could be formalised in that pattern at moderate cost are the finite linear-algebra lemmas: (i)
Libra masking makes the round messages a function of F(r) and uniform randomness, (ii) k
evaluations of f + Z·m at points outside the hypercube are uniform when the evaluation functionals
on m are independent. Neither is done. **Gap: no machine-checked ZK statement exists for any layer.**

## 6. Obligation list to set `zero_knowledge_established=true`

1. Z1–Z4 in the final layer prover and native verifier (the NV circuit never verifies a final proof,
   so the recursion circuit does not change); Z6 in the base layer.
2. The concrete HVZK error bound per component (§3) at the final layer's parameters.
3. Soundness re-derived for the masked protocol (masks add rounds and oracles; the 268-bit RBR
   budget of every component must be re-checked, HVZK-WHIR has its own RBR analysis).
4. A test that the simulator's output and real proofs have identical shape and pass the verifier,
   and statistical tests on opened values (necessary, not sufficient).
