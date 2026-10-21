# The A-IC obstruction, and what any replacement for A-IC must assume

> **2026-10-21 review and G-P1 scope.** The historical numerical claims below
> are not established security bounds. The family instantiation and NV theorem
> they invoke remain open. Theorem O is a conditional obstruction under H-ex(C),
> recursive-witness completeness and outer completeness; it does not prove
> H-ex for concrete SHA-384, that an honest test establishes universal
> completeness, or that A-IC(τ) becomes true upon imposing a time limit.
> Its cap-based numerical estimates need revision for the actual sampler.
> Sections 5–7 below supersede the former Lemma P and Corollary P.1.


Lane `lane/pq-aic-research`, 2026-10-18. Companion to `REPORT.md`. Notation and numbering of
`../final-soundness/PROOF.md` (cited as PROOF §x / Thm 6.4 / Lemma 7.1 / Assumption 7.3).

Tags (as in PROOF.md): **[T]** proven here, complete as written, not yet reviewed;
**[S]** argued at protocol level, every step stated but one or more steps not written out to
the level of [T] — each such step is marked **(unproven step)**; **[P]** proven in a cited
published source; **[A]** assumption.

## 0. Current results and proof status

| Result | Established scope | Open boundary |
|---|---|---|
| Theorem O | Conditional lifting of an existing false concrete inner proof to an outer-oracle forgery | H-ex(C), witness/inner completeness and a quantified outer completeness/query budget must be supplied; no concrete-SHA H-ex proof is claimed. |
| E.1–E.3 | Historical protocol-level construction and random-function argument | E.3 contains an explicit unwritten case check; the sampler-cap instantiation is invalid for the pinned implementation. These do not prove concrete SHA-384 admits a false proof. |
| Lemma P accounting | Correct scalar peeling inequality, kernel-checked | Actual family potential, extraction, NV faithfulness, coherent inner security game and resource bounds remain open. |
| G-P1-C | Written quadratic lower bound for universal fixed-interface circuit simulation, including arbitrary private quantum encodings | Independent review required; the quantum information argument is not formalized. QRAM, feedback and adversary-specific reductions are outside its scope. |

Theorem O establishes a conditional obstruction in its defined model. It does
not prove a universal impossibility for all oracle models or the necessity or
truth of the particular A-IC(τ) formulation.

---

## 1. Models

**Definition 1.1 (certified relation).** For i ≥ 1, the layer-i AIR NV_i contains SHA rows that
constrain message/digest pairs. Let C ⊆ M × {0,1}³⁸⁴ be the set of pairs (m, y) that a row
sequence of the SHA AIR can certify, with the framing of PROOF §1.3. Two cases:
* (a) **concrete:** C = graph(F) for the concrete function F computed by the SHA-512-compression
  AIR (truncated per PROOF §1.3). This is the system as built.
* (b) **unconstrained:** the hash rows are free columns ("oracle gates"), C = M × {0,1}³⁸⁴.
  This is the "relativized" circuit of BCG24 Def 3.5/§3.4 and Arnon–Yogev 2025/329 Defs 4.1–4.2,
  when the argument does not check the gates.

For a deterministic verifier V that makes hash calls, write V^C(x, π) = 1 iff V accepts when
every hash call on input m is answered by some y with (m, y) ∈ C, consistently (equal inputs,
equal answers). For C = graph(F) this is V^F.

**Remark 1.2 (C is independent of H — forced).** In any oracle model the scheme (vk_i, its AIR,
its constants) is fixed before H is sampled, and an AIR's satisfying set is defined by fixed
polynomial identities over BabyBear. So C does not depend on H. The only ways for the certified
relation to depend on H are: (1) the native verifier itself queries H on each certified pair —
CGSY24 §6.3/Thm 6.5 "weak relativized NARK", proof size + O(q·λ), not succinct; (2) the oracle
carries an algebraic structure the argument can use — the AROM (CCGOS23 Def 4.1). Neither is
the system as built.

**Definition 1.3 (model M(C)).** H is a uniformly random function on the domain-separated sets of
PROOF Lemma 1.1 (quantum-accessible). The final verifier V_d uses H. For 1 ≤ i ≤ d, the layer-i
relation R_{vk_i} certifies hash pairs in C, so NV-faithful (F1) reads: T ∈ R_{vk_i}(x_i) ⇒
V_{i−1}^C(vk_{i−1}, x_{i−1}, dec_i(T)) = 1 (for C = graph(F) this is exactly PROOF Lemma 7.1,
which is stated for the concrete SHA-384). The adversary is quantum, makes ≤ t queries to H, and
is **unbounded in running time** — the convention of PROOF Thm 6.4 and of the Main Theorem.

**Definition 1.4 (H-ex(C)).** There are a base statement x₀ whose chunk-validation claim is false
(Lemma 7.2's predicate fails for every witness) and a proof π₀ with V₀^C(vk₀, x₀, π₀) = 1.

**Definition 1.5 (C-completeness).** For every i ≥ 1 and every (x_{i−1}, π_{i−1}) with
V_{i−1}^C(π_{i−1}) = 1, the honest layer-i prover run with hash C (C = graph(F)), on the honest
NV_i witness, outputs π_i with V_i^C(π_i) = 1. This is completeness of SWIRL instantiated with F.
This is a universal premise, not a conclusion from successful honest test
runs. The old cap-based completeness estimate does not apply to the uncapped
native sampler. For an outer adversary with a capped runtime/query budget, a
separate completeness bound is needed.

---

## 2. Theorem O (conditional query-only obstruction)

**Theorem O.** Fix d >= 1 and C independent of the external oracle H. Assume
H-ex(C), inner C-completeness and NV witness completeness/statement linkage at
every required level. Also assume the honest outer prover, on the resulting
valid relation witness, makes at most Q_out H-queries and is accepted with
probability at least 1-epsilon_comp. Then in M(C) there exists an adversary
using at most Q_out H-queries which produces an accepted outer proof naming a
false base statement with probability at least 1-epsilon_comp.

*Proof.* Choose the accepting false base pair furnished by H-ex(C). An
unbounded adversary can find it without H-queries, or take it as nonuniform
advice independent of H. Apply witness completeness and inner C-completeness
at levels 1,...,d-1. This yields a concrete inner accepting proof naming the
same false base statement, still without querying H. Its honest NV_d witness
satisfies the outer relation by witness completeness. Run the assumed outer
prover with H on that witness. Its query bound and acceptance probability are
exactly Q_out and 1-epsilon_comp, and statement linkage preserves falsity. ∎

A numerical query-only contradiction follows **if** Q_out is below the claimed
query budget and 1-epsilon_comp exceeds the claimed failure bound. The previous
numbers Q_out <= 2^46 and epsilon_comp <= 2^-1000 have not been re-established
for the pinned implementation; the prior sampler-cap argument was invalid.

**Interpretation.** Within these hypotheses, query-only recursive semantic
security requires either excluding the false inner pair (perfect inner
soundness), restricting the adversary's computational/advice capabilities, or
changing the relation/model. This is a necessity result under explicit premises,
not evidence that a runtime restriction suffices. Literal consistency between
concrete SHA and an independent H has a separate marginal obstruction even for
fixed efficiently computed pairs (`Qrom.OracleBridge`).

---

## 3. Existence of accepting proofs of false statements

### Lemma E.1 (unconstrained gates) [T at protocol level]
In case (b), H-ex(C) holds for every false base statement x₀.

*Proof.* In case (b) every hash answer in V₀'s computation is prover-chosen. Then:
* every Merkle authentication check passes by choosing the node outputs top-down to equal the
  required values; the PoW check passes by choosing the PoW block with z leading zeros;
* every Fiat–Shamir challenge is a prover-chosen value;
* hence the prover may commit to nothing and choose every opened value after the challenges.

Fix any trace T′ of the right shape with correct program columns. Run the honest prover on T′
and, at every verifier move, choose the challenge to be a root of the difference between the
claimed and the true round polynomial whenever the current claim is false (a false claim at a
sumcheck round with message degree D ≥ 1 has a cheating message whose difference polynomial has
a root in K∖{0, 1}; see the construction in Lemma E.2). After that move the claim is true, and
from then on the honest prover's messages pass. All WHIR checks pass because the opened values
are those of a genuine codeword (T′'s encoding), or are chosen freely. ∎

### Lemma E.2 (lucky move against a random function) [T]
Let K = F_{p¹²}, |K| = 2^{370.88}, char K ≠ 2. Consider one round of an FS-compiled sumcheck
under T\*: the state σ is fixed; the prover sends s ∈ K[X] of degree ≤ D (D ≥ 2), required to
satisfy s(0) + s(1) = c′; the challenge is r = Samp(G(Abs(σ, s))), where Abs and G are the
restrictions of a uniformly random F to the disjoint absorb and squeeze domains, encodings are
injective (PROOF Lemma 1.1), and Samp maps uniform blocks to a uniform element of K except with
probability ε_cap ≤ (1/16)^{12·2²⁰} (PROOF Lemma 6.3). Let s\* (degree ≤ D) be the true round
polynomial, with s\*(0) + s\*(1) = c ≠ c′. Then

  Pr_F[ ∄ s : s(0)+s(1) = c′ ∧ s(r(s)) = s\*(r(s)) ] ≤ 2⁻¹²⁰⁰⁰.

*Proof.*
1. **Candidates.** Put δ = c′ − c ≠ 0. For a ≠ b in K with N(a,b) := ab + (1−a)(1−b) ≠ 0, let
   Δ_{a,b}(X) = δ·(X−a)(X−b)/N(a,b) and s_{a,b} = s\* + Δ_{a,b}. Then deg s_{a,b} ≤ D,
   s_{a,b}(0) + s_{a,b}(1) = c + δ·N(a,b)/N(a,b) = c′, and s_{a,b}(a) = s\*(a), s_{a,b}(b) = s\*(b).
   Distinct unordered pairs {a,b} give distinct s_{a,b} (the root sets differ). The number of
   admissible pairs is ≥ (|K|² − 3|K|)/2 > 2⁷⁴⁰. Take any M = 2³⁸⁴ of them.
2. **Absorb outputs.** The κ_{a,b} := Abs(σ, s_{a,b}) are M independent uniform 384-bit strings
   (distinct inputs). Let N_κ be the number of distinct values. E[N_κ] = 2³⁸⁴(1 − (1 − 2⁻³⁸⁴)^M)
   ≥ 0.632·2³⁸⁴. N_κ is 1-Lipschitz in each κ, so by McDiarmid, Pr[N_κ < 2³⁸³] ≤
   exp(−2(0.132·2³⁸⁴)²/2³⁸⁴) = exp(−0.035·2³⁸⁴) < 2^{−2³⁷⁹}.
3. **Challenges.** Condition on the absorb values. G is independent of Abs (disjoint domains),
   so the challenges r_κ at distinct κ are independent and, outside the cap event, uniform on K.
   For each distinct κ pick one candidate {a,b} with κ_{a,b} = κ. It wins iff r_κ ∈ {a, b}:
   probability 2/|K|. So Pr[no win | N_κ ≥ 2³⁸³] ≤ (1 − 2/|K|)^{2³⁸³} + 2³⁸⁴·ε_cap
   ≤ exp(−2^{384−370.88}) + 2⁻⁵⁰⁰⁰⁰⁰⁰ ≤ 2⁻¹²⁸⁰⁰ (log₂e·2^{13.12} ≈ 12 840).
4. Total ≤ 2^{−2³⁷⁹} + 2⁻¹²⁸⁰⁰ ≤ 2⁻¹²⁰⁰⁰. ∎

The same argument applies to any verifier move whose check is "a nonzero polynomial of degree
≥ 1 in the challenge vanishes" and whose preceding prover message ranges over a family with
≥ 2³⁸⁴ members with distinct roots — e.g. the GKR line reduction (claim (1−μ)a′ + μb′ vs the
true (1−μ)a + μb, with (a′, b′) ranging over the solutions of the root relation).

### Lemma E.3 (random F satisfies H-ex) [S]
For F uniformly random (independent of H), H-ex(graph F) and graph(F)-completeness hold except
with probability ≤ 2⁻¹¹⁹⁹⁰.

*Argument.*
1. Take a false base statement x₀ and any trace T′ of the right shapes, with correct program
   columns, whose public values name x₀. T′ ∉ R_{vk₀}(x₀).
2. The cheating prover commits honestly to T′'s encoding (a genuine interleaved codeword), so
   every WHIR claim about it that is *true* is proven by the honest WHIR prover.
3. **(unproven step)** Every reason T′ ∉ R surfaces as a *false* claim in some sumcheck-type
   move of the PIOP (zerocheck for constraint violations, LogUp-GKR for unbalanced buses, the
   root relation for the GKR output), and each such move's message space contains a two-root
   family as in Lemma E.2. This needs the message shapes of PROOF §3: plain rounds of degree
   ≥ 2; Gruen rounds s = eq_pre·eq₁(ξ, X)·t(X) with t of degree 2 and one linear constraint, so
   that t′ − t = c·(X−a)(X−b) with c fixed by the constraint whenever that coefficient is nonzero.
   This is a routine but unwritten case check over every sub-protocol.
4. Apply Lemma E.2 at the first false claim of each sub-protocol (≤ 2⁶ applications): after the
   lucky round the claim is true, and the honest prover continues. Union bound ≤ 2⁶·2⁻¹²⁰⁰⁰.
5. PoW witnesses exist for each move except with probability (1 − 2⁻³²)^{2⁶⁴} per move;
   sampler caps as in Theorem O step 3. ∎

**Status of H-ex for the concrete SHA-384.** It is a finite statement about one function and
cannot be proven or refuted with known techniques. Its negation — that the FS/Merkle-compiled
base verifier with concrete SHA-384 is *perfectly* sound for every false statement — would be a
statistically sound succinct non-interactive proof with a fixed hash, which fails for all but a
2⁻¹¹⁹⁹⁰ fraction of functions (Lemma E.3) and which no one believes for SHA-384.

---

## 4. Consequence for the paper

Under Theorem O's completeness and budget premises, a query-only recursive
soundness theorem with error below 1-epsilon_comp would imply the negation of
H-ex(C). This is its precise contrapositive. No proof of perfect soundness or
its negation for the concrete SHA-384 base verifier is supplied here.

The computational peeling route instead bounds the resources of the extracted
inner adversary. It is a separate conditional theorem, stated next. Its cost
and advice model must be explicit; calling it A-IC(τ) does not discharge these
requirements.

---

## 5. Corrected Lemma P: conditional peeling accounting

**Scope.** The final layer uses an independent QRO on `P_fin`; all in-circuit
hash evaluations use concrete SHA-384 on `P_in`. The pinned G2 implementation
already separates these domains (`new_final` and the final node prefix). The
old statement that H-1 is absent from the code is obsolete. No construction
change is proposed.

Let `p` be the real outer false-statement acceptance probability and `p_D` the
corresponding measured-database event. Suppose the actual family proof supplies

```
sqrt(p) <= sqrt(p_D) + sqrt(slack),   slack = ell_V / 2^336,
```

and an implemented extraction reduction B satisfies

```
p_D <= Pr[B breaks the concrete inner system] + epsilon_bad + delta_sim.
```

Here `epsilon_bad` is the proved outer bad-event probability and `delta_sim`
bounds the event-probability discrepancy of an approximate simulator/extractor.
For an exact simulation, `delta_sim = 0`. If the stated inner security game
bounds B's success by `epsilon_S`, then

```
p <= (sqrt(epsilon_S + epsilon_bad + delta_sim) + sqrt(slack))^2.
```

This scalar implication is checked in `Qrom/Peeling.lean`. The former expression
`(sqrt(epsilon_S) + sqrt(slack))^2 + epsilon_bad` omitted a cross term.
The same file checks a counterexample with `epsilon_S = 0`,
`epsilon_bad = slack = 1/16`, `p_D = 1/16` and `p = 1/4`.
These scalar results do not construct B or discharge the protocol premises.

B's required resource bound is

```
T_B <= T_A + T_init + T_sim(q_sim, lambda, delta_sim)
             + T_measure(q_sim, lambda) + T_extract(q_sim, n).
```

Charge simulated verifier queries, long-output expansion, database readout,
list recovery and trace decoding. `T_extract = poly(n)` independent of the
measured database is not established. The exact decoder at the actual O-2
radius needs a concrete cost bound; citing an existential codeword or an
asymptotically polynomial decoder is insufficient at the headline parameters.

**Inner assumption.** State the setup distribution, parameter family, permitted
advice and preprocessing, memory model, time unit and success event. In
particular, with a deterministic fixed public verifier, any existing short
accepting false pair can be hard-coded into a nonuniform adversary and output
in time linear in its length. Charging only online time cannot exclude it.
An assumption quantifying over arbitrary setup-dependent advice would therefore
be false whenever such a pair exists. Uniformity alone does not repair a
concrete fixed-instance statement quantified over all algorithms: a finite
hard-coded pair is also computable. An asymptotic uniform-family claim, a game
that fixes the adversary before fresh randomness, or a precisely charged
preprocessing model must be specified and justified before calling `S_(d-1)`
meaningful. None follows merely from the name "standard-model security"; this
note does not alter the implementation to introduce a setup.

The result, when all premises are established, relocates the recursive semantic
assumption to the inner concrete system. It does not prove the inner assumption,
nor is it currently a complete protocol theorem.

## 6. G-P1: the exact investigation and present result

**Question.** For arbitrary adaptive q-query adversaries, is there an online
compressed-oracle simulator, with a readable final database and the required
joint-state equivalence, whose total ordinary bounded-arity quantum gate count
is `q * poly(lambda, log q, log(1/delta))`? Include initialization, reversal,
conversion to the measurement basis and extraction. Require a concrete
approximation error `delta`; exact simulation is a stronger variant.

**Literature baseline.** Don–Fehr–Majenz–Schaffner, Theorem 4.3 and Appendix B,
state total simulator time `O(q_RO*q_E*Time[f] + q_RO^2)` for their sparse
representation. This provides a quadratic upper bound, not a lower bound on
all simulators. The sorted representation and its readout are described
explicitly. [Online-Extractability in the QROM](https://arxiv.org/pdf/2103.03085)

The September 2026 version of Foxman–Lombardi–Ma–Nehoran–Wright defines efficient
on-the-fly simulation as polynomial time in the query number and `log N`; that
definition does not supply the quasi-linear bound sought here (§3).
[Quantum Lazy Sampling and Path Recording for Any Group](https://arxiv.org/pdf/2606.30281)

**Candidate route and cost boundary.** A coherent dictionary could avoid a
linear scan if lookup, insertion and deletion have polylogarithmic cost, preserve
one canonical encoding per database, and uncompute all temporary information.
Ambainis §6 explicitly uses quantum random-access gates for its history-independent
data structure and explains why retaining insertion history changes interference.
That is evidence for a route in an augmented memory model, not an ordinary-gate
implementation of G-P1. [Quantum walk algorithm for element distinctness](https://arxiv.org/abs/quant-ph/0311001)

A classical balanced tree or hash table is insufficient: quantum lookup must
work on superpositions, and two paths reaching the same database must interfere
as the same encoded state. A randomized dictionary also needs a worst-case
coherent execution bound and a bound on bad-seed amplitude, not merely expected
classical lookup time. Adding unit-cost QRAM/QRAG to the reduction requires the
inner security assumption to use that stronger model too.

### G-P1-C: a lower bound in the fixed-interface circuit model

**Model.** The simulator is online and black-box: it receives only each oracle
query/answer register and has private memory. Call j is implemented by a fixed
circuit U_j of one- and two-qubit gates, chosen independently of the query value,
private random data and the adversary's code. It may use arbitrary encodings,
ancillas, entanglement and query-number-dependent preprocessing; count all gates
between one returned answer and the next. All data-dependent controls are
represented as circuit gates. No unit-cost QRAM, uncharged classical memory
lookups/feedback, data-dependent circuit descriptions, or access to the
adversary's saved answers is supplied. The answer is returned on a fixed wire.
This is the coherent circuit implementation of the universal compressed-oracle
interface, not a lower bound on every conceivable security reduction.

**Proposition G-P1-C [written proof; not a fully formalized quantum theorem].**
Let q = 2r and let the oracle domain contain r distinct inputs. Any such
simulator perfectly reproducing a random function for every q-query adversary
uses at least `r(r-1)` two-qubit gates in its last r calls. Therefore its total
ordinary gate count is Ω(q²), even for one-bit outputs. For a simulator whose
complete output distributions are within statistical distance δ < 1/4 for
every such adversary, the bound becomes

```
r * (r * (1 - h_2(2*delta)) - 1),
```

where `h_2` is binary entropy. In particular a fixed sufficiently small δ still
gives Ω(q²). A trace-distance guarantee on the joint interaction implies the
statistical-distance premise used here.

**Proof.**

1. The adversary first queries fixed distinct inputs x_1,...,x_r with blank
   answer registers and saves their first output bits Y_1,...,Y_r in its private
   memory. In the ideal experiment Y is uniformly distributed on {0,1}^r.
   In subsequent calls it uses a fresh blank answer register. Fix any later
   call j, after a fixed sequence of repeated queries to x_1. Just before this
   call, condition the simulator's private state on the initial saved string Y.
   Write that conditional state as rho_Y. It is independent of the as-yet
   unchosen next index i. Tracing out other adversary registers is harmless.

2. Run U_j backwards from its designated output bit, collecting the input
   wires in its causal cone. A one-qubit gate adds no wire; a two-qubit gate
   intersecting the cone adds at most one. Thus a circuit with g_j two-qubit
   gates has at most g_j+1 input wires in this cone. Let C_j be the subset of
   simulator memory wires in it. The reduced state sigma_Y on C_j determines
   the output statistics for every address x_i: prepare that address and the
   blank answer locally. Operations outside the cone cannot signal to the
   output, including when the memory is entangled. Crucially C_j is the same
   subset for every i because the circuit is fixed.

3. In the exact case, measuring that output recovers Y_i with certainty for
   every Y and i. Hence Y -> sigma_Y is a perfect quantum random-access code
   for r independent bits. The perfect case of Nayak's random-access-code bound
   gives |C_j| >= r. Equivalently, states for two different Y must have
   orthogonal supports, since some decoder distinguishes a differing bit
   perfectly; the encoding space consequently has dimension at least 2^r.
   Therefore g_j >= r-1. This argument applies to every j = r+1,...,2r,
   using the same fixed prefix and fixed repeated-query continuation. Summing
   proves the exact claim.

4. For the approximate case, the simulated prefix distribution mu of Y is
   within δ of uniform. For each i, the test that the next answer differs from
   saved Y_i has probability at most δ under mu. Reweighting to uniform adds
   at most δ, since the conditional error is a function into [0,1]. Define
   rho_Y arbitrarily on zero-probability strings. The resulting random-access
   code has uniform-average bit error at most 2δ for each index. The average-
   error form of the same information bound gives
   `|C_j| >= r*(1-h_2(2δ))`. To see this form directly, for uniform independent
   bits, the chain rule and strong subadditivity give
   `I(Y:C_j) >= sum_i I(Y_i:C_j)`; data processing and binary Fano bound each
   term below by `1-h_2(error_i)`, while `I(Y:C_j) <= |C_j|` for a classical-
   quantum encoding. Concavity of binary entropy gives the displayed bound.
   Repeating the gate-cone count and summing proves the approximate claim. ∎

The information-theoretic ingredient is
[Nayak, Theorem 2.3](https://arxiv.org/pdf/quant-ph/9904093).
The application to this online simulator and its causal cones is the argument
above, not a claim that Nayak states G-P1-C. `Qrom/QueryCost.lean` checks only
the finite cone-cardinality induction and the conditional gate-count inference;
it does not formalize quantum causality, trace distance or the information bound.
Independent review of the full model-to-lower-bound argument remains necessary.

**Output width and the headline time cap.** For an m-bit output, keep all
rm independent prefix bits and take the union of the backward cones of the m
fixed answer wires. Its input size is at most g_j+m. A decoder can select any
of the m returned bits after choosing any of the r addresses, so the perfect
random-access-code bound gives `g_j >= m(r-1)`. The total is at least
`m*r*(r-1)`; with statistical error δ the bound is
`r*(rm*(1-h_2(2δ))-m)` by the same proof. For q=2^64 and m=336, the exact
lower bound is `336*2^63*(2^63-1) > 2^128` gates. The last inequality and the
multi-output cone count are checked in `Qrom.QueryCost`. Thus the universal
exact circuit simulator alone exceeds the proposed 2^128-gate reduction budget;
this says nothing by itself about an attack on the inner system. It also does
not price a QRAM or parallel-depth resource model.

**Scope checks.** Arbitrary preprocessing and encodings do not evade this
argument if all information about Y remains in private qubits and every call
uses the stated fixed circuit interface. Measuring Y into an uncharged classical
controller and compiling a different circuit per Y leaves this model. So does
letting the simulator read the adversary's saved Y. A QRAM lookup is a many-wire
primitive and is likewise outside the two-qubit-gate accounting. A reduction
that inspects or recompiles the adversary, a computational rather than statistical
simulation, or a different time/memory model is not excluded by G-P1-C.

**Verdict.** G-P1 is negative for the universal fixed-interface ordinary-circuit
simulator specified above, subject to review of this written proof. The broader
question under other computation models remains open here. A quasi-linear QRAM
route would require an explicit stronger-model inner assumption and a coherent
dictionary proof; it cannot be used as an ordinary-gate result. No security
headline is upgraded on the strength of this cost investigation alone.

## 7. Consequences for the paper and endpoint

* Keep outer-layer security and recursive semantic security as distinct claims.
  The repaired abstract QROM inequality is proved; the actual family premises
  remain open. Do not label the latter fully proved by citing the former.
* Theorem O supports a **conditional** query-only obstruction. Its hypotheses
  must remain visible. It does not establish literal concrete-SHA/independent-RO
  consistency under a runtime cap, nor the necessity of that particular A-IC.
* A-IC(τ) remains a proposed research endpoint requiring a coherent game. G-P1
  may make a different, explicit inner-system assumption usable; it cannot
  repair an inconsistent oracle-identification assumption by itself.
* R5 (`D3_WASM_REQUIREMENTS.md` §2.5) ships capped D3 without composition.
  The recursive assumption is not a premise of that admission path. This
  research tail and its 293,077-byte measurement are separate from deployment.
* U-7 remains SHA-384 throughout. No lattice or algebraic-hash wrapper is funded
  by this investigation; relaxing U-7 would be a separate user decision.

## References
BCG24 = Barbara–Chiesa–Guan, ePrint 2024/728 (TCC 2025), Defs 3.5, 3.13, 3.14; Thms 4.1, 5.1, 6.1;
§2.4. CGSY24 = Chiesa–Guan–Samocha–Yogev, ePrint 2023/1646 (TCC 2024), Def 3.6, Thm 5.1,
Remark 5.2, §2.3, §6.3, Thm 6.5. CCGOS23 = Chen–Chiesa–Gur–O'Connor–Spooner, ePrint 2023/587
(Eurocrypt 2023), Def 4.1, Thm 8.1, Thm 9.4. Arnon–Yogev, ePrint 2025/329, Defs 4.1–4.2, Thm 5.6.
GW11 = Gentry–Wichs, ePrint 2010/610, Thm 5.1. Zha19 = Zhandry, ePrint 2018/276. PROOF.md
references for the rest.
