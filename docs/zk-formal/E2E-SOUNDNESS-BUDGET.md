# E2E soundness-error budget for `BadEvents` (M11d item 4)

Date: 2026-11-03. Lane E (Lean join). Document only: no Lean or code change.

`zk-formal/ZkFormal/PQ/E2EAgg.lean:124-144` defines the backend's bad events over the transcript of
one final proof:

* `hashColl`
* `whirBad`
* `gkrBad`
* `rangeColl`

`e2e_sound_of_agg` (same file, end of §"backend") concludes `E2EStmt s ∨ BE.Any`. The soundness
error of the whole system is therefore `Pr[BE.Any]` for the adversary class of the contract. This
note computes that probability against the 128-bit target, at the parameters pinned today.

**Tags.**
* **[R]** cited from a repo file (path:line or key).
* **[C]** computed here; the arithmetic is shown.
* **[L]** standard literature (references in §8).

All logarithms are base 2. "b bits" means an error of 2^−b.

---

## 0. Bottom line

The adversary budget is **Q = 2^64 quantum (or classical) SHA-384 queries** [R: U-6,
`docs/zk-formal/V3-D3A-STUDY.md:45`]. Every pinned vk is at **ε_rbr ≤ 2^−268.0** per
round-by-round move.

**Accounting for one database: all proofs of the tree are extracted against one oracle
database (§5.1).**

| model | hashColl (+ rangeColl) | whirBad | gkrBad | **total** | bits |
|---|---:|---:|---:|---:|---:|
| classical ROM, BCS: Q·ε_rbr; collisions Q²/2^(n+1) | 2^−209 | 2^−204.0 | 2^−215.2 | **2^−203.95** | **≈ 204** |
| QROM, CMS19 shape: Q²·ε_rbr; collisions Q³/2^n; constants = 1 | 2^−144 | 2^−140.0 | 2^−151.2 | **2^−139.9** | **≈ 140** |
| QROM, repo's historical constants (`final-soundness/calc/bound.out`) | – | – | – | 2^−134.69 | ≈ 134.7 (withdrawn as a theorem, see §7) |

**Per-proof union over the tree (§5.2).** This is conservative. Each proof's extraction error is
charged separately with the full Q; hash collisions are charged once.

| deployment | proofs N | ROM bits | QROM bits (const 1) | QROM bits (historical consts) |
|---|---:|---:|---:|---:|
| D0a linear chain run on 2026-10-31 (base + L1–L5 + FINAL) | 7 | 201.2 | 137.2 | 131.9 |
| 1 Pgas design point: 137 leaves, fan-in 8, depth 3, plus wrap | 160 | 196.7 | 132.7 | 127.4 |
| harness ceiling: fan-in 8, depth 6, plus wrap | 299,594 ≈ 2^18.19 | 185.8 | **121.8** | **116.5** |

**Verdict.**

* **Dominant term: `whirBad`**, specifically the WHIR shift-query move with grinding. The schedules
  are designed to put it at exactly the 268-bit target.
* **Classical ROM: 128 bits holds** with about 76 bits of margin, under every accounting.
* **QROM, one-database accounting: 128 bits holds** on parameters, with about 12 bits of margin at
  constants 1 and about 6.7 bits at the historical constants.
  * This rests on an uninstantiated family-QROM theorem (`final-soundness/GAPS.md` S-19).
  * It also rests on the O-2 first-order (beyond-Johnson, Lean-proven, unrefereed) proximity
    certificates, not on the plain Johnson bound.
* **QROM, per-proof union:**
  * 128 bits holds for the 7-proof chain.
  * It holds for the 160-proof design only at constants 1 (127.4 bits at the historical
    constants).
  * It **fails** for a depth-6, fan-in-8 tree, by 6.2 bits (constants 1) or 11.5 bits
    (historical constants).
  * The fix is either the one-database theorem, or a per-round target of ≥ 274.2 bits
    (constants 1; ≈ 280 with the historical constants) for every layer in a tree that deep.
* **Parameters that are short or unpinned:**
  1. **The ZK wrap has no pinned parameters at 268 bits.** The HVZK-WHIR sweep used a Plonky3
     `security_level` of 128 (`research/near-compression/e2e/ZK-ARGUMENT.md:66-79`). A wrap built
     at a 128-bit rbr target would give about 2^0 in the QROM (Q²·2^−128) and 2^−64 in the ROM.
     The wrap must be held to the same 268-bit rbr target as every other vk.
  2. **The Lean docstring of `hashColl` states the classical bound Q²/2^337.** The 128-bit QROM
     claim needs the cubic bound Q³/2^336 = 2^−144. The docstring now says so (fixed in M11d).
  3. **M8 production nodes are not pinned yet** ("rate 1/4–1/16, fan-in 8, ≤ 3 levels",
     `E2E-GENERAL-CHUNK-PLAN.md:423`). They must keep the 268-bit rbr target with a vk-bound O-2
     table, as the measured depth-2/3 nodes do.

---

## 1. Pinned parameters (current, not superseded)

### 1.1 Common to every vk

| parameter | value | source |
|---|---|---|
| field | BabyBear p = 15·2^27 + 1; challenge field Ext12 = F_p[X]/(X^12 − 31), \|F\| = p^12 = **2^370.88** (not 2^372) | [R] `research/near-compression/x15-domains/SOUNDNESS.md:15`; `final-soundness/PROOF.md` §1.1 |
| hash | SHA-384 throughout; framed `H(tag, parts)`; prefix `nearproof-sha384-ext12-v5-w42-c1` | [R] U-7 (`V3-D3A-STUDY.md:46`); `PROOF.md` §1.3 |
| digest width | Merkle leaves, nodes, vk pre-hash, tag-9 range digest and boundary digests truncated to **42 B = 336 bits**; the transcript (FS) state is **48 B = 384 bits**, never truncated | [R] U-10 (`V3-D3A-STUDY.md:49`); `PROOF.md` §1.3 and Lemma 1.1; tag-9 truncation: `native/recursion/patches/openvm-recursion-agg.patch:16-17, 121`; boundary `bdigest` 42 B: `docs/logs/e2e-lean-m11b-2026-11-03.md:94` |
| oracle split | narrow-leaf (tags 0, 6), narrow-node (92-B node messages), wide (tags 2, 3, 4, 5, 7) are disjoint and prefix-free, so they act as independent ROs: 336-bit narrow, 384-bit wide | [R] `PROOF.md` Lemma 1.1 (GAPS S-1) |
| per-round rbr target | **268 bits = 236 query bits + z = 32 PoW bits** (query-phase grinding, 2-element PoW witness) | [R] U-10; `PROOF.md` §1.1 (`protocol_security_level = security_bits − query_phase_pow_bits`) |
| other grinding | LogUp PoW bits = 0; folding/μ PoW not used | [R] `native/recursion/levers-check/main.rs:89` (`params.logup.pow_bits=0`) |
| WHIR domains | ×15 domains, n = 15·2^(log h + b), keep-domain, exactly uniform query sampler (rejects x = p − 1) | [R] `x15-domains/SOUNDNESS.md`; `PROOF.md` Lemma 4.1 |
| proximity basis | U-13: DKT26 line MCA at the Johnson radius √ρ(1 + 1/128), backend `ListDecoding` m = 64 (**O-1**), and first-order beyond-Johnson certificates with a per-round agreement table bound into the vk (**O-2**) | [R] U-13 (`V3-D3A-STUDY.md:52`); `FAITHFUL.md` §R.7 "O-2 agreement table" |
| transcript | T\* (counter-mode squeeze; PoW on block B₁), WHIR-Y | [R] U-10, U-11; `PROOF.md` §6.2 |

### 1.2 Per vk (WHIR schedule and calculator bits)

The calculator is stark-backend `SoundnessCalculator::calculate_from_vk`, printed by
`nearproof-chunk-e2e soundness <vk>` (`native/pq-chunk-e2e/src/main.rs:684-703`).

| vk (role) | l_skip, n_stack, log_blowup, k₁/k | WHIR queries per round | calculator bits: total / WHIR query / proximity / LogUp / GKR sumcheck | source |
|---|---|---|---|---|
| base (D0a app leaf) | –, 18, 7, –/4 | [44, 35, 27, 23] | 269.6 / 269.6 / 280.1 / 321.4 / 369.3 | [R] `research/near-compression/e2e/results/soundness-d2_05-h10042-s3.txt:1` |
| L1–L5 (inner NV) | –, 19, 6, –/4 | [48, 38, 29, 23] | 269.2 / 269.2 / 281.6 / 321.9 / 369.3 | same file, lines 2-3 |
| FINAL / aggregation node | 2, 19, 6, 1/4 | [46, 41, 31, 25], all rounds `first_order=true` | 268.2 / 268.2 / 283.1 / 321.9 / 369.3 | same file, line 4; `docs/logs/pq-agg-depth2-legal-2026-10-24.md:34-37` |
| E2E segment leaves (WASM base, STATE T2) | per template | – | 268.2 (reported) | [R] `E2E-GENERAL-CHUNK-PLAN.md:470, 492, 565, 596, 634` |
| ZK wrap | **not pinned** (not built) | – | – | [R] `E2E-GENERAL-CHUNK-PLAN.md:108`; `e2e/ZK-ARGUMENT.md:66-79` |

**Proof-level analysis shapes.** `research/near-compression/final-soundness/calc/bound.out` uses
the NV fixed-point model shapes:

| shape | queries | rbr error |
|---|---|---|
| final (b = 8) | [38, 35, 29, 24] | 2^−268.01 |
| inner (b = 6) | [45, 41, 31, 24] | 2^−268.02 |
| base stress (W = 601) | [48, 44, 32, 25] | 2^−268.06 |

These are model shapes, not the deployed vks above. They give the same per-round target. The
proof-level per-move terms (OOD, μ, fold, LogUp *with* the list factor ℓ₀) used in §3 come from
this file. GAPS S-24 and S-27 say the certificates must be regenerated for the final pinned shape.

**Which regime the schedules assume [C].** Under O-1 alone (Johnson, a = √ρ(1 + 1/128)), the
query bits per round are t·(−log a). Rates per round are ρ_i = 2^−(lir_i)/15, with
lir = b, b + k₁, b + k₁ + k, ….

* FINAL [46, 41, 31, 25] at b = 6, k₁ = 1, k = 4: ρ = 2^−9.91, 2^−10.91, 2^−14.91, 2^−18.91, which
  gives 227.3 / 223.1 / 230.7 / 236.1 bits. Three rounds are below 236.
* L1–L5 [48, 38, 29, 23]: 237.2 / 206.8 / 215.8 / 217.2.

So the deployed schedules **rely on O-2** (first-order, beyond-Johnson agreement). The aggregation
log says so explicitly (`first_order=true`). The phrase "proven Johnson-regime list decoding m = 64"
in `e2e/README.md:96` describes O-1, which is used only where it suffices. Both O-1 and O-2 are
proven theorems: DKT26, Lean-checked in ArkLib with the 36 certificates kernel-checked (U-13,
GAPS S-26/S-27). The paper is unrefereed, and the DKT26 → WHIR transfer is open (S-28).

For comparison [C]:
* Under the **conjectured up-to-capacity** regime (per-query error ≈ ρ), the same FINAL schedule
  would give 455.7 / 447.2 / 462.1 / 472.7 query bits.
* Under **unique decoding** ((1 + ρ)/2 per query, ≈ 0.9985 bits), it would give ≈ 46 bits.

The parameters assume **no** conjecture beyond DKT26.

### 1.3 Recursion structure

| item | value | source |
|---|---|---|
| node fan-in | 8 (2–8 identical or mixed children measured) | [R] `E2E-GENERAL-CHUNK-PLAN.md:18, 106, 241` |
| depth | ≤ 3 levels targeted (M8); the harness admits depth 1..=6 (`AGG_DEPTH`) | [R] plan:423; `openvm-recursion-agg.patch:845`; `prover-budget/README.md:244` |
| leaves at 1 Pgas | 137 segments of 2^24 rows, fan-in 8, depth 3 | [R] `research/near-compression/prover-budget/README.md:140-141` |
| wrap | one ZK wrap (HVZK-WHIR) over the root | [R] plan:244-253 |
| D0a chain measured | base + L1..L5 + FINAL = 7 proofs | [R] `e2e/README.md:113-114` |

Proof counts [C]:
* Design point: 137 leaves; ⌈137/8⌉ = 18, ⌈18/8⌉ = 3, then 1, so 22 nodes; plus 1 wrap. Total
  **160** (2^7.32).
* Depth-6, fan-in-8 ceiling: 8^6 = 262,144 leaves; Σ_{i<6} 8^i = 37,449 nodes; plus 1 wrap. Total
  **299,594** (2^18.19).

---

## 2. Event decomposition and the union bound

`BadEvents.Any := hashColl ∨ whirBad ∨ gkrBad ∨ rangeColl` (`E2EAgg.lean:144`), so

```
Pr[BE.Any] ≤ Pr[hashColl] + Pr[whirBad] + Pr[gkrBad] + Pr[rangeColl].
```

**`rangeColl` folds into `hashColl`.** The tag-9 range digest
`D = SHA-384(prefix, tag 9, [n_ctx, n_state, ctx.., a, e, s_a.., s_e..])` is truncated to 42 B
(`openvm-recursion-agg.patch:16-17`). A `rangeColl` (two distinct range statements, equal
digest) is a 336-bit collision of the RO restricted to the tag-9 framed domain. Those queries are
among the adversary's Q. So `rangeColl ⊆ hashColl`, provided `hashColl` is read as "any collision
among the adversary's queries in any 336-bit domain". It is counted **once**, inside the hashColl
term below.

The same holds for the boundary-digest and `view` collisions that `SegSound` (ob2 of
`e2e_sound_of_agg`) pushes into `BE.Any`: `bdigest` is 42-B SHA-384 (M11b/M11c). In the recursive
setting these are SHA-384 evaluations inside circuits, so §7 A3 applies.

### 2.1 `hashColl`: collision bounds [L + C]

| model | bound | n = 336 (42 B) | n = 384 (48 B) |
|---|---|---:|---:|
| classical ROM (birthday) | Q(Q−1)/2^(n+1) ≤ Q²/2^(n+1) | 2^(128−337) = **2^−209** | 2^(128−385) = **2^−257** |
| QROM (BHT upper attack, tight per Zhandry) | c·Q³/2^n, c a small constant | 2^(192−336) = **2^−144** (c = 1); 2^−140 at c = 2^4 | 2^(192−384) = **2^−192** |

**The 128-bit claim needs the QROM row at n = 336: 2^−144**, which leaves 16 bits of margin. The
classical Q²/2^337 written in the `hashColl` docstring is not enough to claim post-quantum
security. U-10 itself records the cubic bound t³/2^336 ≤ 2^−144 (`V3-D3A-STUDY.md:49`).

Mixing widths: the narrow (336-bit) and wide (384-bit) domains are independent ROs (Lemma 1.1).
Charging all Q queries at n = 336 is an upper bound.

### 2.2 Fiat–Shamir: from rbr soundness to the transcript events [L]

`whirBad` and `gkrBad` are the BCS-compiled form of "some verifier challenge lands in its
round-by-round bad set".

* **Classical ROM** (BCS16; rbr soundness, Canetti et al. / Holmgren): Pr ≤ Q·ε_rbr. Each query
  is one attempt at one move.
* **QROM** (Chiesa–Manohar–Spooner 2019, Thm 8.6): an rbr-sound IOP compiled by BCS is sound
  with error O(Q²·ε_rbr + Q³/2^λ). The quadratic loss is Grover search over challenges. Generic
  multi-round measure-and-reprogram (Don–Fehr–Majenz 2020) loses (2Q + 1)^(2r) and is unusable
  here (`V3-D3A-STUDY.md` §11.2).

  The repo's own route (`PROOF.md` §6.4) is a conditional compressed-oracle operator bound
  p ≤ (Q·g + √(ℓ_V/2^336))², with g² ≈ max-move error. It gives Q²·ε_rbr to leading order. Its
  concrete instantiation is open (S-19).
* **Grinding.** z = 32 PoW bits on the first block of the query challenge (T\*-2) multiply that
  move's rbr error by 2^−z (`PROOF.md` Lemma 5.1). In the ROM, z bits buy z bits. In the QROM,
  the Q²·(2^−z·ε) form is Grover-tight: z bits of classical work buy z/2 "Grover bits", which the
  Q² charge already accounts for. The 268 = 236 + 32 accounting is therefore valid in both models,
  but only under T\* (GAPS S-15; the pre-T\* code did not compose).

---

## 3. Per-component numbers

### 3.1 `whirBad` (ε_WHIR per round, rbr)

The WHIR moves are listed in `PROOF.md` Lemmas 4.2–4.6 and 5.1, evaluated in
`final-soundness/calc/bound.out` [R].

| move | formula | worst value |
|---|---|---:|
| shift queries + PoW | 2^−z·a_i^(t_i) | **2^−268.01** (final r1); inner 2^−268.02; base 2^−268.06 |
| OOD (1 sample) | ℓ_i²/2·(2^(m_i)/\|F\|) | 2^−271.91 (final r1, ℓ = 2^41.0) |
| fold MCA (DKT26) | E/\|F\| + 3ℓ_i/\|F\| | 2^−280.74 |
| μ batching (W stacked columns) | E_(W−1)/\|F\| + ℓ₀(W−1)/\|F\| | 2^−282.1 / 2^−283.0 / 2^−287.5 |
| γ combination | ℓ_(i+1)(t_i + 1)/\|F\| | ≤ 2^−320 (calculator `whir_gamma` 347.8–348.7) |

Deployed calculator values per vk (§1.2): query 268.2–269.6, proximity/fold 280.1–283.1, OOD 329.0,
μ 283.6–291.1 bits. The calculator ignores the list factor in OOD and digest terms (GAPS G-12), so
`bound.py`'s 271.9-bit OOD figure is the one to use.

**ε_WHIR,rbr = 2^−268.0** (all vks). This is the system-wide max.

### 3.2 `gkrBad`: LogUp α/β, GKR sumcheck, Schwartz–Zippel

* **LogUp fractional sum (α, β), SZ** [R `FAITHFUL.md` §2(f), lines 1264-1270]:
  ε_LogUp ≤ ℓ_msg·N²/(2|F|) + 2N/|F|. Here N = Σ interactions × height is the number of
  fractional terms and ℓ_msg the maximum message length. The pinned figures, re-derived [C]:

  | NV head | ℓ_msg | N | ε_LogUp | source |
  |---|---:|---:|---:|---|
  | 3c9d479ab | 15 | 2^25.05 | 2^(3.91 + 50.10 − 1 − 370.88) = **2^−317.9** | §2(f) |
  | R.7 (49 interactions per row) | 20 | 2^24.98 | 2^−317.6 | §R.7 |
  | X.5 | 22 | – | 2^−316.6 | §X.5 |
  | Z.6 (current head; NvAir at 2^19) | – | 2^25.36 | 2^−316.7 | line 2251 |

  The calculator's per-vk `logup` (321.4–321.9) uses the backend's own count.

  **In the rbr list form**, every PIOP move is charged ×ℓ₀, the initial WHIR list size, which is up
  to 2^40.0 under O-2 (`PROOF.md` Thm 5.2). That gives **2^−279.16 (final) / 2^−279.64 (inner) /
  2^−293.06 (base)** [R bound.out]. These are the values used below. They are the binding PIOP
  term.
* **GKR sumcheck** (fractional-sum GKR, Papini–Haböck 2023; Gruen rounds): per round
  deg/|F| = 3/2^370.88 = **2^−369.30** [C], matching the calculator's `gkr_sumcheck=369.3`.
  Batching is 1/|F| = 2^−370.9. As an rbr error the per-round value is what matters. For
  reference, a plain union over all rounds, at about n(n+1)/2 = 325 rounds for n ≈ 25 layers,
  gives 2^(log 975 − 370.88) = 2^−361.0 [C]. Times ℓ₀ ≤ 2^40 in list form this is ≤ 2^−329.
* **Zerocheck / constraint batching / stacking**: 355.0 / 349.4–350.8 / 346.8–351.5 bits
  (calculator), ≥ 2^−306 with ℓ₀ [C: 346.8 − 40.0].

**ε_gkr,rbr := max = 2^−279.2** (LogUp α/β with list factor, final layer).

### 3.3 Range statement and tape binding

* `rangeColl`: §2.1, folded into hashColl.
* The TAPE evaluation binding (`e2e/README.md:79-81`) is an SZ term (l_skip + n_stack)/|EF| ≈
  2^−367 per transcript. That is ≤ 2^−303 at 2^64 queries classically and ≤ 2^−239 at Q² in the
  QROM [C]. It is negligible.

---

## 4. Totals for one proof / one database

Q = 2^64. All terms are the worst over every vk family, so this is also the total for a whole tree
when one extraction game covers all proofs (§5.1).

| term | ROM | QROM |
|---|---|---|
| hashColl (incl. rangeColl, boundary digests), n = 336 | Q²/2^337 = 2^−209 | Q³/2^336 = 2^−144 |
| whirBad | Q·ε = 2^(64 − 268.0) = 2^−204.0 | Q²·ε = 2^(128 − 268.0) = 2^−140.0 |
| gkrBad | 2^(64 − 279.2) = 2^−215.2 | 2^(128 − 279.2) = 2^−151.2 |
| **sum** | 2^−204.0 + 2^−209 + 2^−215.2 = **2^−203.95** | 2^−140.0 + 2^−144 + 2^−151.2 = **2^−139.91** |
| **bits** | **203.9** | **139.9** |

The QROM figure carries hidden constants:
* At c_coll = 16 the hash term becomes 2^−140 and the total 2^−139.0.
* `bound.out` reports the CMS19-constant cross-check as 2^−137.10 and the CDHZ26 cross-check as
  2^−130.22.
* With its historical family constants (×10 on g², t → 2t simulation), the total is 2^−134.69.

So the parameter-level QROM claim is **≈ 135–140 bits**, depending on constants that are not yet
established (S-19).

---

## 5. Whole aggregation tree

### 5.1 One database (intended)

All leaves, nodes and the wrap are produced against the same SHA-384 oracle. The extractor
(`ExtractWG`/`ExtractW`) is straight-line: it reads the committed traces off the adversary's query
database, with no rewinding. One extraction run therefore covers every proof of the tree.

* **Classical ROM.** "Some query hits some move's bad set" is bounded by Q·max ε over all families.
  The number of proofs does not appear; the adversary's Q, which must include the honest-prover
  hashing of every proof in the tree, is the resource. The result is §4: **203.9 bits**.
* **QROM.** The family operator bound (`PROOF.md` §6.4: one potential, per-query crossing norm g
  = max over moves, since a query input fixes one transcript prefix) gives the same form,
  (Q·g + √(ℓ_V/2^336))². The result is **139.9 bits** at constants 1, or 134.7 at the historical
  constants. That theorem is **not instantiated** (S-19). Recursion adds the extraction chain
  (one level per tree level). In a straight-line, one-database argument this costs no extra
  probability, but it needs NV-faithfulness at every level and the recursive hash model (§7 A3).

Q also has to be checked against the honest work [C]: a 299,594-proof tree at an assumed (order-of-magnitude, not measured) 2^20
compressions per proof is about 2^38.2 SHA-384 calls. That is far below Q = 2^64, so the budget is
not consumed by the honest prover.

### 5.2 Per-proof union (conservative fallback)

If only a per-proof theorem is available, so that each proof's extraction error is bounded with the
full Q, the extraction terms are multiplied by N. Hash collisions are one global event and are
charged once.

```
QROM:  Pr ≤ Q³/2^336 + N·(Q²·ε_WHIR + Q²·ε_gkr) = 2^−144 + N·(2^−140.0 + 2^−151.2)
ROM:   Pr ≤ Q²/2^337 + N·(Q·ε_WHIR + Q·ε_gkr)   = 2^−209 + N·(2^−204.0 + 2^−215.2)
```

| N | log N | ROM bits | QROM bits | QROM, historical consts (134.69 − log N) |
|---:|---:|---:|---:|---:|
| 7 (D0a chain) | 2.81 | 201.2 | **137.2** | 131.9 (the repo's "union over 7 layers") |
| 160 (1 Pgas design) | 7.32 | 196.7 | **132.7** | 127.4 ✗ |
| 299,594 (depth 6, fan-in 8) | 18.19 | 185.8 | **121.8 ✗** | 116.5 ✗ |

Holding 128 QROM bits under the per-proof union at N = 2^18.19 requires
ε_rbr ≤ 2^−(128 + 128 + 18.19) = **2^−274.2** at constants 1, which is about 6.2 bits more per
round. With the historical ~5.3-bit constant loss, the requirement is about 2^−280. There are two
ways to get there:
* raise the query target from 236 to about 242 (≈ 1–2 extra queries per round), or raise z to 38;
* or prove the one-database theorem of §5.1, which removes the log N term.

---

## 6. Verdict against the 128-bit target (U-6: ≤ 2^−128 at ≤ 2^64 quantum queries)

1. **Dominant term:** `whirBad`, the WHIR shift-query move with grinding (2^−268.0 per move,
   2^−140 after the Q² QROM loss). The next terms are hashColl (2^−144 QROM) and LogUp α/β with
   the list factor (2^−151.2).
2. **Classical ROM:** about 204 bits (one database), and ≥ 185.8 bits even with the per-proof
   union at depth 6. **Holds.**
3. **QROM:**
   * About 140 bits at constants 1, or 134.7 at the repo's historical constants, under
     one-database accounting. **Holds on parameters.**
   * This is conditional on S-19 (family-QROM instantiation), S-28 (DKT26 → WHIR transfer) and the
     O-2 certificates being regenerated for the pinned shapes.
   * Under the per-proof union it holds for N ≤ about 2^11.9 at constants 1 (2^6.7 at the
     historical constants). It does **not** hold for a depth-6, fan-in-8 tree.
4. **Under which proximity result:** DKT26 O-1 (Johnson) plus O-2 (first-order beyond-Johnson),
   both Lean-proven, with the paper unrefereed. No up-to-capacity list-decoding conjecture is
   used. Pure Johnson (O-1) would leave the deployed schedules 0–29 bits short per round (§1.2).
   Under capacity conjectures they would have about 200 bits of slack.
5. **Short or unpinned parameters:**
   * **ZK wrap:** must be pinned at a 268-bit rbr target with z = 32 under T\*. The measured
     HVZK-WHIR sweep used `security_level` 128 and leaves its mask spot checks ungrounded.
     `ZK-ARGUMENT.md` already lists re-deriving the 268-bit budget for the masked protocol as an
     open item (line 111).
   * **Depth > 3 trees:** either prove §5.1 or raise the per-round target to ≥ 274.2 bits.
   * **`hashColl` docstring:** replace Q²/2^337 with the QROM Q³/2^336 (= 2^−144 at Q = 2^64).
   * **`hashColl` scope:** say explicitly that it covers rangeColl and boundary-digest
     collisions, or keep rangeColl separate but count it once.
   * **M8 node parameters (rate 1/4–1/16):** not pinned; they need their own O-2 table.

---

## 7. Open assumptions this calculation relies on

* **A1. SHA-384 is a (quantum) random oracle**, with the framing split of Lemma 1.1 (narrow
  336-bit and wide 384-bit domains independent). This is a standard idealisation (U-6/U-7), not a
  theorem about SHA-384.
* **A2. The 42-B truncation.**
  * A truncation of a RO is a RO, so the 336-bit QROM collision bound applies; it gives 16 bits of
    margin at Q = 2^64.
  * The generic quantum collision attack (BHT) costs 2^112 queries at n = 336. This is safe only
    because the contract bounds queries to 2^64. A contract of "2^128 quantum time and queries"
    would break 42-B digests.
  * WHIR-Y is not needed at 336 bits (`PROOF.md` Lemma 4.6 remark).
* **A3. Recursive in-circuit hashing.** Leaves, nodes and the wrap verify children with SHA-384
  computed *inside* the circuit, and boundary/range digests are in-circuit. The former A-IC
  assumption (U-11) is withdrawn as a justification (`PROOF.md` §7.1). U-12 restricts the claim to
  adversaries with ≤ 2^64 queries and τ ≤ 2^128 time. A concrete-hash computational assumption or
  a new reduction (§7.2–7.3, S-20/S-23/S-25) is required. **No recursive security number is
  currently established.** The figures above are parameter-level budgets for that eventual
  theorem.
* **A4. Straight-line extraction.** `ExtractWG`/`ExtractW` must be straight-line (database
  reading, no rewinding). Rewinding extractors do not carry over to the QROM at these losses, and
  a rewinding loss compounds per recursion level. The compressed-oracle route of `PROOF.md` §6.4
  is straight-line but uninstantiated (S-19). The simulation t → 2t of the counter-mode oracle
  (Lemma 6.3) needs a sampler cap that the implementation lacks (S-17).
* **A5. Round-by-round knowledge soundness of one SWIRL layer**, `PROOF.md` Thm 5.2 (2^−268.01),
  which is conditional on S-28.
* **A6. Proximity results.** DKT26 Thm 5.12, Prop 5.10, Lemmas 5.6/5.11 and Cors 7.3/7.5/7.7/7.8
  (Lean-checked, paper unrefereed). Three further inputs:
  * the ×15-domain edit of WHIR Thm 5.2 (`x15-domains/SOUNDNESS.md`, unreviewed, S-13);
  * the Puškin 2026 corrected WHIR Thm 5.3;
  * O-2 certificates regenerated for each pinned shape and bound into the vk.
* **A7. T\* transcript** as implemented (counter-mode squeeze, PoW on B₁). The grinding credit
  (Lemma 5.1) holds only under T\*-2 (S-15).
* **A8. NV-faithfulness and segment soundness.** `NvFaithful` for the node and the wrap (5 of 6
  sub-obligations open), `LeafHolds`, and `SegSound`/`WitnessExtraction` are deterministic
  obligations. They contribute no probability but are premises of `e2e_sound_of_agg`.
* **A9. Q = 2^64** includes every hash the adversary evaluates: honest proving of the tree,
  grinding and attack queries. τ ≤ 2^128 time (U-12).

---

## 8. References

* [ACFY24] Arnon, Chiesa, Fenzi, Yogev. WHIR: Reed–Solomon proximity testing with super-fast
  verification. ePrint 2024/1586 (Eurocrypt 2025). Thm 5.2, Construction 5.1.
* [Pus26] Puškin. An analysis of the WHIR IOPP. MSc thesis, Tartu, 2026. Thm 5.3.
* [DKT26] Dao, Kominers, Thaler. Reed–Solomon codes beyond Johnson. ePrint 2026/2056.
* [BCS16] Ben-Sasson, Chiesa, Spooner. Interactive oracle proofs. TCC 2016-B.
* [CMS19] Chiesa, Manohar, Spooner. Succinct arguments in the quantum random oracle model. TCC
  2019, ePrint 2019/834. Thm 8.6.
* [DFM20] Don, Fehr, Majenz. The measure-and-reprogram technique 2.0. ePrint 2020/282.
* [BHT98] Brassard, Høyer, Tapp. Quantum cryptanalysis of hash and claw-free functions.
* [Zha15] Zhandry. A note on the quantum collision and set equality problems. QIC 2015,
  arXiv 1312.1027 (Θ(q³/2^n) tight).
* [Zha19] Zhandry. How to record quantum queries. ePrint 2018/276.
* [PH23] Papini, Haböck. Improving logarithmic derivative lookups using GKR. ePrint 2023/1284.
* [Gru24] Gruen. Some improvements for the PIOP for ZeroCheck. ePrint 2024/108.
* Repo:
  * `research/near-compression/final-soundness/{PROOF.md, GAPS.md, calc/bound.out}`
  * `research/near-compression/results/pq-recursion-nv/FAITHFUL.md` §2(f), §R.6–R.7, §X.5, §Z.6
  * `research/near-compression/x15-domains/SOUNDNESS.md`
  * `research/near-compression/e2e/{README.md, ZK-ARGUMENT.md, results/soundness-d2_05-h10042-s3.txt}`
  * `docs/zk-formal/V3-D3A-STUDY.md` §D (U-6, U-7, U-10 – U-13) and §11.2
  * `docs/logs/pq-agg-depth2-legal-2026-10-24.md`
  * `research/near-compression/prover-budget/README.md`
  * `research/near-compression/tail-architecture/OUTER_SECURITY.md`: the lattice (LaBRADOR) tail.
    It is not on the E2E WHIR path and contributes no term here; if adopted, it would add its own
    extraction and quantum Fiat–Shamir terms, which that note says are not yet derived.
