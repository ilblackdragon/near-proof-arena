# Lane `lane/v3-size` — deduplicated proof-size bound (lever (a)): status

Design: `V3-D0-DESIGN.md` §5.3, §13, §13.1, §15. Branch `lane/v3-size` (off `lane/v3-air`).

Everything new is in `zk-formal/ZkFormal/Size/`. No v1 or existing v2 definition or proof is modified.

Rules: no `sorry`, `axiom` or `native_decide` (checked by grep). Every theorem below was checked
with `#print axioms` and uses axioms ⊆ {propext, Classical.choice, Quot.sound}. Evaluations use `decide +kernel`.

## 1. Statements

| deliverable | theorem | file | axioms |
|---|---|---|---|
| 1 | **`Size.multiproof_size_le`**: if `S` is strictly sorted, `S < 2^n` and `\|S\| ≤ s`, then `\|multiproofBytes … o S\| ≤ openSizeD s (shapesOf o)`, where `openSizeD s mats = 4·Σ_{(m,w)} min s 2^m · w + 64·dsum s n` and `dsum s n = Σ_{j<n} min s 2^j`. The stream is the honest prover's, and the deployed reader consumes exactly that stream (`Prover.ev_multiproof`). | `Size/Dedup.lean` | std3 |
| 1 | `upBytes_lengthD` (one sibling plus one row block per **parent**), `levelsBytes_lengthD` (≤ `min s 2^j` parents at depth `j`), `length_le_pow`, `dsum_le_mul` (`dsum s n ≤ s·n`), `openSizeD_le` (`openSizeD ≤ openSize`) | `Size/Dedup.lean` | std3 |
| 1 | **`Size.size32D : SizeStmt32D`**: for a 32-byte hash, the honest proof `proveTree` has at most `sizeBoundD V pr.hdr` bytes. `sizeBoundD` is `sizeBound` with `openSizeD` per oracle. `sizeBoundD_le`: `sizeBoundD ≤ sizeBound`. | `Size/Dedup.lean` | std3 |
| 2 | **`Size.sizeBoundD_le_dedup`**: on every admissible header and for any `prm`, `sizeBoundD (Iop.verifier F K A prm) hdr ≤ sizeMaxDedup A prm` | `Size/Sched.lean` | std3 |
| 2 | **`Size.sizeMaxDedup_le_sched`**: `sizeMaxDedup A prm ≤ sizeMaxSched A prm` (never worse than P1). Via `friDedupMax_le` and the DP comparison `phiG_le_mul` / `phiMaxG_le_mul` | `Size/Sched.lean` | propext, Quot.sound |
| 2 | `go_schedG`: P1's `go_sched` for **any** per-commit cost. Roll-in forced commits are included. `tab_eq_tabG`/`phiMax_eq`: P1's DP is the instance `cost = stepCost B`. | `Size/Sched.lean` | std3 |
| 2 (v2) | **`Size.sizeBoundD_le_dedupP g AP hdr`**: for the v2 verifier `verifierP` at `auxGroup = g`, `sizeBoundD ≤ sizeMaxDedup AP.toAir (pg g)` | `Size/Admission.lean` | std3 |
| 2 (v2) | **`Size.admission_v2_dedup g hg`**, **`Size.np_proverCompleteDedup g hg`**: `V2.PG.Admission.admission_v2` / `np_proverCompleteP` with the size hypothesis on `sizeBoundD` (discharged by `size32D`) | `Size/Admission.lean` | std3 |
| 3 | **`Size.sizeOfWeq prm ts`**: the bound as a function of the table shapes `TShape = (w, aux, quot, fin, maxLog)`. **`sizeMaxDedup_eq_model`**: `sizeMaxDedup A prm = sizeOfWeq prm (A.tables.map (shapeOf prm.auxGroup))`. `sizeMaxSched_eq_model` does the same for P1 (`sizeOfSchedS`). `sizeOfWeq_parts` splits it into prefix, main, aux, quotient and FRI. | `Size/Model.lean` | propext, Quot.sound |
| 3 | `near_sizeMaxDedup(_g2,_g3)`, `near_size_dedup`, `v3_*` (below) | `Size/V3Eval.lean` | propext (std3 for `near_size_dedup`, `v3_bound`) |

`std3` means {propext, Classical.choice, Quot.sound}.

**`sizeBound` versus `sizeBoundD`.** The literal `sizeBound … ≤ sizeMaxDedup …` is false. `Prover.sizeBound` is a *definition* that charges `nq·64·depth` per oracle, i.e. no dedup. So the deduplicated per-header bound is the new `sizeBoundD`:
* `size32D` proves that the honest proof fits it;
* `admission_v2_dedup` consumes it.
`hsize` was only ever used through `size32`, so nothing else changes.

### Why `dsum`

With nq = 216 sorted, deduplicated positions:
* level `j` of the multiproof carries at most `min(216, 2^j)` parents. Each parent has at most one sibling digest of 64 B and one injected row block.
* `dsum 216 26 = 255 + 18·216 = 4,143` digests per depth-26 oracle, against `216·26 = 5,616` before. That is −94,272 B per oracle.
* The same holds for every committed FRI layer. Its depth is `n0 − c − a`. Its rows are `min(216, 2^depth)·32·2^a`, which matters for the last layers (depth ≥ 5).

## 2. Numbers (kernel-checked, `Size/V3Eval.lean`)

### `nearAir` (7 tables)

| `g` | P1/P2 `sizeMaxSched` | **`sizeMaxDedup`** | Δ |
|---|---:|---:|---:|
| 1 (= `Params.default`) | 5,473,967 | **4,134,191** (`near_sizeMaxDedup`, `near_size_dedup`) | −1,339,776 (−24.5 %) |
| 2 | 5,347,055 | **4,007,279** | −1,339,776 |
| 3 | 5,353,423 | **4,013,647** | −1,339,776 |

Of the −1.34 MB:
* −282,816 comes from main/aux/quotient (3 × 94,272);
* −1,056,960 comes from FRI: 2,792,448 → 1,735,488, including the 6 possible roll-in commits.

### Synthetic v3 AIR `V3.v3S g` (23 tables)

The 23 tables:
* **one SHA:** v1 L5 table `Sha.Table.table`, 544 columns, 17 interactions, degree 4 (real table);
* **trie (6):** lane `v3-trie` head `f723a708`, nodeV3 with `UPB`, 186/21; headV3, valV3, walkV3, uniqV3, upsV3 186/15;
* **ChaCha (3):** chachaV3, genV3, shufV3 (real, in tree);
* **scheduler (5):** lane `v3-sched` head `f9bbf2f5` after cuts B and D **and the +20 source map**: `W_eq` 781, not 761;
* **receipt side (6):** lane `v3-rcpt` head `fad713e5`: rcptV3, acctV3, akeyV3, bndV3, srcpV3, sizeV3;
* **v1 `mrk`, `sort`:** real tables at the v3 heights `maxLog` 19 and 18.

**Where the shapes come from.** Shapes `(w, aux, quot, fin, maxLog)` at g = 1, 2, 3 are computed from the tables themselves:
* Tables that live only on other branches were evaluated on an exported snapshot of that branch head. Their totals match the branches' own kernel checks: `weqTrieU` 1201/1081, `weqSched` 781/709, `weqRcpt` 867/795.
* `trie_shapes_check` and `sched_shapes_check` re-derive by kernel every transcribed entry whose table is also in this tree: head, val, walk, uniq, ups, proc, mem, cmp at g = 1, 2, 3.

**Not counted:**
* `qvV3`, the queue parsers (≈ 80–120 `W_eq` ≈ +75–112 KB);
* any later width changes.

| `g` | `W_eq` | P1 model `sizeOfSchedS` | **`sizeOfWeq` (dedup)** | prefix | main | aux | quot | FRI |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 4,434 | 9,729,983 | **7,450,143** | 175,871 | 2,328,544 | 1,511,360 | 748,224 | 2,686,144 |
| 2 | 4,090 | 9,426,335 | **7,146,495** | 169,439 | 2,328,544 | 965,312 | 997,056 | 2,686,144 |
| 3 | 4,146 | 9,473,407 | **7,193,567** | 168,127 | 2,328,544 | 799,424 | 1,211,328 | 2,686,144 |

`v3_bound g AP hA hdr h`: every v2 AIR whose tables have exactly these shapes satisfies `sizeBoundD ≤ sizeOfWeq (pg g) (v3S g)` at every admissible header.

### Margin against 8,388,608 − B

**Hint body `B` (exact, from the decoder).** `B = u32 0 ‖ u32 n ‖ refunds`, with `n ≤ 4481` under A1 (`max_receipts`). By `Receipt.encode` / `pRefund`, the largest refund is a gas refund from a 64-character signer (`signer = receiver`) with a SECP256K1 key:

| field | bytes |
|---|---:|
| `system` | 10 |
| receiver | 4 + 64 |
| `receipt_id` | 32 |
| tag | 1 |
| signer | 4 + 64 |
| key | 1 + 64 |
| `gas_price` | 16 |
| output data receivers | 4 |
| input data ids | 4 |
| action count | 4 |
| action tag | 1 |
| deposit | 16 |
| **total** | **289 B** |

So `B ≤ 8 + 4481·289 = 1,295,017` (`bodyMax_eq`). The design's "≤ 204 B per refund, ≤ 0.91 MB" undercounts:
* gas refunds carry the signer's id (up to 64 B) and its key, which may be SECP256K1 (`receipt.rs:519-537`);
* the design figure fits only `system`/ED25519 balance refunds.

The `split`/`join` framing of `n` is not fixed yet (a few bytes) and is not included.

| `g` | bound | margin with B = 910,000 (`v3_fits_910k`) | margin with exact B = 1,295,017 (`v3_over_bodyMax`) |
|---|---:|---:|---:|
| 1 | 7,450,143 | **+28,465** | **−356,552** |
| 2 | 7,146,495 | **+332,113** | **−52,904** |
| 3 | 7,193,567 | **+285,041** | **−99,976** |

## 3. Findings

1. **Lever (a) delivers about 2.3 MB on the v3 shapes, not 0.6–0.7 MB.** P1 model 9.73 MB → 7.45 MB at g = 1. It is only 1.34 MB on `nearAir`.
2. **§13's v3 projection was low by ≈ 1.9 MB: roll-in commits grow with the number of tables.** §13 used "3.95 MB + 864 B·`W_eq`", calibrated on `nearAir`, which has 7 tables.
   * With 23 tables, a header can place a table so that it rolls in at *every* one of the ℓ = 21 FRI layers. Every layer is then committed with arity 2 (`capE`, P1 finding).
   * The FRI DP saturates at about 21 tables. The FRI bound for the first k tables of `v3S 2` (`#eval`):

     | first k tables | FRI bound (B) |
     |---:|---:|
     | 1 | 1,061,952 |
     | 5 | 1,587,584 |
     | 10 | 2,210,496 |
     | 15 | 2,564,032 |
     | ≥ 21 | 2,686,144 |

   * Arity 16 changes nothing while roll-ins dominate: `friS` at `maxArityLog = 4` is still 2,686,144 (`v3_fri_noRoll`).
3. **With the exact hint bound, the margin is negative at every g, by 52,904 B at best (g = 2).** It is positive (+332 KB at g = 2) only under the design's 0.91 MB `B`.

## 4. Remaining levers, ranked (base: g = 2, 7,146,495 B; gap −52,904 B under exact B)

| # | lever | saving | kind / cost |
|---|---|---:|---|
| 1 | **Roll-in alignment.** The honest prover pads each table so that `log_T ≡ log_max (mod 3)`. Every roll-in then lands on a regular arity-8 commit. On the formal side, the admission's size hypothesis is needed only at **honest** headers: `hsize` is used only at `trHdr (traceOf c w)`, and the restricted header set needs an aligned `roll_count`. | **−1,624,192** (FRI 2,686,144 → 1,061,952, `v3_fri_noRoll`). Bound 5,522,303; margin +1.57 MB even with exact B. | No verifier or parameter change. Proof: ≈ 0.5 k LOC in this lane. Prover: pads up to 4× rows on unaligned tables. Tables whose `maxLog` blocks alignment (walk 21, chacha 21, gen/shuf 20, srcp 20, acct 17, …) need `maxLog` raised to the next aligned value (≤ 22; re-check `multBound`/`fpBound`). **Lead/assembly decision.** |
| 2 | **Compact refund codec in the hint.** `prep` re-encodes `B` natively. The wire drops the duplicated signer id (= receiver), `system`, the zero vector counts and the action tag. | ≈ −0.45 to −0.5 MB of B (≈ 289 → ≈ 180 B per refund) | Hint codec (spec/assembly). No proof-size bound change. |
| 3 | **auxGroup g = 2** instead of 1 | −303,648 (already in the base); g = 3 is +47,072 vs g = 2 | P2 done |
| 4 | **Width cuts.** Marginal cost (`v3_marginal`): **928 B per base column**, **7,008 B per aux K-column** (one interaction at g = 1, two at g = 2), **6,944 B per quotient chunk**. Closing −52,904 needs ≈ 57 base columns or 8 aux columns. Examples: ChaCha key → stream id (−32 cols ≈ −29.7 KB); the rcpt small-table merge (≈ 60–80 `W_eq` ≈ −52 to −70 KB, per STATUS-V3-RCPT §4.1); sched cut A (design: ≈ −0.27 MB). | per column as listed | per-lane re-proofs |
| 5 | **Fewer tables.** Only below about 21 tables does this help the FRI bound (finding 2). | 23 → 15: ≈ −122 KB; → 10: ≈ −476 KB (`#eval`) | big restructuring |
| 6 | Final degree `finalLog` 1 → 5 | −58,624 (FRI), minus ≈ 1 KB of final polynomial | **protocol change** (the final message is hard-coded `.elems 2`). Not proposed. |
| 7 | Arity 16 | 0 now; −71,104 after lever 1 (990,848 vs 1,061,952) | parameter change plus soundness numerics. Not proposed. |

**Recommendation.** Lever 1 (roll-in alignment) gives the decisive margin with no protocol change.

Without lever 1, at g = 2 the bound fits iff `B ≤ 1,242,113`:
* with the exact `B`, about 57 base columns of cuts (lever 4) are needed for a zero margin;
* adding `qvV3` (+75–112 KB) raises that to ≈ 140–180 columns, so lever 4 alone is thin.

The design's B figure should be corrected to 1,295,017; the spec lane should confirm it, or adopt lever 2. No protocol parameter has been changed.

## 5. Files, build

| file | content | elaboration (CPUs 8–15) |
|---|---|---|
| `Size/Dedup.lean` | `dsum`, `openSizeD`, `multiproof_size_le`, `openBytes_lengthD`, `sizeBoundD`, `size32D` | < 1 s |
| `Size/Sched.lean` | generic DP `phiG`, `go_schedG`, `fcostD`/`costD`, `sizeMaxDedup`, `sizeBoundD_le_dedup`, `sizeMaxDedup_le_sched` | < 2 s |
| `Size/Admission.lean` | `admission_v2_dedup`, `np_proverCompleteDedup`, `sizeBoundD_le_dedupP` | < 5 s |
| `Size/Model.lean` | `TShape`, `shapeOf`, `sizeOfWeq`, `sizeOfSchedS`, `sizeMaxDedup_eq_model` | < 1 s |
| `Size/V3Synth.lean` | synthetic v3 shapes `v3S g` | < 1 s |
| `Size/V3Eval.lean` | all kernel evaluations | 192 s, 6.4 GB |

Build:

```
lake build ZkFormal.Size.V3Eval ZkFormal.Size.Admission
```

`ZkFormal.lean` (the root import) is not modified.
