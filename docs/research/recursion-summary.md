# Recursion track: feasibility summary (input to the checkpoint-2 decision memo)

Status: **decided, checkpoint 2 outcome (B), option R5** (2026-10-06, accepted by the user). There is
no composition, and no bounded R1 either. D3 stays capped at `G_α`. The decision is recorded in
`D3_WASM_REQUIREMENTS.md` §2.5 (v0.3) and `RECURSION_REQUIREMENTS.md` (status).

The levers below move to the prover lane as `G_α` work (`D3_WASM_REQUIREMENTS.md` §2.4):
* taller tables with lower blowup;
* the Array-based verifier;
* a faster prover;
* the bus budget.

They matter because of the user's strategic point: the value of ZK is ONE proof across all shards,
which standard validator hardware cannot re-execute. Single-proof capacity (`G_α`) is therefore the
key metric. The analysis below was the input to the decision.

| Item | Result | Evidence class | Where |
|---|---|---|---|
| §3.1 segmentation semantics, PoC subset = the whole D3α interpreter | `run (Σks + n) s = foldSegments ks s >>= run n` for every split. The boundary state is the full `St`: control, memory, gas and stack budget, host state, storage overlay and recorder. | **P** (axioms propext, Classical.choice, Quot.sound) | `spec/lean/v3/NearSpecV3/Wasm/Segment.lean` |
| R1 cost model | Size formula exact on real proofs: 0 B error on the NEAR max-case proof (3,561,135 B), ±1.4% expected-size error on 33 proofs. 280–908 KB per segment, linear in S. | measured (size formula, slope, verify up to 5 MB, prove at S ≤ 4); assumed (D3 widths, gas mix); extrapolated (beyond) | `docs/research/recursion-r1-cost.md`, `tools/recursion/` |
| R1 at the caps | 8 MiB is reached at S ≈ 14 (≈ 48 Tgas). The existing verifier's bus budget 2^36 limits S to ≈ 31–50. The 600 s prove cap allows only S ≈ 1–3. 10^15 gas needs S ≈ 290: 124–253 MiB and 15–60 h of 8-vCPU proving. No break-even on the cost board at mainnet scale. | estimated from the calibrated model | same |
| R2 ROM theorem | Fits `CryptoSound`'s ROM branch unchanged: `RomSound` with `bcsNum` at 2^-128 for S ≤ 4096 and domains ≥ 2^16. This needs challenge-weighted `badPot` (request Q4) and intermediate query groups in BCS (Q1). | analysis | `docs/research/recursion-r2-theorem.md` |
| R2 core algebra | The closeness transfer through one accumulation step (`acc_close`, from `shift_close` and `quot_close`), the spot-check facts (`spot_doom`, `spot_escape`), and the farness form of the existing line gap (`line_far`). | **P**, kernel-checked against zk-formal Udr (read-only import); no sorry, no Mathlib | `recursion-poc/RecursionPoc/Accumulation.lean` |
| R2 size of the rest | ≈ 11–19k LOC on top of the multi-segment front end it shares with R1. | estimate | R2 doc §2.7 |
| R2 vs R1 cost | R2 is not cheaper with a native verifier. Every segment is still opened at ≈ 216 positions, accumulator openings add ≈ 40%, and the global buses force the same commit-everything-first schedule. | analytical, unmeasured | R2 doc §5 |

**Reading.**
* R1 is admissible today and its soundness work is small, but it does not reach mainnet-scale D3
  within the current caps. Its proof grows linearly, and **prove time is the binding cap**.
* R2 is provable inside the admission theorem but is not cheaper with a native verifier.
  Accumulation pays off only when the verifier would run in-circuit (R3), and R3 is not admissible.
* The strongest levers are outside composition:
  - lower blowup with taller tables, about 3× fewer bytes per operator;
  - a faster or parallel prover;
  - an Array-based Lean verifier, which removes the S² term;
  - raising the bus budget to 2^40 (2^-143 commit-phase term, not re-checked in the kernel).

  Even with every lever, 10^15 gas stays at or above ≈ 40 MiB.
* Together this pointed to (B) R5 for mainnet-scale D3. The *bounded* R1 option (S ≲ 14 under
  8 MiB) was considered and **rejected** by the user: `G_α` is raised by prover-lane levers instead.

**Interface requests to zk-formal** (not filed; zk-formal untouched): Q1–Q9 in the R2 doc §4. Q4
(challenge-weighted `badPot`) and the bus-budget increase also matter for R1 at S > 50.
