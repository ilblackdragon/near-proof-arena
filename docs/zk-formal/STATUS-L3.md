# STATUS — lane L3 (IOP math, unique-decoding regime)

Package `zk-formal/`, namespace `ZkFormal.Udr` (`ZkFormal.Udr.Np` for the protocol instance).
All listed "proved" items are sorry-free, axioms ⊆ {propext, Classical.choice, Quot.sound}.

## Generic UDR math (proved)

| Item | Theorem | File |
|---|---|---|
| CA ⇒ strong (containment) line lemma | `strong_of_ca`, `strong_of_gap` | `Udr/Code.lean` |
| d/3 gap + strong line, any linear code, vector symbols (≤ e+1 bad z) | `gap_d3`, `strong_line_d3` | `Udr/Code.lean` |
| interleaving lift of a 2e<d gap (same threshold) | `gap_interleave` | `Udr/Code.lean` |
| polynomial toolkit (root bounds, IsPoly, Fubini) | `coeffs_zero_of_roots`, `count_roots_lt`, `IsPoly.mul`, `ev_swap` | `Udr/Poly.lean` |
| RS codes (scalar, interleaved) | `rsCode`, `rsInterleaved`, `ev_eq_of_agree` | `Udr/RS.lean` |
| linear algebra (underdetermined systems) | `exists_nonzero_sol` | `Udr/BWLin.lean` |
| **BW d/2 RS line gap** (threshold 3n+2e+1, 2e+D ≤ n) | `rsGap : RsGapStmt` | `Udr/BW.lean` |
| **strong line, interleaved RS, d/2** | `strong_line_rs`, `strong_line_rs_scalar` | `Udr/Main.lean` |
| **FRI pass-set argument** (virtual folds, roll-ins, e_i ≤ 2e_{i+1}+1) | `fri : FriStmt`, `friRoll : FriRollStmt`, `fri_query_bound` | `Udr/Fri.lean`, `Udr/Main.lean` |
| **grand product** (γ round) / fingerprints (α round) | `gpGamma`, `gpAlpha` | `Udr/GrandProduct.lean` |
| **DEEP farness** / closeness transfer | `deep_close`, `deep_value` | `Udr/Deep.lean` |
| **multilinear batching** chain | `batch_close`, `batch_chain` | `Udr/Deep.lean` |

## RbrFacts for np-udr-stark (`Udr/Rbr.lean`, `Udr/Np/*`) — **DONE**

**`ZkFormal.Udr.Np.rbrWith`** (`Udr/Np/Main.lean`), sorry-free, axioms ⊆ {propext, Classical.choice, Quot.sound}:

```lean
theorem rbrWith (A : Air) (prm : Params) (hok : NpOk A prm) :
    RbrWith (Iop.verifier Fp Fp8 A prm) (AirLang Fp A) Fp8.all badBudget (agreeUdr prm.logBlowup) (Doomed A prm)
```
with `badBudget = 2^36`, `agreeUdr b n = n - ((n - n/2^b)/2 - 1)`, and
`NpOk A prm := prm = Params.default ∧ (∀ T ∈ A.tables, allConstraints + 2·auxCount + 3·#interactions ≤ 2^20) ∧ A.numBuses < 2^30`
(decidable on the concrete AIR). This is the `hR` input of L2's `Bcs.stark_romSound_rbr`.

| Obligation | Theorem | File(s) |
|---|---|---|
| `ShapedPrefixStmt`, `ScheduleAltStmt` | `shapedPrefix`, `scheduleAlt` | Shape.lean |
| main commit (`¬InLang ⇒` far or decoded trace fails) | `msg0` | Early.lean, Hom.lean |
| `α_fp` (fingerprints ≤ `Air.fpBound`) | `chal1` | BusRounds.lean, Bus.lean |
| `γ` (grand product ≤ `Air.multBound`) | `chal3` | BusRounds.lean |
| aux commit (running products ⇒ grand products) | `msg4` | Msg4.lean, AuxChain.lean |
| `α_c` (constraint combination) | `chal5` | Ali.lean |
| quotient commit | `msg6` | Early.lean |
| `z` (ALI identity, `z ∈ F` counted bad) | `chal7` | Chal7.lean, Degree.lean |
| OOD values (DEEP farness, global = semantic ALI) | `msg8` | Msg8.lean, Deep8.lean, Global8.lean |
| batching `r_k`, FRI `β_i`/`γ_i` | `chalLate` | Late.lean |
| later messages (frame) | `msgLate` | FrameMsg.lean, FrameFri.lean |
| query phase (FRI pass sets, local bridge from `checkAt`) | `query_of_deepSem` | Query.lean, Good.lean, Bridge1–7.lean, Domain.lean |
| verifier `deepAt` = batched DEEP word | `deepSem` | DeepSem.lean, SumR.lean |

Definition fixes found while proving (all in REQUESTS.md): radius `(n-D)/2 - 1` (R-L3-2), stage 8 needs `z ∉ F`,
bus indices `< p` (R-L3-5, `NpOk`).

Size: `Udr/` ≈ 11.2k lines. Elaboration: all `Udr` modules rebuilt from scratch in ≈ 23 s wall (≈ 56 s CPU).
