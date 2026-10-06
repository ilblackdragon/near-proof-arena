import ZkFormal.Size.V3Synth
import ZkFormal.Size.Admission

/-!
# ZkFormal.Size.V3Eval — kernel-checked evaluations of the deduplicated bound

All numbers are `decide +kernel` (no `native_decide`).

## `nearAir` (v1 NEAR AIR, 7 tables)

| `g` | `sizeMaxSched` (P1/P2) | **`sizeMaxDedup`** | saving |
|---|---:|---:|---:|
| 1 | 5,473,967 | **4,134,191** | −1,339,776 |
| 2 | 5,347,055 | **4,007,279** | −1,339,776 |
| 3 | 5,353,423 | **4,013,647** | −1,339,776 |

## Synthetic v3 AIR (`V3.v3S g`: 23 tables, one SHA)

| `g` | `W_eq` | `sizeOfSchedS` (P1 model) | **`sizeOfWeq` (dedup)** | FRI part |
|---|---:|---:|---:|---:|
| 1 | 4,434 | 9,729,983 | **7,450,143** | 2,686,144 |
| 2 | 4,090 | 9,426,335 | **7,146,495** | 2,686,144 |
| 3 | 4,146 | 9,473,407 | **7,193,567** | 2,686,144 |

`v3_bound_g*`: every AIR whose tables have these shapes satisfies `sizeBoundD ≤` the value at
every admissible header.
-/

namespace ZkFormal.Size.V3

open ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Near ZkFormal.Size ZkFormal.V2.SizeSched
  ZkFormal.Prover ZkFormal.Algebra ZkFormal.V2

/-! ## `nearAir` -/

theorem near_sizeMaxDedup : sizeMaxDedup nearAir Params.default = 4134191 := by decide +kernel
theorem near_sizeMaxDedup_g2 : sizeMaxDedup nearAir (V2.G.pg 2) = 4007279 := by decide +kernel
theorem near_sizeMaxDedup_g3 : sizeMaxDedup nearAir (V2.G.pg 3) = 4013647 := by decide +kernel

/-- Every admissible NEAR header (v1 verifier, deployed parameters) has a deduplicated
size bound of at most 4,134,191 bytes (P1: 5,473,967). -/
theorem near_size_dedup : ∀ hdr, (Iop.verifier Fp Fp8 nearAir Params.default).headerOk hdr = true →
    sizeBoundD (Iop.verifier Fp Fp8 nearAir Params.default) hdr ≤ 4134191 := fun hdr h =>
  Nat.le_trans (sizeBoundD_le_dedup nearAir Params.default hdr (verifier_headerOk h).1)
    (Nat.le_of_eq near_sizeMaxDedup)

/-! ## Transcription cross-checks (tables present in this tree) -/

/-- headV3, valV3, walkV3, uniqV3, upsV3: in-tree tables have the shapes transcribed from
lane `v3-trie` (`trieS g`, entries 2–6). -/
theorem trie_shapes_check : ∀ g ∈ [1, 2, 3],
    [NearV3.HeadV3.table, NearV3.ValV3.table, NearV3.WalkV3.table, NearV3.Uniq.table,
      NearV3.UpsV3.table].map (shapeOf g) = (trieS g).drop 1 := by decide +kernel

/-- sprV3, smmV3, scpV3: in-tree tables have the shapes transcribed from lane `v3-sched`
(`schedS g`, entries 3–5). -/
theorem sched_shapes_check : ∀ g ∈ [1, 2, 3],
    [NearV3.Sched.Proc.table, NearV3.Sched.Mem.table, NearV3.Sched.Cmp.table 7].map (shapeOf g) =
      (schedS g).drop 2 := by decide +kernel

/-! ## The synthetic v3 AIR -/

theorem v3_weq : [1, 2, 3].map (fun g => weqS (v3S g)) = [4434, 4090, 4146] := by decide +kernel

theorem v3_sizeOfWeq_g1 : sizeOfWeq (V2.G.pg 1) (v3S 1) = 7450143 := by decide +kernel
theorem v3_sizeOfWeq_g2 : sizeOfWeq (V2.G.pg 2) (v3S 2) = 7146495 := by decide +kernel
theorem v3_sizeOfWeq_g3 : sizeOfWeq (V2.G.pg 3) (v3S 3) = 7193567 := by decide +kernel

theorem v3_sizeOfSchedS : [1, 2, 3].map (fun g => sizeOfSchedS (V2.G.pg g) (v3S g)) =
    [9729983, 9426335, 9473407] := by decide +kernel

/-- `(prefix, main, aux, quotient, FRI)` at `g = 1, 2, 3`. -/
theorem v3_parts : [1, 2, 3].map (fun g => partsS (V2.G.pg g) (v3S g)) =
    [(175871, 2328544, 1511360, 748224, 2686144), (169439, 2328544, 965312, 997056, 2686144),
     (168127, 2328544, 799424, 1211328, 2686144)] := by decide +kernel

/-- **Any AIR with the v3 shapes**: on every admissible header of the v2 verifier at
`auxGroup = g`, `sizeBoundD ≤ sizeOfWeq (pg g) (v3S g)`. -/
theorem v3_bound (g : Nat) (AP : V2.AirP) (hA : AP.toAir.tables.map (shapeOf g) = v3S g)
    (hdr : List Nat) (h : (Iop.verifierP Fp Fp8 AP (V2.G.pg g)).headerOk hdr = true) :
    sizeBoundD (Iop.verifierP Fp Fp8 AP (V2.G.pg g)) hdr ≤ sizeOfWeq (V2.G.pg g) (v3S g) := by
  have := sizeBoundD_le_dedupP g AP hdr h
  rw [sizeMaxDedup_eq_model] at this
  exact Nat.le_trans this (Nat.le_of_eq (by rw [← hA]; rfl))

/-! ## Margins against the 8 MiB cap minus the hint body `B` -/

/-- Hint body under A1 by the decoder `pRefund`/`Receipt.encode`: `u32 0 ‖ u32 n ‖ n` refunds,
`n ≤ 4481`, each ≤ 10 (`system`) + 68 + 32 + 1 + 68 + 65 (SECP256K1) + 16 + 4 + 4 + 4 + 1 + 16
= 289 bytes. -/
def bodyMax : Nat := 8 + 4481 * (10 + 68 + 32 + 1 + 68 + 65 + 16 + 4 + 4 + 4 + 1 + 16)

theorem bodyMax_eq : bodyMax = 1295017 := by decide

/-- With the design's `B ≤ 910,000`: the bound fits at every `g` (margins 28,465 / 332,113 /
285,041 bytes). -/
theorem v3_fits_910k : sizeOfWeq (V2.G.pg 1) (v3S 1) + 910000 + 28465 = 8388608 ∧
    sizeOfWeq (V2.G.pg 2) (v3S 2) + 910000 + 332113 = 8388608 ∧
    sizeOfWeq (V2.G.pg 3) (v3S 3) + 910000 + 285041 = 8388608 := by
  rw [v3_sizeOfWeq_g1, v3_sizeOfWeq_g2, v3_sizeOfWeq_g3]; decide

/-- With the decoder's `B ≤ 1,295,017`: over by 356,552 / 52,904 / 99,976 bytes. -/
theorem v3_over_bodyMax : sizeOfWeq (V2.G.pg 1) (v3S 1) + bodyMax = 8388608 + 356552 ∧
    sizeOfWeq (V2.G.pg 2) (v3S 2) + bodyMax = 8388608 + 52904 ∧
    sizeOfWeq (V2.G.pg 3) (v3S 3) + bodyMax = 8388608 + 99976 := by
  rw [v3_sizeOfWeq_g1, v3_sizeOfWeq_g2, v3_sizeOfWeq_g3, bodyMax_eq]; decide

/-! ## Lever numbers -/

/-- The FRI DP without roll-in forced commits (`cap ≡ 0`: only the regular arity schedule), i.e.
the FRI part when every table's roll-in layer coincides with a regular commit. -/
def friNoRollS (prm : Params) (ts : List TShape) : Nat :=
  phiMaxG (max prm.maxArityLog 1) ts.length (fun _ => 0)
    (costD (prm.numChunks * prm.posPerChunk) (prm.logBlowup + prm.finalLog))
    (prm.maxLogLde - prm.logBlowup - prm.finalLog)

/-- Roll-in forced commits cost 1,624,192 of the 2,686,144 FRI bytes (`g = 2`); with arity 16
the regular schedule would cost 990,848. -/
theorem v3_fri_noRoll : friNoRollS (V2.G.pg 2) (v3S 2) = 1061952 ∧
    friNoRollS { V2.G.pg 2 with maxArityLog := 4 } (v3S 2) = 990848 ∧
    friS { V2.G.pg 2 with maxArityLog := 4 } (v3S 2) = 2686144 := by decide +kernel

/-- Add one column to the first (full-height) table. -/
def bumpS (f : TShape → TShape) : List TShape → List TShape
  | t :: ts => f t :: ts
  | [] => []

/-- Marginal bytes per base column / aux K-column / quotient K-column of a full-height table. -/
theorem v3_marginal :
    sizeOfWeq (V2.G.pg 2) (bumpS (fun t => { t with w := t.w + 1 }) (v3S 2)) = 7146495 + 928 ∧
    sizeOfWeq (V2.G.pg 2) (bumpS (fun t => { t with aux := t.aux + 1, fin := t.fin + 1 }) (v3S 2)) =
      7146495 + 7008 ∧
    sizeOfWeq (V2.G.pg 2) (bumpS (fun t => { t with quot := t.quot + 1 }) (v3S 2)) =
      7146495 + 6944 := by decide +kernel

end ZkFormal.Size.V3
