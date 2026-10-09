import ZkFormal.Size.V3Synth
import ZkFormal.Size.Admission
import ZkFormal.NearV3.Rcpt.Budget

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
| 1 | 4,448 | 9,742,975 | **7,463,135** | 2,686,144 |
| 2 | 4,104 | 9,439,327 | **7,159,487** | 2,686,144 |
| 3 | 4,160 | 9,486,399 | **7,206,559** | 2,686,144 |

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

/-- All six trie tables, including nodeV3's UPB delta and upsV3's root binding/full-range carries,
have the transcribed shapes. -/
theorem trie_shapes_check : ∀ g ∈ [1, 2, 3],
    NearV3.Budget.trieTablesU.map (shapeOf g) = trieS g := by decide +kernel

/-- All five scheduler tables have the transcribed shapes. -/
theorem sched_shapes_check : ∀ g ∈ [1, 2, 3],
    NearV3.Sched.Budget.schedTables.map (shapeOf g) = schedS g := by decide +kernel

/-- All six receipt tables have the transcribed shapes. -/
theorem rcpt_shapes_check : ∀ g ∈ [1, 2, 3],
    NearV3.Rcpt.Budget.rcptTables.map (shapeOf g) = rcptS g := by decide +kernel

/-! ## The synthetic v3 AIR -/

theorem v3_weq : [1, 2, 3].map (fun g => weqS (v3S g)) = [4448, 4104, 4160] := by decide +kernel

theorem v3_sizeOfWeq_g1 : sizeOfWeq (V2.G.pg 1) (v3S 1) = 7463135 := by decide +kernel
theorem v3_sizeOfWeq_g2 : sizeOfWeq (V2.G.pg 2) (v3S 2) = 7159487 := by decide +kernel
theorem v3_sizeOfWeq_g3 : sizeOfWeq (V2.G.pg 3) (v3S 3) = 7206559 := by decide +kernel

theorem v3_sizeOfSchedS : [1, 2, 3].map (fun g => sizeOfSchedS (V2.G.pg g) (v3S g)) =
    [9742975, 9439327, 9486399] := by decide +kernel

/-- `(prefix, main, aux, quotient, FRI)` at `g = 1, 2, 3`. -/
theorem v3_parts : [1, 2, 3].map (fun g => partsS (V2.G.pg g) (v3S g)) =
    [(176767, 2340640, 1511360, 748224, 2686144), (170335, 2340640, 965312, 997056, 2686144),
     (169023, 2340640, 799424, 1211328, 2686144)] := by decide +kernel

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

/-- With the design's `B ≤ 910,000`: the bound fits at every `g` (margins 15,473 / 319,121 /
272,049 bytes). -/
theorem v3_fits_910k : sizeOfWeq (V2.G.pg 1) (v3S 1) + 910000 + 15473 = 8388608 ∧
    sizeOfWeq (V2.G.pg 2) (v3S 2) + 910000 + 319121 = 8388608 ∧
    sizeOfWeq (V2.G.pg 3) (v3S 3) + 910000 + 272049 = 8388608 := by
  rw [v3_sizeOfWeq_g1, v3_sizeOfWeq_g2, v3_sizeOfWeq_g3]; decide

/-- With the decoder's `B ≤ 1,295,017`: over by 369,544 / 65,896 / 112,968 bytes. -/
theorem v3_over_bodyMax : sizeOfWeq (V2.G.pg 1) (v3S 1) + bodyMax = 8388608 + 369544 ∧
    sizeOfWeq (V2.G.pg 2) (v3S 2) + bodyMax = 8388608 + 65896 ∧
    sizeOfWeq (V2.G.pg 3) (v3S 3) + bodyMax = 8388608 + 112968 := by
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
    sizeOfWeq (V2.G.pg 2) (bumpS (fun t => { t with w := t.w + 1 }) (v3S 2)) = 7159487 + 928 ∧
    sizeOfWeq (V2.G.pg 2) (bumpS (fun t => { t with aux := t.aux + 1, fin := t.fin + 1 }) (v3S 2)) =
      7159487 + 7008 ∧
    sizeOfWeq (V2.G.pg 2) (bumpS (fun t => { t with quot := t.quot + 1 }) (v3S 2)) =
      7159487 + 6944 := by decide +kernel

end ZkFormal.Size.V3
