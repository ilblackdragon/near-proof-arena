import ZkFormal.V2.SizeSchedNear
import ZkFormal.V2.G.Defs
import ZkFormal.Near.NpOkCheck

/-!
# ZkFormal.V2.G.SizeNear — P2: the schedule-exact size bound at `auxGroup = g`

Kernel evaluations of `SizeSched.sizeMaxSched` at `pg g` for `nearAir` (v1's NEAR AIR, the
only full-size AIR in the tree) and the header-free size theorem at `g = 2, 3`.
`SizeSched.sizeBound_le_sched` is generic in `prm`, so only the evaluations are new.

Grouping changes the layout: `aux = chains + ⌈sends/g⌉ + ⌈recvs/g⌉` shrinks, but
`Table.degree g` (`2 + Σ_{group} phiDegree`) grows and with it `quot = degree - 1`.  The FRI
part is unchanged (`friSchedMax` depends only on LDE sizes).  On `nearAir` (all bus factors
have `phiDegree = 2`):

| `g` | per-table degree | Σ aux (K cols) | Σ quot (K cols) | `sizeMaxSched` (B) | delta vs `g = 1` |
|---|---|---|---|---|---|
| 1 | 4 ×7 | 66 | 21 | 5 473 967 | — |
| 2 | 6 ×6, 4 | 36 | 33 | 5 347 055 | −126 912 |
| 3 | 8 ×5, 6, 4 | 27 | 43 | 5 353 423 | −120 544 |

So on `nearAir` the quotient growth eats most of the aux saving, and `g = 2` is marginally
better than `g = 3` (V3-D0 §5.3's −0.46 MB estimate counts only the aux columns).
`nearAir_npOkG3` and `nearAir_deg3` check P2's side conditions on `nearAir` at `g = 3`.
-/

namespace ZkFormal.V2.SizeSched

open ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Near ZkFormal.Prover ZkFormal.Algebra

theorem near_friSchedMax_g3 : friSchedMax nearAir (G.pg 3) = 12928 := by decide +kernel

theorem near_sizeMaxSched_g2 : sizeMaxSched nearAir (G.pg 2) = 5347055 := by decide +kernel

theorem near_sizeMaxSched_g3 : sizeMaxSched nearAir (G.pg 3) = 5353423 := by decide +kernel

/-- Every admissible NEAR header at `g = 3` has `sizeBound ≤ 5 353 423` bytes. -/
theorem near_size_sched_g3 : ∀ hdr, (Iop.verifier Fp Fp8 nearAir (G.pg 3)).headerOk hdr = true →
    sizeBound (Iop.verifier Fp Fp8 nearAir (G.pg 3)) hdr ≤ 5353423 := fun hdr h =>
  Nat.le_trans (sizeBound_le_sched nearAir (G.pg 3) hdr (verifier_headerOk h).1)
    (Nat.le_of_eq near_sizeMaxSched_g3)

/-- Every admissible NEAR header at `g = 2` has `sizeBound ≤ 5 347 055` bytes. -/
theorem near_size_sched_g2 : ∀ hdr, (Iop.verifier Fp Fp8 nearAir (G.pg 2)).headerOk hdr = true →
    sizeBound (Iop.verifier Fp Fp8 nearAir (G.pg 2)) hdr ≤ 5347055 := fun hdr h =>
  Nat.le_trans (sizeBound_le_sched nearAir (G.pg 2) hdr (verifier_headerOk h).1)
    (Nat.le_of_eq near_sizeMaxSched_g2)

/-- P2's side condition `NpOkG` holds for `nearAir` at `g = 3`. -/
theorem nearAir_npOkG3 : G.NpOkG nearAir (G.pg 3) := by
  refine ⟨⟨3, rfl, by decide, by decide⟩, ?_, by decide⟩
  decide +kernel

/-- The table-degree part of `headerOk` holds for `nearAir` at `g = 3` (`degree ≤ 8 ≤ 16`). -/
theorem nearAir_deg3 : ∀ T ∈ nearAir.tables, T.degree 3 ≤ 2 ^ (G.pg 3).logBlowup := by
  decide +kernel

end ZkFormal.V2.SizeSched
