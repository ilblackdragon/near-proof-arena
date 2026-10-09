import ZkFormal.NearV3.Assembly.NearAir
import ZkFormal.Size.HonestAdmission

/-!
# Proof-size and admission-interface facts for the assembled v3 AIR

Decision (this lane): `auxGroup = g = 2`, two SHA-256 instances, `B0 = 2,000,000`.
The aligned deduplicated bound of `nearAirV3` at `g = 2` is `6,276,897` bytes,
leaving `816,694` bytes under the 8 MiB cap after the maximum hint body
`B ≤ 1,295,017` (`Size.V3.bodyMax_eq`).

* `nearV3_sizeMaxAligned` / `nearV3_size` — every admissible honest (roll-aligned)
  header of the v2 verifier at `g = 2` has `sizeBoundD ≤ 6,276,897`.
* `nearAirV3_wf`, `nearAirV3_npOkPg` (from `Assembly.NearAirCheck`) are the static parts.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.V2 ZkFormal.Size ZkFormal.Stark ZkFormal.Algebra

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The aligned deduplicated size bound of `nearAirV3` at `auxGroup = 2`. -/
theorem nearV3_sizeMaxAligned : sizeMaxAligned nearAirV3.toAir (ZkFormal.V2.G.pg 2) = 6276897 := by
  decide +kernel

/-- **The v3 size bound.** On every admissible header of the deployed public-bus
verifier at `auxGroup = 2` that is honest and roll-in aligned, the deduplicated
proof-size bound is `6,276,897` bytes. -/
theorem nearV3_size (hdr : List Nat)
    (h : (Iop.verifierP Fp Fp8 nearAirV3 (ZkFormal.V2.G.pg 2)).headerOk hdr = true)
    (ha : RollAligned nearAirV3.toAir (ZkFormal.V2.G.pg 2) hdr) :
    sizeBoundD (Iop.verifierP Fp Fp8 nearAirV3 (ZkFormal.V2.G.pg 2)) hdr ≤ 6276897 := by
  calc sizeBoundD (Iop.verifierP Fp Fp8 nearAirV3 (ZkFormal.V2.G.pg 2)) hdr
      ≤ sizeMaxAligned nearAirV3.toAir (ZkFormal.V2.G.pg 2) :=
        sizeBoundD_le_alignedP 2 nearAirV3 hdr h ha
    _ = 6276897 := nearV3_sizeMaxAligned

/-- The `g = 2` admission-scheme parameters for the v3 AIR. -/
def v3AuxGroup : Nat := 2

theorem v3AuxGroup_bounds : 1 ≤ v3AuxGroup ∧ v3AuxGroup ≤ 3 := by decide

end ZkFormal.NearV3.Assembly
