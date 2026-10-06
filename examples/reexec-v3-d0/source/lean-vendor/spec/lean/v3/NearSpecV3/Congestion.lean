import NearSpecV3.F64

/-!
# Congestion control decisions (nearcore 2.13.4, PV 86)

Leaf module of `near/pv86/chunk-validation/v0`. Transcribes
`CongestionControl` of `core/primitives/src/congestion_info.rs` for
`CongestionInfo::V1` (the only variant at PV 86):

* `CongestionInfoV1 { delayed_receipts_gas: u128, buffered_receipts_gas: u128,
  receipt_bytes: u64, allowed_shard: u16 }` (:462-472);
* `incoming/outgoing/memory_congestion` (:331-345) = `clamped_f64_fraction` of the
  three fields over `max_congestion_incoming_gas` / `max_congestion_outgoing_gas` /
  `max_congestion_memory_consumption`;
* `missed_chunks_congestion` (:68-77): `0.0` if `missed ≤ 1`, else
  `clamped_f64_fraction(missed as u128, max_congestion_missed_chunks)`;
* `congestion_level` (:44-54): `incoming.max(outgoing).max(memory).max(missed)`;
* `is_fully_congested` (:95-100): `level == 1.0`;
* `outgoing_gas_limit(sender)` (:80-93): fully congested ⇒ `allowed_shard_outgoing_gas`
  if `sender == allowed_shard` else 0; otherwise `mix(max_outgoing_gas, min_outgoing_gas, level)`;
* `clamped_f64_fraction` (:474-477), `mix` (:484-502).

All float operations use the exact binary64 model `NearSpecV3.F64`.

PV 86 `CongestionControlConfig` (runtime config; the oracle reads it from the
live `RuntimeConfigStore` and records it in `vectors/congestion.json "config"`):
`max_congestion_incoming_gas 4·10¹⁷`, `max_congestion_outgoing_gas 10¹⁶`,
`max_congestion_memory_consumption 10⁹`, `max_congestion_missed_chunks 125`,
`max_outgoing_gas 3·10¹⁷`, `min_outgoing_gas 10¹⁵`,
`allowed_shard_outgoing_gas 10¹⁵`.

**Integer characterization of `is_fully_congested`** (boundary doc §9.3). For
doubles `0 < a < b`, `a / b` rounds to a value `< 1.0` (if `b = 2^k·m`, then
`a ≤ b − ulp⁻(b)` and `a/b ≤ 1 − 2^-53`, which is representable), so
`clamped_f64_fraction(v, max) = 1.0` iff `v ≥ max` or `(v as f64) = (max as f64)`.
Since every term is `≤ 1.0` the level is `1.0` iff some term is. For the PV 86
constants the rounding intervals of the maxima give the integer thresholds:
* `4·10¹⁷ = 2^19·5^17 ∈ [2^58, 2^59)`, ulp 64, mantissa `2^13·5^17` even ⇒
  `(v as f64) = 4·10¹⁷` iff `|v − 4·10¹⁷| ≤ 32`; threshold `4·10¹⁷ − 32`;
* `10¹⁶ = 2^16·5^16 ∈ [2^53, 2^54)`, ulp 2, mantissa `5·10¹⁵` even ⇒ threshold `10¹⁶ − 1`;
* `10⁹ < 2^53` is exact ⇒ threshold `10⁹`;
* missed chunks: values `< 125` are exact ⇒ threshold `125` (and `125 > 1`).
`fullyCongestedInt` states this; `fullyCongested_boundaries` checks the
threshold points in the kernel. Agreement with the float model on all inputs is
**tested** (all 3000 oracle vectors plus a dense boundary sweep in
`TestSched.lean`), not proved in general.
-/

namespace NearSpecV3

/-- `CongestionInfoV1`. -/
structure CongestionInfo where
  delayedReceiptsGas : Nat
  bufferedReceiptsGas : Nat
  receiptBytes : Nat
  allowedShard : Nat
  deriving DecidableEq, Repr

/-- The fields of `CongestionControlConfig` used here. -/
structure CongestionConfig where
  maxCongestionIncomingGas : Nat
  maxCongestionOutgoingGas : Nat
  maxCongestionMemoryConsumption : Nat
  maxCongestionMissedChunks : Nat
  maxOutgoingGas : Nat
  minOutgoingGas : Nat
  allowedShardOutgoingGas : Nat
  deriving DecidableEq, Repr

def CongestionConfig.pv86 : CongestionConfig where
  maxCongestionIncomingGas := 400000000000000000
  maxCongestionOutgoingGas := 10000000000000000
  maxCongestionMemoryConsumption := 1000000000
  maxCongestionMissedChunks := 125
  maxOutgoingGas := 300000000000000000
  minOutgoingGas := 1000000000000000
  allowedShardOutgoingGas := 1000000000000000

namespace Congestion

/-- `clamped_f64_fraction(value, max)` (:474-477), `max > 0`. -/
def clampedFraction (v max : Nat) : F64 :=
  if max ≤ v then F64.one else F64.div (F64.ofNat v) (F64.ofNat max)

/-- `mix(left, right, ratio)` (:484-502). -/
def mix (left right : Nat) (ratio : F64) : Nat :=
  let leftPart := F64.mul (F64.ofNat left) (F64.sub F64.one ratio)
  let rightPart := F64.mul (F64.ofNat right) ratio
  F64.asU64 (F64.round (F64.add leftPart rightPart))

/-- `CongestionControl::congestion_level` (:44-54). -/
def level (cfg : CongestionConfig) (info : CongestionInfo) (missed : Nat) : F64 :=
  let incoming := clampedFraction info.delayedReceiptsGas cfg.maxCongestionIncomingGas
  let outgoing := clampedFraction info.bufferedReceiptsGas cfg.maxCongestionOutgoingGas
  let memory := clampedFraction info.receiptBytes cfg.maxCongestionMemoryConsumption
  let missedC := if missed ≤ 1 then F64.zero else clampedFraction missed cfg.maxCongestionMissedChunks
  F64.max (F64.max (F64.max incoming outgoing) memory) missedC

/-- `CongestionControl::is_fully_congested(level)` (:95-100). -/
def isFullyCongestedLevel (l : F64) : Bool := F64.beq l F64.one

def isFullyCongested (cfg : CongestionConfig) (info : CongestionInfo) (missed : Nat) : Bool :=
  isFullyCongestedLevel (level cfg info missed)

/-- `CongestionControl::outgoing_gas_limit(sender_shard)` (:80-93). -/
def outgoingGasLimit (cfg : CongestionConfig) (info : CongestionInfo) (missed : Nat)
    (senderShard : Nat) : Nat :=
  let l := level cfg info missed
  if isFullyCongestedLevel l then
    (if senderShard = info.allowedShard then cfg.allowedShardOutgoingGas else 0)
  else mix cfg.maxOutgoingGas cfg.minOutgoingGas l

/-- Integer characterization for PV 86 constants (see module doc). -/
def fullyCongestedInt (info : CongestionInfo) (missed : Nat) : Bool :=
  decide (400000000000000000 - 32 ≤ info.delayedReceiptsGas) ||
  decide (10000000000000000 - 1 ≤ info.bufferedReceiptsGas) ||
  decide (1000000000 ≤ info.receiptBytes) ||
  decide (125 ≤ missed)

/-- Generic form: `F1(v, max) = 1.0 ⇔ v ≥ max ∨ toF64 v = toF64 max`. -/
def clampedIsOneInt (v max : Nat) : Bool :=
  decide (max ≤ v) || F64.beq (F64.ofNat v) (F64.ofNat max)

/-- Threshold points of `fullyCongestedInt` against the float model. -/
theorem fullyCongested_boundaries :
    clampedFraction (400000000000000000 - 32) 400000000000000000 = F64.one ∧
    clampedFraction (400000000000000000 - 33) 400000000000000000 ≠ F64.one ∧
    clampedFraction (10000000000000000 - 1) 10000000000000000 = F64.one ∧
    clampedFraction (10000000000000000 - 2) 10000000000000000 ≠ F64.one ∧
    clampedFraction 999999999 1000000000 ≠ F64.one ∧
    clampedFraction 124 125 ≠ F64.one := by decide +kernel

end Congestion
end NearSpecV3
