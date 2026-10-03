import ArenaCore.SHA256
import NearSpec.Bytes

/-!
# SHA-256

nearcore's `CryptoHash::hash_bytes` is SHA-256 (`core/primitives-core/src/hash.rs`).
NearSpec uses formal-core's `ArenaCore.sha256` (FIPS 180-4, kernel-reducible)
directly — the same function the NPAI interpreter's `SHA256` opcode and the
`sha256_cr` assumption (`ArenaCore.Assumptions.Sha256CollisionResistant`) are
stated over. There is no second SHA-256 implementation in the trusted base.
-/

namespace NearSpec

/-- `CryptoHash::hash_bytes` in nearcore = `ArenaCore.sha256`. -/
abbrev sha256 (m : Bytes) : Bytes := ArenaCore.sha256 m

end NearSpec
