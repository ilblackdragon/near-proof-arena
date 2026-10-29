import NearSpecV3.ChaCha20
import NearSpecV3.GF256
import NearSpecV3.ReedSolomon
import NearSpecV3.F64
import NearSpecV3.Congestion
import NearSpecV3.BandwidthScheduler
import NearSpecV3.Wire
import NearSpecV3.ClaimV3
import NearSpecV3.WitnessV3
import NearSpecV3.Layout
import NearSpecV3.TrieBuild
import NearSpecV3.RuntimeD0
import NearSpecV3.ChunkValidationV0
-- The D1 output-emitting checker (`checkD1CoreObs`, `checkD1CoreOut`) and its projection theorems.
-- Additive only: `checkD1` is defined as its projection, so importing this module changes no signed
-- statement and no verdict. Imported here so the axioms and the projection are in the default build.
import NearSpecV3.ChunkValidationD1Out
-- D0 ⊂ D1 (`relD0_relD1 : RelD0 cb w → RelD1 cb w`), proved; previously only tested on fixtures.
import NearSpecV3.D0SubD1
-- W11 proof debt: split correctness, column partition and authentication (2026-10-29).
import NearSpecV3.ReshardingProofs
-- W04 float fuel/range, and the guarded axiom audit of both.
import NearSpecV3.Wasm.FloatRange
import NearSpecV3.ProofDebtAudit
import NearSpecV3.ChallengeV3
import NearSpecV3.ClaimV3Props
import NearSpecV3.SHA512
import NearSpecV3.Ed25519
import NearSpecV3.ChallengeChunkV3Gas
import NearSpecV3.ChallengeChunkV3Float
-- The L2 float kernel's directed test suite (141 kernel-decided cases). Imported here, not just
-- built on demand, so that `lake build` checks them: a wrong bit pattern in `Wasm/Float.lean`
-- then breaks the build instead of only a downstream corpus run.
import NearSpecV3.Wasm.FloatTests
import NearSpecV3.StorageBound
import NearSpecV3.D3.CryptoDomain
import NearSpecV3.Wasm.CryptoHost
import NearSpecV3.D3.GlobalContractExec
-- L4's directed global-contract / state-init tests (134 kernel-evaluated cases). Imported here so
-- that the default `lake build` checks them: a wrong fee literal, trie-key byte or wallet hash
-- then breaks the build instead of only a downstream replay. Additive only -- nothing below this
-- import is reachable from `checkD2Core`/`checkD3`/`RelD3`, so the signed D3 statement is unchanged.
import NearSpecV3.D3.GlobalContractTests
import NearSpecV3.D3.GlobalContractChunk

-- Supply economics: the epoch inflation bound (2.5 %/yr) and the block header's supply identity,
-- plus the per-site accounting of the runtime's balance writes. Additive only: nothing here is
-- reachable from `checkD2Core`/`checkD3`/`RelD3`, so no signed statement or verdict changes.
import NearSpecV3.Supply
import NearSpecV3.SupplyRuntime
import NearSpecV3.SupplyConfinement
-- The state measure (§6): NEAR summed over the trie's account keys, plus gas keys, plus burnt.
-- Built on PTrie.allKeys' sound/complete pair; makes the per-site arithmetic composable.
import NearSpecV3.StateMeasure
-- Action-layer confinement (§7): no action writes an account key except actDeleteAccount on recv.
import NearSpecV3.ActionConfinement

-- Recursion track: segment fold semantics (Wasm/Segment.lean). Was orphaned until
-- 2026-10-23; imported here so the result is in the default build and cannot rot.
import NearSpecV3.Wasm.Segment
import NearSpecV3.Wasm.StEncode
import NearSpecV3.Wasm.EncodeRT
import NearSpecV3.Wasm.ValEncode
import NearSpecV3.Wasm.GasEncode
import NearSpecV3.Wasm.LabelEncode
