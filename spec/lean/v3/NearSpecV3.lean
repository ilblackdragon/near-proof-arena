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
import NearSpecV3.ChallengeV3
import NearSpecV3.ClaimV3Props
import NearSpecV3.SHA512
import NearSpecV3.Ed25519

-- Recursion track: segment fold semantics (Wasm/Segment.lean). Was orphaned until
-- 2026-10-23; imported here so the result is in the default build and cannot rot.
import NearSpecV3.Wasm.Segment
import NearSpecV3.Wasm.StEncode
import NearSpecV3.Wasm.EncodeRT
import NearSpecV3.Wasm.ValEncode
import NearSpecV3.Wasm.GasEncode
import NearSpecV3.Wasm.LabelEncode
