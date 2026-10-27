import NearSpecV3.Successor.Config

/-! # W02 Gate-B caps: unit tests for the limits changed on the successor tiers

* **Evaluator fuel.** A contract whose loop runs `2·K` zero-fee `block`/`end` instructions per
  charged `loop`/`br` pair exhausted the former `(gas / regular + 2)·64 + 10^6` step budget long
  before its gas, so the successor reported `unmodeled fuel exhausted` (an exclusion) for a call
  nearcore runs to `GasExceeded`. `Wasm.wasmFuel` runs it to its gas limit.
* **Transaction size.** `max_transaction_size` gates `wire_size` = body + borsh `Signature`, so a
  SECP256K1 transaction is one byte larger than an ED25519 one with the same body.
* **Tier configuration.** `.allFeatures` carries none of the arena caps; the signed tier keeps them.

The chunk-level counterparts (validated by pinned nearcore) are the `gate-b-caps` fixtures,
`docs/evidence/lean-chunk-completion/gate-b-caps/README.md`. -/

namespace NearSpecV3.Successor.GateBCapsTests
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm NearSpecV3.Successor

def assertTest (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"gate-b caps: {name}")

/-- Unsigned LEB128. -/
def leb : Nat → List UInt8
  | n => if n < 128 then [UInt8.ofNat n] else UInt8.ofNat (n % 128 + 128) :: leb (n / 128)
decreasing_by omega

/-- `(module (func (export "nest") (loop $l (block … (block) …) (br $l))))` with `k` nested blocks
(the same shape as `gburn.nest` in `oracle/v3-successor/src/scenarios.rs`). -/
def nestModule (k : Nat) : ByteArray :=
  let body : List UInt8 := [0x00, 0x03, 0x40] ++ (List.replicate k [0x02, 0x40]).flatten ++
    List.replicate k 0x0b ++ [0x0c, 0x00, 0x0b, 0x0b]
  let code : List UInt8 := [0x01] ++ leb body.length ++ body
  let sec (id : UInt8) (c : List UInt8) : List UInt8 := [id] ++ leb c.length ++ c
  ⟨([0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00] ++
    sec 1 [0x01, 0x60, 0x00, 0x00] ++ sec 3 [0x01, 0x00] ++
    sec 7 ([0x01, 0x04] ++ "nest".toUTF8.toList ++ [0x00, 0x00]) ++ sec 10 code).toArray⟩

/-- The former step budget, for the comparison. -/
def oldFuel (gas : Nat) : Nat := (gas / pv86.regularOpCost + 2) * 64 + 1000000

def ctx (gas : Nat) : CallCtx := { prepaidGas := gas }

/-- A transaction value with the given body and signature lengths (only the size gate reads them). -/
def txOf (body sig : Nat) (tag : Nat) : TxD2 :=
  { raw := [], body := List.replicate body 0, signer := [], pk := ⟨tag, []⟩, nonce := 0,
    nonceIdx := none, receiver := [], blockHash := [], actions := [], strict := false,
    sigTag := tag, sig := List.replicate sig 0 }

/-- 4-byte little-endian length, as the witness wire format uses. -/
def encU32 (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n % 256), UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n / 65536 % 256),
   UInt8.ofNat (n / 16777216 % 256)]
/-- A borsh byte string: 4-byte length then the bytes. -/
def encBytes (b : List UInt8) : List UInt8 := encU32 b.length ++ b

-- Small zstd frames produced by the vendored codec (`zref encode`, zstd 1.5.6) and their plaintext.
def frame_raw : List UInt8 := [40,181,47,253,0,88,1,1,0,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def plain_raw : List UInt8 := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def frame_rle : List UInt8 := [40,181,47,253,0,88,69,0,0,16,81,81,1,0,31,128,5]
def plain_rle : List UInt8 := List.replicate 40 81
def frame_huf : List UInt8 := [40,181,47,253,0,88,173,1,0,180,2,116,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103,2,0,241,212,128,65,59,203]
def plain_huf : List UInt8 := (List.replicate 3 "the quick brown fox jumps over the lazy dog ").foldl (· ++ ·.toUTF8.toList) []
def frame_seq : List UInt8 := [40,181,47,253,0,88,85,0,0,24,97,98,99,1,0,210,212,13,1]
def plain_seq : List UInt8 := (List.replicate 40 "abc").foldl (· ++ ·.toUTF8.toList) []

def runTests : IO Unit := do
  let code := nestModule 500
  let gas := 30 * 10 ^ 9
  let old := outcome pv86 code "nest" (ctx gas) (oldFuel gas)
  let new := outcome pv86 code "nest" (ctx gas) (NearSpecV3.Wasm.wasmFuel pv86 gas)
  assertTest s!"former fuel is exhausted before the gas ({old})" (old == "unmodeled fuel exhausted")
  assertTest s!"wasmFuel runs the call to GasExceeded ({new})"
    (new.startsWith s!"abort {gas} {gas} " && (new.splitOn "GasExceeded").length > 1)
  -- a call small enough for the former budget: both budgets give the same outcome
  let small := 15 * 10 ^ 8
  assertTest "budgets agree below the former limit"
    (outcome pv86 code "nest" (ctx small) (oldFuel small) ==
      outcome pv86 code "nest" (ctx small) (NearSpecV3.Wasm.wasmFuel pv86 small))
  let max := TxParams.maxTransactionSize
  assertTest "ED25519 at max_transaction_size" (txOf (max - 65) 64 0).sizeOk
  assertTest "ED25519 one byte above" (!(txOf (max - 64) 64 0).sizeOk)
  assertTest "SECP256K1 at max_transaction_size" (txOf (max - 66) 65 1).sizeOk
  assertTest "SECP256K1 body that fits ED25519 is one byte above" (!(txOf (max - 65) 65 1).sizeOk)
  assertTest "allFeatures lifts the caps"
    ((Tier.cfg .allFeatures).gasCap.isNone && (Tier.cfg .allFeatures).witnessUnbounded &&
      (Tier.cfg .allFeatures).layoutUnbounded && (Tier.cfg .allFeatures).segmentUnbounded)
  assertTest "signed keeps the caps"
    ((Tier.cfg .signed).gasCap == some D3.gAlpha && !(Tier.cfg .signed).witnessUnbounded &&
      !(Tier.cfg .signed).layoutUnbounded && !(Tier.cfg .signed).segmentUnbounded)
  -- W02 size limits: the zstd decoder (vendored zstd 1.5.6), the versioned witness format, and the
  -- two new caps. The frames below were produced by nearcore's `EncodedChunkStateWitness::encode`
  -- codec (`zref encode`, zstd level 3) on the paired plaintext.
  let okEq (r : Except String (List UInt8)) (exp : List UInt8) : Bool :=
    match r with | .ok v => v == exp | _ => false
  assertTest "zstd raw block" (okEq (Zstd.decompressList frame_raw) plain_raw)
  assertTest "zstd rle block" (okEq (Zstd.decompressList frame_rle) plain_rle)
  assertTest "zstd huffman literals" (okEq (Zstd.decompressList frame_huf) plain_huf)
  assertTest "zstd sequences" (okEq (Zstd.decompressList frame_seq) plain_seq)
  -- versioned witness.bin: the `near-arena-cwitness-v3` format carrying the compressed state
  -- witness decodes to the same `(swBytes, codes)` the in-the-clear format would.
  let cwit := encU32 witnessTagC.length ++ witnessTagC ++ encBytes frame_seq ++ encU32 0
  assertTest "decodeWitnessFileV compressed format"
    (match decodeWitnessFileV cwit with
     | .ok (sw, cs) => sw == plain_seq && cs.isEmpty
     | _ => false)
  let owit := encU32 witnessTag.length ++ witnessTag ++ encBytes plain_seq ++ encU32 0
  assertTest "decodeWitnessFileV old format falls through"
    (match decodeWitnessFileV owit, decodeWitnessFile owit with
     | .ok (a, _), .ok (b, _) => a == b
     | .error e1, .error e2 => e1 == e2
     | _, _ => false)
  -- encoded-length cap (`MAX_COMPRESSED_STATE_WITNESS_SIZE` = 48 MiB) and its reason
  let overEnc := encU32 witnessTagC.length ++ witnessTagC ++
    encBytes (List.replicate (maxCompressedWitnessBytes + 1) 0) ++ encU32 0
  assertTest "encoded_length over 48 MiB rejects"
    (match decodeWitnessFileV overEnc with
     | .error e => (e.splitOn "encoded_length exceeds").length > 1
     | _ => false)
  -- code-response cap bytes = 4 + Σ(4 + |code|); boundary at 64 MiB
  assertTest "codeResponseBytes empty" (codeResponseBytes [] == 4)
  assertTest "codeResponseBytes two codes" (codeResponseBytes [[1,2,3], [9]] == 4 + (4+3) + (4+1))
  assertTest "maxContractCodeResponseBytes = 64 MiB" (maxContractCodeResponseBytes == 67108864)
  assertTest "maxCompressedWitnessBytes = 48 MiB" (maxCompressedWitnessBytes == 50331648)
  IO.println s!"Gate-B cap tests passed: fuel ({old} → {new}), wire size, tier caps, zstd decoder, versioned witness, size caps"

end NearSpecV3.Successor.GateBCapsTests

def main : IO Unit := NearSpecV3.Successor.GateBCapsTests.runTests
