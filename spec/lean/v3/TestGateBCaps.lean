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
  IO.println s!"Gate-B cap tests passed: fuel ({old} → {new}), wire size, tier caps"

end NearSpecV3.Successor.GateBCapsTests

def main : IO Unit := NearSpecV3.Successor.GateBCapsTests.runTests
