import NearSpecV3.Wasm.CryptoHost
import NearSpecV3.AltBn128

/-!
# Host-arm tests for the three `alt_bn128_*` hosts (`D3γ` table)

`TestAltBn128.lean` compares the payload functions (`AltBn128.g1MultiExp`, `g1Sum`,
`pairingCheck`) against the pinned `zeropool-bn` oracle. This module tests the **host arms** — the
layer `wasmtime_runner/logic.rs` owns and the payloads do not:

* argument order `(value_len, value_ptr, register_id)` read from the wasm operand stack;
* the charge order and the exact gas of every branch, including the length error;
* memory-sourced vs register-sourced input (`value_len = u64::MAX` selects the register);
* the return convention: the two writers write 64 bytes and push nothing, `pairing_check` pushes
  `0`/`1` and writes no register;
* the `HostError(AltBn128 invalid input: …)` message text, including `stdx`'s split wording.

Source: `wasmtime_runner/logic.rs:932-954` (`alt_bn128_g1_multiexp`), `:982-1004`
(`alt_bn128_g1_sum`), `:1033-1054` (`alt_bn128_pairing_check`), and `logic/alt_bn128.rs`
(the payloads and `split_elements`). Gas: PV86
`core/parameters/res/runtime_configs/parameters.snap:173-178`.

Every expectation below is derived from the Rust source, not from the Lean implementation; the
payload verdicts are separately pinned against the oracle in `TestAltBn128.lean`.
-/

open NearSpecV3 NearSpecV3.Wasm
open ArenaCore

namespace NearSpecV3.Wasm.AltBn128HostTest

/-! ## Harness (same shape as `TestBLS12381Host`) -/

structure Out where
  ret : Option Nat
  reg : Option Bytes
  burnt : Nat
  used : Nat
  err : Option String
  deriving Repr

def mkSt (regs : Array (Nat × ByteArray)) (regUsage : Nat) (prepaid : Nat) : St :=
  { pages := #[⟨Array.replicate pageSize 0⟩], globals := #[], table := #[], tableMax := 0,
    elems := #[], datas := #[], stackRem := 0, gas := Gas.init prepaid,
    registers := regs, regUsage := regUsage }

def runHost (h : HM Unit) (s : St) : Out :=
  match h.run s with
  | .ok _ s' =>
    { ret := s'.stack.back?.map (fun v => match v with
        | .i64 x => x.toNat | .i32 x => x.toNat | _ => 0)
      reg := (s'.registers.find? (·.1 = 0)).map (fun p => p.2.toList)
      burnt := s'.gas.burnt, used := s'.gas.used, err := none }
  | .error e s' =>
    { ret := none
      reg := (s'.registers.find? (·.1 = 0)).map (fun p => p.2.toList)
      burnt := s'.gas.burnt, used := s'.gas.used, err := some e }

def runMem (arm : Vector Nat 3 → HM Unit) (data : Bytes) (ptr : Nat) (prepaid : Nat := 10 ^ 15) :
    Out :=
  let st := writeBytes (mkSt #[] 0 prepaid) ptr ⟨data.toArray⟩
  runHost (arm ⟨#[data.length, ptr, 0], by simp⟩) st

def runReg (arm : Vector Nat 3 → HM Unit) (data : Bytes) (reg : Nat) (prepaid : Nat := 10 ^ 15) :
    Out :=
  let st := mkSt #[(reg, ByteArray.mk data.toArray)] (data.length + 8) prepaid
  runHost (arm ⟨#[u64Bound - 1, reg, 0], by simp⟩) st

def runPairMem (data : Bytes) (ptr : Nat) (prepaid : Nat := 10 ^ 15) : Out :=
  let st := writeBytes (mkSt #[] 0 prepaid) ptr ⟨data.toArray⟩
  runHost (hostAltBn128PairingCheck ⟨#[data.length, ptr], by simp⟩) st

def runPairReg (data : Bytes) (reg : Nat) (prepaid : Nat := 10 ^ 15) : Out :=
  let st := mkSt #[(reg, ByteArray.mk data.toArray)] (data.length + 8) prepaid
  runHost (hostAltBn128PairingCheck ⟨#[u64Bound - 1, reg], by simp⟩) st

def readCost (n : Nat) : Nat := C.readMemoryBase.gas + n * C.readMemoryByte.gas
def writeCost (n : Nat) : Nat := C.writeRegisterBase.gas + n * C.writeRegisterByte.gas
def regReadCost (n : Nat) : Nat := C.readRegisterBase.gas + n * C.readRegisterByte.gas

/-- `base + read_memory(len) + element·(len/itemSize)`, plus the write when the writer ran. The
per-element count is taken from the *split input*, so it is `len / itemSize` only after the length
gate passed. -/
def writerGas (base element itemSize outLen : Nat) (len : Nat) (wrote : Bool) : Nat :=
  base + readCost len + element * (len / itemSize) + (if wrote then writeCost outLen else 0)

def isAltBn128Invalid (r : Out) : Bool :=
  match r.err with
  | some e => e.startsWith "HostError(AltBn128 invalid input:"
  | none => false

def unhex (s : String) : Bytes := (Bytes.ofHex? s).getD []
def hexOf (b : Bytes) : String := Bytes.toHex b

/-! ## Directed constants

The bn generators (`zeropool-bn-0.5.11/src/groups/mod.rs:583-648`, de-Montgomeryised and verified
against the crate's own curve equations). -/

def g1Gen : Bytes :=
  unhex "01000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000"

def g2Gen : Bytes :=
  unhex "edf692d95cbdde46ddda5ef7d422436779445c5e66006a42761e1f12efde0018c212f3aeb785e49712e7a9353349aaf1255dfb31b7bf60723a480d9293938e19aa7dfa6601cce64c7bd3430c69e7d1e38f40cb8d8071ab4aeb6d8cdba55ec8125b9722d1dcdaac55f38eb37033314bbc95330c69ad999eec75f05f58d0890609"

/-- One element of `g1_multiexp`: the G1 generator with scalar `1`. The scalar is 32-byte
little-endian, so its `1` is the *first* byte (`logic/alt_bn128.rs:156-161`). -/
def g1GenScalar1 : Bytes := g1Gen ++ [1] ++ List.replicate 31 0

/-! ## `g1_multiexp` -/

def multiexpChecks : List (String × Bool) :=
  let ok := runMem hostAltBn128G1Multiexp g1GenScalar1 64
  let empty := runMem hostAltBn128G1Multiexp [] 64
  let badLen := runMem hostAltBn128G1Multiexp (g1GenScalar1 ++ [0]) 64
  let viaReg := runReg hostAltBn128G1Multiexp g1GenScalar1 5
  [ ("multiexp: valid writes 64 bytes", ok.reg.map List.length == some 64),
    ("multiexp: valid no error", ok.err == none),
    ("multiexp: valid pushes nothing", ok.ret == none),
    ("multiexp: valid 1*G == G", ok.reg == some g1Gen),
    ("multiexp: valid burnt gas",
      ok.burnt = writerGas altBn128G1MultiexpBase.gas altBn128G1MultiexpElement.gas 96 64 96 true),
    ("multiexp: valid used gas == burnt",
      ok.used = writerGas altBn128G1MultiexpBase.gas altBn128G1MultiexpElement.gas 96 64 96 true),
    -- empty input: the sum is infinity, encoded as 64 zero bytes, and no element is charged
    ("multiexp: empty writes 64 zero bytes", empty.reg == some (List.replicate 64 0)),
    ("multiexp: empty gas",
      empty.burnt = altBn128G1MultiexpBase.gas + readCost 0 + writeCost 64),
    -- 97 bytes: the split fails *before* pay_per, so base + read(97) and no element charge
    ("multiexp: bad length errors", isAltBn128Invalid badLen),
    ("multiexp: bad length writes nothing", badLen.reg == none),
    ("multiexp: bad length burnt gas",
      badLen.burnt = altBn128G1MultiexpBase.gas + readCost 97),
    ("multiexp: bad length message mentions 96",
      match badLen.err with
      | some e => (e.splitOn "chunks of size 96").length > 1
      | none => false),
    -- register-sourced: the register path pays read_register, not read_memory
    ("multiexp: register input succeeds", viaReg.err == none),
    ("multiexp: register input writes 64 bytes", viaReg.reg.map List.length == some 64),
    ("multiexp: register input gas",
      viaReg.burnt = altBn128G1MultiexpBase.gas + regReadCost 96
        + altBn128G1MultiexpElement.gas * 1 + writeCost 64) ]

/-! ## `g1_sum` -/

def sumChecks : List (String × Bool) :=
  let one := [0] ++ g1Gen
  let dbl := one ++ [1] ++ g1Gen  -- G + (-G) = infinity
  let ok := runMem hostAltBn128G1Sum one 64
  let cancel := runMem hostAltBn128G1Sum dbl 64
  let empty := runMem hostAltBn128G1Sum [] 64
  let badSign := runMem hostAltBn128G1Sum ([2] ++ g1Gen) 64
  let badLen := runMem hostAltBn128G1Sum (one ++ [0]) 64
  [ ("sum: valid writes 64 bytes", ok.reg.map List.length == some 64),
    ("sum: valid no error", ok.err == none),
    ("sum: valid 0*G == G", ok.reg == some g1Gen),
    ("sum: valid pushes nothing", ok.ret == none),
    ("sum: valid burnt gas",
      ok.burnt = writerGas altBn128G1SumBase.gas altBn128G1SumElement.gas 65 64 65 true),
    ("sum: G + (-G) == infinity", cancel.reg == some (List.replicate 64 0)),
    ("sum: empty == infinity", empty.reg == some (List.replicate 64 0)),
    ("sum: empty gas", empty.burnt = altBn128G1SumBase.gas + readCost 0 + writeCost 64),
    ("sum: sign 2 errors", isAltBn128Invalid badSign),
    ("sum: sign 2 writes nothing", badSign.reg == none),
    -- sign 2 is a *decode* failure, so it pays the per-element charge
    ("sum: sign 2 gas",
      badSign.burnt = altBn128G1SumBase.gas + readCost 65 + altBn128G1SumElement.gas),
    ("sum: bad length errors", isAltBn128Invalid badLen),
    ("sum: bad length gas", badLen.burnt = altBn128G1SumBase.gas + readCost 66) ]

/-! ## `pairing_check`: no register, `0`/`1` verdict -/

def pairGas (len : Nat) : Nat :=
  altBn128PairingBase.gas + readCost len + altBn128PairingElement.gas * (len / 192)

def pairChecks : List (String × Bool) :=
  let empty := runPairMem [] 64
  let onePair := runPairMem (g1Gen ++ List.replicate 128 0) 64  -- infinity G2, so product is 1
  let badLen := runPairMem [0] 64
  let viaReg := runPairReg (g1Gen ++ List.replicate 128 0) 5
  [ -- the empty product is one, so the verdict is `1`
    ("pair: empty returns 1", empty.ret == some 1),
    ("pair: empty writes no register", empty.reg == none),
    ("pair: empty no error", empty.err == none),
    ("pair: empty gas", empty.burnt = pairGas 0),
    -- a pair whose G2 point is infinity contributes 1, so the product is 1
    ("pair: infinity G2 returns 1", onePair.ret == some 1),
    ("pair: infinity G2 gas", onePair.burnt = pairGas 192),
    -- a malformed length is a host error after base + read, with no per-element charge
    ("pair: bad length errors", isAltBn128Invalid badLen),
    ("pair: bad length burnt gas", badLen.burnt = altBn128PairingBase.gas + readCost 1),
    -- register-sourced: charge comes from the register's own length
    ("pair: register input returns 1", viaReg.ret == some 1),
    ("pair: register input gas", viaReg.burnt = altBn128PairingBase.gas + regReadCost 192
        + altBn128PairingElement.gas) ]

/-! ## Argument order

A transposition of `(value_len, value_ptr)` is discriminating for `g1_multiexp`: the source order
reads 96 bytes at pointer 64, the transposed order reads 64 bytes at pointer 96 and the length gate
then rejects `64 % 96 ≠ 0`. -/

def orderChecks : List (String × Bool) :=
  let st := writeBytes (mkSt #[] 0 (10 ^ 15)) 64 ⟨g1GenScalar1.toArray⟩
  let ok := runHost (hostAltBn128G1Multiexp ⟨#[g1GenScalar1.length, 64, 0], by simp⟩) st
  let tr := runHost (hostAltBn128G1Multiexp ⟨#[64, g1GenScalar1.length, 0], by simp⟩) st
  [ ("order: source order succeeds", ok.reg.map List.length == some 64),
    ("order: transposed call errors on the length gate", isAltBn128Invalid tr),
    ("order: transposed call burns a different amount", tr.burnt != ok.burnt) ]

/-! ## `cryptoHostCall` dispatch -/

def dispatchChecks : List (String × Bool) :=
  [ ("dispatch: alt_bn128_g1_multiexp selects an arm",
      (cryptoHostCall "alt_bn128_g1_multiexp").isSome),
    ("dispatch: alt_bn128_g1_sum selects an arm", (cryptoHostCall "alt_bn128_g1_sum").isSome),
    ("dispatch: alt_bn128_pairing_check selects an arm",
      (cryptoHostCall "alt_bn128_pairing_check").isSome),
    ("dispatch: unknown alt_bn128 name stays out of domain",
      (cryptoHostCall "alt_bn128_nope").isNone),
    ("dispatch: empty name stays out of domain", (cryptoHostCall "").isNone),
    -- the table selects an arm for every name the D3α guard excludes
    ("dispatch: every cryptoHosts name has an arm",
      cryptoHosts.all (fun n => (cryptoHostCall n).isSome)) ]

def allChecks : List (String × Bool) :=
  multiexpChecks ++ sumChecks ++ pairChecks ++ orderChecks ++ dispatchChecks

def main : IO UInt32 := do
  let mut bad := 0
  for (name, ok) in allChecks do
    if !ok then
      bad := bad + 1
      IO.eprintln s!"ALTBN128 HOST FAIL: {name}"
  IO.println s!"alt_bn128 host cases: {allChecks.length} total, {bad} failures"
  return if bad = 0 then 0 else 1

end NearSpecV3.Wasm.AltBn128HostTest

def main (args : List String) : IO UInt32 := NearSpecV3.Wasm.AltBn128HostTest.main
