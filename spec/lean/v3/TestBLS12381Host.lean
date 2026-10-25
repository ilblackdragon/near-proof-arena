import NearSpecV3.Wasm.CryptoHost
import NearSpecV3.BLS12381
import NearSpecV3.BLS12381Pairing

/-!
# Host-arm tests for the nine `bls12381_*` hosts (`D3γ` table)

The payload suite (`TestBLS12381.lean`) compares `BLS12381.p1Sum` and friends against the pinned
`blst` oracle. This module tests the **host arms** — the layer nearcore's
`bls12381_impl!`/`bls12381_pairing_check` bodies own and the payload functions do not:

* argument order `(value_len, value_ptr, register_id)` read from the wasm operand stack;
* the charge order and the exact gas of every branch, including the length error;
* memory-sourced vs register-sourced input (`value_len = u64::MAX` selects the register);
* the return convention (`0` + register write on success, `1` + no write on a decode failure);
* the `HostError(BLS12381InvalidInput …)` message text;
* `pairing_check`'s own order: base, **read**, per-element from `data.len()`, decode, and its
  three-way `0`/`1`/`2` verdict with no register write at all.

Source: `runtime/near-vm-runner/src/wasmtime_runner/logic.rs:33-83` (the `bls12381_impl!` macro),
`:1352-1376` (`bls12381_pairing_check`), and `runtime/near-vm-runner/src/logic/bls12381.rs`
(the payloads). Gas: PV86 `core/parameters/res/runtime_configs/parameters.snap:184-201`.

Every expectation below is derived from the Rust source, not from the Lean implementation; the
payload verdicts are additionally cross-checked against the `blst` oracle in `TestBLS12381.lean`.
-/

open NearSpecV3 NearSpecV3.Wasm
open ArenaCore

namespace NearSpecV3.Wasm.BLSHostTest

/-! ## Harness -/

/-- Outcome of one host call. -/
structure Out where
  ret : Option Nat
  reg : Option Bytes
  burnt : Nat
  used : Nat
  err : Option String
  deriving Repr

/-- A machine state with one 64 KiB page and the given registers. -/
def mkSt (regs : Array (Nat × ByteArray)) (regUsage : Nat) (prepaid : Nat) : St :=
  { pages := #[⟨Array.replicate pageSize 0⟩], globals := #[], table := #[], tableMax := 0,
    elems := #[], datas := #[], stackRem := 0, gas := Gas.init prepaid,
    registers := regs, regUsage := regUsage }

/-- Run one host arm, collecting the return value, the register-0 payload, gas and the error. -/
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

/-- Run an arm whose arguments come from *memory* at `ptr`. -/
def runMem (arm : Vector Nat 3 → HM Unit) (data : Bytes) (ptr : Nat) (prepaid : Nat := 10 ^ 15) :
    Out :=
  let st := writeBytes (mkSt #[] 0 prepaid) ptr ⟨data.toArray⟩
  runHost (arm ⟨#[data.length, ptr, 0], by simp⟩) st

/-- Run an arm whose input comes from *register* `reg` (`value_len = u64::MAX`, `value_ptr = reg`),
which is how nearcore selects the register path in `get_memory_or_register`. -/
def runReg (arm : Vector Nat 3 → HM Unit) (data : Bytes) (reg : Nat) (prepaid : Nat := 10 ^ 15) :
    Out :=
  let st := mkSt #[(reg, ByteArray.mk data.toArray)] (data.length + 8) prepaid
  runHost (arm ⟨#[u64Bound - 1, reg, 0], by simp⟩) st

/-- Run `pairing_check`, whose arguments are `(value_len, value_ptr)` with no register. -/
def runPairMem (data : Bytes) (ptr : Nat) (prepaid : Nat := 10 ^ 15) : Out :=
  let st := writeBytes (mkSt #[] 0 prepaid) ptr ⟨data.toArray⟩
  runHost (hostPairingCheck ⟨#[data.length, ptr], by simp⟩) st

def runPairReg (data : Bytes) (reg : Nat) (prepaid : Nat := 10 ^ 15) : Out :=
  let st := mkSt #[(reg, ByteArray.mk data.toArray)] (data.length + 8) prepaid
  runHost (hostPairingCheck ⟨#[u64Bound - 1, reg], by simp⟩) st

def readCost (n : Nat) : Nat := C.readMemoryBase.gas + n * C.readMemoryByte.gas
def writeCost (n : Nat) : Nat := C.writeRegisterBase.gas + n * C.writeRegisterByte.gas
def regReadCost (n : Nat) : Nat := C.readRegisterBase.gas + n * C.readRegisterByte.gas

/-- `base + element·(len/itemSize) + read_memory(len)`, plus the write when the host writes. -/
def writerGas (base element itemSize outLen : Nat) (len : Nat) (wrote : Bool) : Nat :=
  base + element * (len / itemSize) + readCost len +
    (if wrote then writeCost outLen else 0)

def isBlsInvalid (r : Out) : Bool :=
  match r.err with
  | some e => e.startsWith "HostError(BLS12-381 invalid input:"
  | none => false

/-- Fixture hex helpers. -/
def unhex (s : String) : Bytes := (Bytes.ofHex? s).getD []
def hexOf (b : Bytes) : String := String.ofList (b.flatMap fun x =>
  let d := "0123456789abcdef".toList
  [d[x.toNat / 16]!, d[x.toNat % 16]!])

/-! ## Directed constants

The G1/G2 generators, an uncompressed 96/192-byte encoding of each, and a compressed 48/96-byte
encoding. These are the IETF `BLS12_381_G1`/`G2` points, so the encodings are independently known
and the "valid" branch does not depend on the Lean encoder. -/

/-- `G1` uncompressed: `x ‖ y`. -/
def g1GenBytes : Bytes :=
  unhex "17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb\
08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1"

/-- `G2` uncompressed: `x.c1 ‖ x.c0 ‖ y.c1 ‖ y.c0`. -/
def g2GenBytes : Bytes :=
  unhex "13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e\
024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8\
0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be\
0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801"

/-- Compressed `G1` generator (48 bytes, top bit set, sign bit clear). -/
def g1GenCompressed : Bytes :=
  unhex "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb"

/-- Compressed `G2` generator (96 bytes, top bit set, sign bit clear). -/
def g2GenCompressed : Bytes :=
  unhex "93e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e\
024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8"

/-! ## The per-host checks

Each block returns a list of `(description, Bool)`. A `Bool` is the *source-derived* expectation;
`TestBLS12381.lean` separately pins the payload verdict against `blst`. -/

/-- The eight `bls12381_impl!` hosts share one argument order and one branch structure, so one
generic checker covers them: a valid input (ret `0`, write, exact gas), a wrong length (error, no
write, base + element·⌊len/item⌋ + read burned), and a register-sourced input. -/
def writerChecks (arm : Vector Nat 3 → HM Unit) (name : String) (base element itemSize : Nat)
    (valid : Bytes) (outLen : Nat) : List (String × Bool) :=
  let ok := runMem arm valid 64
  let badLen := runMem arm (valid ++ [0]) 64
  let viaReg := runReg arm valid 5
  [ (s!"{name}: valid returns 0", ok.ret == some 0),
    (s!"{name}: valid writes {outLen} bytes", ok.reg.map List.length == some outLen),
    (s!"{name}: valid no error", ok.err == none),
    (s!"{name}: valid burnt gas", ok.burnt = writerGas base element itemSize outLen valid.length true),
    (s!"{name}: valid used gas", ok.used = writerGas base element itemSize outLen valid.length true),
    -- wrong length: base + element·⌊len/item⌋ + read charge, then BLS12381InvalidInput, no write
    (s!"{name}: wrong length errors", isBlsInvalid badLen),
    (s!"{name}: wrong length writes nothing", badLen.reg == none),
    (s!"{name}: wrong length burnt gas",
      badLen.burnt = base + element * ((itemSize + 1) / itemSize) + readCost (itemSize + 1)),
    -- register-sourced: `bls12381_impl!` divides the *operand* `value_len`, which is `u64::MAX`
    -- on this path, so `element * ⌊(2⁶⁴−1)/ITEM_SIZE⌋` overflows and nearcore raises
    -- `HostError(IntegerOverflow)` after paying only the base (`gas_counter.rs:290-302`).
    -- The Lean arm must reproduce that, not charge for the register's own length.
    (s!"{name}: register input overflows", viaReg.err == some "HostError(IntegerOverflow)"),
    (s!"{name}: register input burns base only", viaReg.burnt = base),
    (s!"{name}: register input returns nothing", viaReg.ret == none) ]

/-- `bls12381_p1_sum`: `(sign, p1)` pairs. -/
def p1SumChecks : List (String × Bool) :=
  let valid := [0] ++ g1GenBytes
  let invalidSign := [2] ++ g1GenBytes
  let offCurve := [0] ++ List.replicate 95 0 ++ [3]
  let r := runMem hostP1Sum valid 64
  let rs := runMem hostP1Sum invalidSign 64
  let rc := runMem hostP1Sum offCurve 64
  writerChecks hostP1Sum "p1_sum" p1SumBase.gas p1SumElement.gas 97 valid 96 ++
  [ ("p1_sum: sign 2 returns 1", rs.ret == some 1),
    ("p1_sum: sign 2 writes nothing", rs.reg == none),
    ("p1_sum: sign 2 no error", rs.err == none),
    ("p1_sum: sign 2 gas", rs.burnt = writerGas p1SumBase.gas p1SumElement.gas 97 96 97 false),
    ("p1_sum: off-curve returns 1", rc.ret == some 1),
    ("p1_sum: off-curve writes nothing", rc.reg == none) ]

/-- `bls12381_p2_sum`: `(sign, p2)` pairs. -/
def p2SumChecks : List (String × Bool) :=
  let valid := [0] ++ g2GenBytes
  let invalidSign := [1, 2].take 1 ++ g2GenBytes  -- sign = 1 is valid (negate); use 2 below
  let _ := invalidSign
  let badSign := [2] ++ g2GenBytes
  let r := runMem hostP2Sum valid 64
  let rb := runMem hostP2Sum badSign 64
  writerChecks hostP2Sum "p2_sum" p2SumBase.gas p2SumElement.gas 193 valid 192 ++
  [ ("p2_sum: sign 2 returns 1", rb.ret == some 1),
    ("p2_sum: sign 2 writes nothing", rb.reg == none),
    ("p2_sum: sign 2 no error", rb.err == none),
    ("p2_sum: sign 2 gas", rb.burnt = writerGas p2SumBase.gas p2SumElement.gas 193 192 193 false) ]

/-- `bls12381_g1_multiexp`: `(p1, 32-byte little-endian scalar)`. -/
def g1MultiexpChecks : List (String × Bool) :=
  let scalar : Bytes := List.replicate 31 0 ++ [2]
  let valid := g1GenBytes ++ scalar
  let r := runMem hostG1Multiexp valid 64
  writerChecks hostG1Multiexp "g1_multiexp" g1MultiexpBase.gas g1MultiexpElement.gas 128 valid 96 ++
  [ ("g1_multiexp: valid returns 0", r.ret == some 0),
    ("g1_multiexp: valid 96 bytes", r.reg.map List.length == some 96),
    -- 2·G1 is the point doubling of the generator: distinct from G1 itself
    ("g1_multiexp: 2G differs from G", r.reg != some g1GenBytes) ]

/-- `bls12381_g2_multiexp`: `(p2, 32-byte little-endian scalar)`. -/
def g2MultiexpChecks : List (String × Bool) :=
  let scalar : Bytes := List.replicate 31 0 ++ [2]
  let valid := g2GenBytes ++ scalar
  let r := runMem hostG2Multiexp valid 64
  writerChecks hostG2Multiexp "g2_multiexp" g2MultiexpBase.gas g2MultiexpElement.gas 224 valid 192 ++
  [ ("g2_multiexp: valid returns 0", r.ret == some 0),
    ("g2_multiexp: valid 192 bytes", r.reg.map List.length == some 192),
    ("g2_multiexp: 2G differs from G", r.reg != some g2GenBytes) ]

/-- `bls12381_p1_decompress`: compressed `G1` in, uncompressed out. -/
def p1DecompressChecks : List (String × Bool) :=
  let r := runMem hostP1Decompress g1GenCompressed 64
  writerChecks hostP1Decompress "p1_decompress" p1DecompressBase.gas p1DecompressElement.gas 48
      g1GenCompressed 96 ++
  [ ("p1_decompress: returns 0", r.ret == some 0),
    ("p1_decompress: 96 bytes out", r.reg.map List.length == some 96),
    -- the compressed bit must be set: a clear top bit is a `1` return, not an error
    ("p1_decompress: uncompressed input returns 1",
      (runMem hostP1Decompress (g1GenBytes.take 48) 64).ret == some 1),
    ("p1_decompress: uncompressed input no error",
      (runMem hostP1Decompress (g1GenBytes.take 48) 64).err == none) ]

/-- `bls12381_p2_decompress`: compressed `G2` in, uncompressed out. -/
def p2DecompressChecks : List (String × Bool) :=
  let r := runMem hostP2Decompress g2GenCompressed 64
  writerChecks hostP2Decompress "p2_decompress" p2DecompressBase.gas p2DecompressElement.gas 96
      g2GenCompressed 192 ++
  [ ("p2_decompress: returns 0", r.ret == some 0),
    ("p2_decompress: 192 bytes out", r.reg.map List.length == some 192) ]

/-- `bls12381_map_fp_to_g1`: one canonical `Fp` in, one 96-byte G1 point out. -/
def mapFpChecks : List (String × Bool) :=
  let one : Bytes := List.replicate 47 0 ++ [1]
  let r := runMem hostMapFpToG1 one 64
  writerChecks hostMapFpToG1 "map_fp_to_g1" mapFpToG1Base.gas mapFpToG1Element.gas 48 one 96 ++
  [ ("map_fp_to_g1: returns 0", r.ret == some 0),
    ("map_fp_to_g1: 96 bytes out", r.reg.map List.length == some 96),
    -- non-canonical Fp (= p) is a `1` return, not an error
    ("map_fp_to_g1: noncanonical returns 1",
      (runMem hostMapFpToG1 (BLS12381.Fp.toBE BLS12381.p) 64).ret == some 1),
    ("map_fp_to_g1: noncanonical no error",
      (runMem hostMapFpToG1 (BLS12381.Fp.toBE BLS12381.p) 64).err == none) ]

/-- `bls12381_map_fp2_to_g2`: one canonical `Fp2` in, one 192-byte G2 point out. -/
def mapFp2Checks : List (String × Bool) :=
  let one : Bytes := List.replicate 95 0 ++ [1]
  let r := runMem hostMapFp2ToG2 one 64
  writerChecks hostMapFp2ToG2 "map_fp2_to_g2" mapFp2ToG2Base.gas mapFp2ToG2Element.gas 96 one 192 ++
  [ ("map_fp2_to_g2: returns 0", r.ret == some 0),
    ("map_fp2_to_g2: 192 bytes out", r.reg.map List.length == some 192) ]

/-! ## `pairing_check`: its own order, no register, three-way verdict -/

/-- `pairing_check`'s gas: base + read_memory(len) + element·(data.len()/288). It never writes a
register and never pays the writer's base/element order. -/
def pairGas (len : Nat) : Nat :=
  pairingBase.gas + readCost len + pairingElement.gas * (len / 288)

def pairChecks : List (String × Bool) :=
  -- `e(G1, G2) ≠ 1`, so one valid pair is the `2` verdict
  let one := g1GenBytes ++ g2GenBytes
  let r1 := runPairMem one 64
  -- the empty product is `1`, so the `0` verdict, with base + read(0)
  let r0 := runPairMem [] 64
  -- a malformed length is a host error after base + read + per-element
  let rBad := runPairMem (one ++ [0]) 64
  -- register-sourced 1-byte input: 0 elements charged, so no overflow
  let rReg := runPairReg [0] 5
  -- register-sourced 577-byte input: 2 elements from the data length, then a length error
  let rReg577 := runPairReg (List.replicate 577 0) 5
  -- a non-trivial product that is one: `e(5·G1, G2) · e(−G1, 5·G2)`. Both pairs are finite, so
  -- every Miller-loop addition step contributes; the pinned nearcore returned `0` for exactly these
  -- bytes in a validator-produced chunk (docs/evidence/lean-chunk-completion/curve-host-fixtures,
  -- step `116.bls12381_pairing_check.pos.e(5a,b)e(-a,5b)`)
  let bilinear := unhex (
      "10e7791fb972fe014159aa33a98622da3cdc98ff707965e536d8636b5fcc5ac7a91a8c46e59a00dca575af0f18fb13dc" ++
      "16ba437edcc6551e30c10512367494bfb6b01cc6681e8a4c3cd2501832ab5c4abc40b4578b85cbaffbf0bcd70d67c6e2" ++
      "13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e" ++
      "024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8" ++
      "0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be" ++
      "0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801" ++
      "17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb" ++
      "114d1d6855d545a8aa7d76c8cf2e21f267816aef1db507c96655b9d5caac42364e6f38ba0ecb751bad54dcd6b939c2ca" ++
      "00fb837804dba8213329db46608b6c121d973363c1234a86dd183baff112709cf97096c5e9a1a770ee9d7dc641a894d6" ++
      "0411a5de6730ffece671a9f21d65028cc0f1102378de124562cb1ff49db6f004fcd14d683024b0548eff3d1468df2688" ++
      "093567b4228be17ee62d11a254edd041ee4b953bffb8b8c7f925bd6662b4298bac2822b446f5b5de3b893e1be5aa4986" ++
      "19b5e8f5d4a72f2b75811ac084a7f814317360bac52f6aab15eed416b4ef9938e0bdc4865cc2c4d0fd947e7c6925fd14")
  let rOne := runPairMem bilinear 64
  [ ("pairing: one pair returns 2", r1.ret == some 2),
    ("pairing: one pair writes no register", r1.reg == none),
    ("pairing: one pair no error", r1.err == none),
    ("pairing: one pair gas", r1.burnt = pairGas 288),
    ("pairing: empty returns 0", r0.ret == some 0),
    ("pairing: e(5a,b)·e(-a,5b) returns 0", rOne.ret == some 0),
    ("pairing: e(5a,b)·e(-a,5b) gas", rOne.burnt = pairGas 576),
    ("pairing: empty gas", r0.burnt = pairGas 0),
    ("pairing: malformed length errors", isBlsInvalid rBad),
    ("pairing: malformed length burnt gas", rBad.burnt = pairGas 289),
    -- the charge comes from the *register length*, not from the operand `value_len`. With a
    -- 1-byte register both readings give 0 elements, so the discriminating case is a register of
    -- 2·288+1 bytes: the data-length reading charges 2 elements, the operand reading divides
    -- u64::MAX and overflows.
    ("pairing: register 1 byte charges 0 elements", rReg.burnt = pairingBase.gas + regReadCost 1),
    ("pairing: register 1 byte errors on length", isBlsInvalid rReg),
    ("pairing: register 577 bytes charges 2 elements",
      rReg577.burnt = pairingBase.gas + regReadCost 577 + 2 * pairingElement.gas),
    ("pairing: register 577 bytes errors on length", isBlsInvalid rReg577) ]

/-! ## Argument order and stack discipline

`bls12381_impl!` reads `(value_len, value_ptr, register_id)` — value_len first. A transposition of
the first two would read `value_len = ptr` and `value_ptr = len`; the checks above pin the order
because a 97-byte valid input at ptr 64 succeeds only under the source order. This block makes the
distinction explicit with a deliberately transposed call. -/

def orderChecks : List (String × Bool) :=
  let valid := [0] ++ g1GenBytes
  let st := writeBytes (mkSt #[] 0 (10 ^ 15)) 64 ⟨valid.toArray⟩
  -- source order: len = 97, ptr = 64
  let ok := runHost (hostP1Sum ⟨#[valid.length, 64, 0], by simp⟩) st
  -- transposed: len = 64, ptr = 97 — reads 64 zero bytes at 97. The first byte (sign) is 0 and the
  -- remaining 63 bytes are not a 96-byte point, so the length check (64 % 97 = 64) fires first and
  -- the call is a BLS12381InvalidInput error rather than a decode failure.
  let tr := runHost (hostP1Sum ⟨#[64, valid.length, 0], by simp⟩) st
  [ ("order: source order succeeds", ok.ret == some 0),
    ("order: transposed call errors on length", isBlsInvalid tr),
    ("order: transposed call burns a different amount", tr.burnt != ok.burnt) ]

/-! ## The three-way verdict's discriminating middle branch

`pairing_check` returns `1` — not `2` — when a point fails to decode or a subgroup check. An
on-curve G1 point outside G1 (the `(0, ±2)` corner) is the clean discriminator at PV86. -/

def subgroupChecks : List (String × Bool) :=
  -- `(0, 2)` is on E but outside G1; at version 0 it decodes (blst reports POINT_NOT_IN_GROUP but
  -- `bls12381_pairing_check` deserializes with the *strict* check, so it must return 1)
  let x0 : Bytes := List.replicate 48 0
  let y2 : Bytes := List.replicate 47 0 ++ [2]
  let notInG1 := x0 ++ y2 ++ g2GenBytes
  let r := runPairMem notInG1 64
  [ ("pairing: G1 point outside G1 returns 1", r.ret == some 1),
    ("pairing: G1 point outside G1 no error", r.err == none),
    ("pairing: G1 point outside G1 writes no register", r.reg == none),
    -- a G2 point with the compressed bit set in the uncompressed slot is rejected by the
    -- `point_data[0] & 0x80 != 0` gate (`logic/bls12381.rs:349`), so the verdict is 1
    ("pairing: compressed G2 in uncompressed slot returns 1",
      (runPairMem (g1GenBytes ++ (g2GenCompressed ++ List.replicate 96 0)) 64).ret == some 1) ]

/-! ## `cryptoHostCall` dispatch

The arms above are reached here by direct call. `cryptoHostCall` is the table the successor call
loop would consult, so its dispatch has to be checked too: every one of the nine names must select
*some* arm (not `none`, which the loop reports as out of domain), and an unknown name must stay
`none` rather than silently matching a prefix. The selected arm's arity is the argument count
`popArgs` asks for, which differs for `pairing_check` (2) and the eight register writers (3). -/

def dispatchChecks : List (String × Bool) :=
  [ ("dispatch: p1_sum selects an arm", (cryptoHostCall "bls12381_p1_sum").isSome),
    ("dispatch: p2_sum selects an arm", (cryptoHostCall "bls12381_p2_sum").isSome),
    ("dispatch: g1_multiexp selects an arm", (cryptoHostCall "bls12381_g1_multiexp").isSome),
    ("dispatch: g2_multiexp selects an arm", (cryptoHostCall "bls12381_g2_multiexp").isSome),
    ("dispatch: map_fp_to_g1 selects an arm", (cryptoHostCall "bls12381_map_fp_to_g1").isSome),
    ("dispatch: map_fp2_to_g2 selects an arm", (cryptoHostCall "bls12381_map_fp2_to_g2").isSome),
    ("dispatch: p1_decompress selects an arm", (cryptoHostCall "bls12381_p1_decompress").isSome),
    ("dispatch: p2_decompress selects an arm", (cryptoHostCall "bls12381_p2_decompress").isSome),
    ("dispatch: pairing_check selects an arm", (cryptoHostCall "bls12381_pairing_check").isSome),
    ("dispatch: unknown name stays out of domain", (cryptoHostCall "bls12381_nope").isNone),
    ("dispatch: empty name stays out of domain", (cryptoHostCall "").isNone),
    -- alt_bn128 shares this table: its arithmetic lives in `NearSpecV3/AltBn128.lean` and its
    -- three arms are added to `cryptoHostCall` by the BN128 substream. The earlier assertion here
    -- said the opposite, but it was written before the two substreams met on this branch; the
    -- merged table does claim the three alt_bn128 names, so the check now states that.
    ("dispatch: alt_bn128_g1_multiexp selects an arm", (cryptoHostCall "alt_bn128_g1_multiexp").isSome),
    ("dispatch: alt_bn128_g1_sum selects an arm", (cryptoHostCall "alt_bn128_g1_sum").isSome),
    ("dispatch: alt_bn128_pairing_check selects an arm", (cryptoHostCall "alt_bn128_pairing_check").isSome),
    ("dispatch: alt_bn128 unknown suffix stays out of domain", (cryptoHostCall "alt_bn128_nope").isNone) ]

def allChecks : List (String × Bool) :=
  p1SumChecks ++ p2SumChecks ++ g1MultiexpChecks ++ g2MultiexpChecks ++
  p1DecompressChecks ++ p2DecompressChecks ++ mapFpChecks ++ mapFp2Checks ++
  pairChecks ++ orderChecks ++ subgroupChecks ++ dispatchChecks

def main : IO UInt32 := do
  let mut bad := 0
  for (name, ok) in allChecks do
    if !ok then
      bad := bad + 1
      IO.eprintln s!"BLS HOST FAIL: {name}"
  IO.println s!"bls12381 host cases: {allChecks.length} total, {bad} failures"
  return if bad = 0 then 0 else 1

end NearSpecV3.Wasm.BLSHostTest

def main (args : List String) : IO UInt32 := NearSpecV3.Wasm.BLSHostTest.main
