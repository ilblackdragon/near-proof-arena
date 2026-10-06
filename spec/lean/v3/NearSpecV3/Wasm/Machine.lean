import NearSpecV3.Wasm.Prepare
import NearSpecV3.Wasm.Numerics
import NearSpecV3.Wasm.TrieStore
/-!
# NEAR WASM (D3α): machine state, gas counter with profile, memory

Shared by `Host` (host functions) and `Exec` (instruction execution). Execution model:

A small-step machine over the flat operator arrays of `Prepared`. Everything NEAR-specific
follows `docs/research/near-wasm-boundary.md` §§2–5:

* **Gas.** The instrumented module's `remaining_gas` global (`g`) is decremented at finite-wasm
  points. When `charge > g`, `finite_wasm_gas(charge)` fails in `GasCounter::burn_gas`. Wasmtime call
  hooks synchronise `g` with the host counter: `CallingHost`/`ReturningFromWasm` burn `remaining − g`,
  and `CallingWasm`/`ReturningFromHost` set `g := remaining` (`wasmtime_runner/mod.rs:1042-1072`).
  `ReturningFromWasm` also fires on a trap (wasmtime `func.rs:1481`).
* **Stack budget.** Entry subtracts `stackCharge` from 262,144; exhaustion is
  `HostError(MemoryAccessViolation)` (`instrument_v3.rs:576-585`, `logic.rs:290-292`).
* **Memory.** `(memory 1024 2048)` whatever the contract declares, stored as 64 KiB pages that share
  one zero page until first written.
* **Traps** are named as nearcore's `FunctionCallError::WasmTrap` variants (`mod.rs:385-394`):
  table out of bounds is reported as `MemoryOutOfBounds`.

Totality: `run` is structurally recursive on an explicit step budget `fuel`. A run that exhausts the
fuel reports `unmodeled` and never a guessed outcome.
-/
namespace NearSpecV3.Wasm

def maxGasBurnt : Nat := 1000000000000000
def maxLengthReturnedData : Nat := 4194304
def u64Bound : Nat := 2 ^ 64

/-- An `ExtCosts` entry at PV86 (PV85 snapshot; compute overrides from `61/72/82.yaml`). `key` indexes
the profile slots of the costs whose compute differs from their gas (`profile.rs:144-175`). -/
structure Cost where
  gas : Nat
  compute : Nat := gas
  key : Option Nat := none
  deriving Inhabited

namespace C
def base : Cost := ⟨264768111, 264768111, none⟩
def contractLoadingBase : Cost := ⟨35445963, 35445963, none⟩
def contractLoadingBytes : Cost := ⟨1089295, 1089295, none⟩
def readMemoryBase : Cost := ⟨2609863200, 2609863200, none⟩
def readMemoryByte : Cost := ⟨3801333, 3801333, none⟩
def writeMemoryBase : Cost := ⟨2803794861, 2803794861, none⟩
def writeMemoryByte : Cost := ⟨2723772, 2723772, none⟩
def readRegisterBase : Cost := ⟨2517165186, 2517165186, none⟩
def readRegisterByte : Cost := ⟨98562, 98562, none⟩
def writeRegisterBase : Cost := ⟨2865522486, 2865522486, none⟩
def writeRegisterByte : Cost := ⟨3801564, 3801564, none⟩
def utf8DecodingBase : Cost := ⟨3111779061, 3111779061, none⟩
def utf8DecodingByte : Cost := ⟨291580479, 291580479, none⟩
def utf16DecodingBase : Cost := ⟨3543313050, 3543313050, none⟩
def utf16DecodingByte : Cost := ⟨163577493, 163577493, none⟩
def sha256Base : Cost := ⟨4540970250, 4540970250, none⟩
def sha256Byte : Cost := ⟨24117351, 24117351, none⟩
def keccak256Base : Cost := ⟨5879491275, 5879491275, none⟩
def keccak256Byte : Cost := ⟨21471105, 21471105, none⟩
def keccak512Base : Cost := ⟨5811388236, 5811388236, none⟩
def keccak512Byte : Cost := ⟨36649701, 36649701, none⟩
def ripemd160Base : Cost := ⟨853675086, 853675086, none⟩
def ripemd160Block : Cost := ⟨680107584, 680107584, none⟩
def logBase : Cost := ⟨3543313050, 3543313050, none⟩
def logByte : Cost := ⟨13198791, 13198791, none⟩
def storageWriteBase : Cost := ⟨64196736000, 200000000000, some 0⟩
def storageWriteKeyByte : Cost := ⟨70482867, 70482867, none⟩
def storageWriteValueByte : Cost := ⟨31018539, 31018539, none⟩
def storageWriteEvictedByte : Cost := ⟨32117307, 32117307, none⟩
def storageReadBase : Cost := ⟨56356845749, 159000000000, some 1⟩
def storageReadKeyByte : Cost := ⟨30952533, 10000000, some 2⟩
def storageReadValueByte : Cost := ⟨5611004, 2500000, some 3⟩
def storageLargeReadOverheadBase : Cost := ⟨1, 41000000000, some 4⟩
def storageLargeReadOverheadByte : Cost := ⟨1, 3111005, some 5⟩
def storageRemoveBase : Cost := ⟨53473030500, 200000000000, some 6⟩
def storageRemoveKeyByte : Cost := ⟨38220384, 38220384, none⟩
def storageRemoveRetValueByte : Cost := ⟨11531556, 11531556, none⟩
def storageHasKeyBase : Cost := ⟨54039896625, 158000000000, some 7⟩
def storageHasKeyByte : Cost := ⟨30790845, 10000000, some 8⟩
def touchingTrieNode : Cost := ⟨2280000000, 4000000000, some 9⟩
def readCachedTrieNode : Cost := ⟨2280000000, 4000000000, some 10⟩
def ed25519VerifyBase : Cost := ⟨210000000000, 210000000000, none⟩
def ed25519VerifyByte : Cost := ⟨9000000, 9000000, none⟩
def promiseAndBase : Cost := ⟨1465013400, 1465013400, none⟩
def promiseAndPerPromise : Cost := ⟨5452176, 5452176, none⟩
def promiseReturn : Cost := ⟨560152386, 560152386, none⟩
def validatorStakeBase : Cost := ⟨911834726400, 911834726400, none⟩
def validatorTotalStakeBase : Cost := ⟨911834726400, 911834726400, none⟩
def yieldCreateBase : Cost := ⟨153411779276, 153411779276, none⟩
def yieldCreateByte : Cost := ⟨15643988, 15643988, none⟩
def yieldCreateWithIdBase : Cost := ⟨290000000000, 290000000000, none⟩
def yieldResumeBase : Cost := ⟨1195627285210, 1195627285210, none⟩
def yieldResumeByte : Cost := ⟨47683715, 47683715, none⟩
/-- number of profile slots for costs whose compute ≠ gas -/
def nKeys : Nat := 11
end C
def pageSize : Nat := 65536
def maxTableElementsStore : Nat := 10000

inductive Val where
  | i32 (v : UInt32)
  | i64 (v : UInt64)
  | ref (r : Option Nat)
  deriving Repr, Inhabited

def Val.default : VT → Val
  | .i64 => .i64 0
  | .funcref | .externref => .ref none
  | _ => .i32 0

/-- `GasCounter` (`logic/gas_counter.rs:64-108`) plus the wasm-side `remaining_gas` global `g`. -/
structure Gas where
  burnt : Nat
  /-- gas reserved for promises (`promises_gas`) -/
  promises : Nat := 0
  prepaid : Nat
  /-- `fast_counter.gas_limit`: `min(max_gas_burnt, prepaid)`, lowered by promise gas -/
  limit : Nat
  g : Nat
  /-- profile (`ProfileDataV3`): burnt gas attributed to host (ext) costs and to actions -/
  host : Nat := 0
  action : Nat := 0
  /-- per-slot ext-cost gas for the costs with compute ≠ gas (`Cost.key`) -/
  special : Array Nat := Array.replicate C.nKeys 0
  /-- `send_action_compute_usage` -/
  sendCompute : Nat := 0
  deriving Inhabited

def Gas.init (prepaid : Nat) : Gas :=
  { burnt := 0, prepaid := prepaid, limit := Nat.min 1000000000000000 prepaid, g := 0 }

def specialCosts : Array Cost := #[C.storageWriteBase, C.storageReadBase, C.storageReadKeyByte,
  C.storageReadValueByte, C.storageLargeReadOverheadBase, C.storageLargeReadOverheadByte,
  C.storageRemoveBase, C.storageHasKeyBase, C.storageHasKeyByte, C.touchingTrieNode, C.readCachedTrieNode]

/-- `compute_outcome`'s compute usage (`logic.rs:131-154`, `profile.rs:98-175`). -/
def Gas.computeUsage (gs : Gas) : Nat :=
  let specialGas := gs.special.foldl (· + ·) 0
  -- `special[k]` absent = no gas recorded under key k (the array starts as `C.nKeys` zeros and is
  -- only updated in place), so `getD 0` is the meaning, not a fallback
  let ext := (gs.host - specialGas) + (specialCosts.zipIdx).foldl (fun acc (c, k) =>
    let v := gs.special[k]?.getD 0
    acc + (if v = 0 then 0 else v * c.compute / c.gas)) 0
  let wasm := gs.burnt - gs.action - gs.host
  ext + gs.sendCompute + wasm

def Gas.used (gs : Gas) : Nat := gs.burnt + gs.promises
def Gas.remaining (gs : Gas) : Nat := gs.prepaid - gs.used

def errGasExceeded : String := "HostError(GasExceeded)"
def errGasLimitExceeded : String := "HostError(GasLimitExceeded)"
def errIntOverflow : String := "HostError(IntegerOverflow)"
def errMAV : String := "HostError(MemoryAccessViolation)"
def trapStr (t : String) : String := s!"WasmTrap({t})"
def trapMem : String := trapStr "MemoryOutOfBounds"

/-- `process_gas_limit` (`gas_counter.rs:168-201`): clamp `burnt` to `min(prepaid, max_gas_burnt)` —
*not* to the promise-lowered `limit` (review F1) — and recompute `promises_gas`. -/
def processGasLimit (gs : Gas) (newBurnt newUsed : Nat) : Gas × Option String :=
  let hard := Nat.min gs.prepaid maxGasBurnt
  let b := Nat.min newBurnt hard
  let usedLim := Nat.min gs.prepaid newUsed
  ({ gs with burnt := b, promises := usedLim - b },
   some (if newBurnt > maxGasBurnt then errGasLimitExceeded else errGasExceeded))

/-- `GasCounter::burn_gas` (`gas_counter.rs:147-166`). -/
def burn (gs : Gas) (x : Nat) : Gas × Option String :=
  let nb := gs.burnt + x
  if nb ≥ u64Bound then (gs, some errIntOverflow)
  else if nb ≤ gs.limit then ({ gs with burnt := nb }, none)
  else processGasLimit gs nb ((nb + gs.promises) % u64Bound)

/-- `GasCounter::deduct_gas(burnt, used)` (`gas_counter.rs:118-140`); `b ≤ u`. -/
def deduct (gs : Gas) (b u : Nat) : Gas × Option String :=
  let pg := u - b
  let np := gs.promises + pg
  let nb := gs.burnt + b
  if np ≥ u64Bound ∨ nb ≥ u64Bound ∨ nb + np ≥ u64Bound then (gs, some errIntOverflow)
  else if nb ≤ maxGasBurnt ∧ nb + np ≤ gs.prepaid then
    let lim := if pg ≠ 0 then Nat.min maxGasBurnt (gs.prepaid - np) else gs.limit
    ({ gs with burnt := nb, promises := np, limit := lim }, none)
  else processGasLimit gs nb (nb + np)

/-- `GasCounter::pay_per` / `pay_base` (`gas_counter.rs:288-312`): `checked_mul` (no burn, no profile on
overflow), `burn_gas`, then the profile records the burnt delta (also on failure). -/
def payPer (gs : Gas) (c : Cost) (n : Nat) : Gas × Option String :=
  if c.gas * n ≥ u64Bound then (gs, some errIntOverflow)
  else
    let (gs', e) := burn gs (c.gas * n)
    let d := gs'.burnt - gs.burnt
    let gs' := { gs' with host := gs'.host + d,
                          special := match c.key with
                            | some k => gs'.special.modify k (· + d)
                            | none => gs'.special }
    (gs', e)

def payBase (gs : Gas) (c : Cost) : Gas × Option String := payPer gs c 1

/-- `GasCounter::pay_action_accumulated` (`gas_counter.rs:322-352`). -/
def payAction (gs : Gas) (burnGas burnCompute useGas : Nat) : Gas × Option String :=
  let (gs', e) := deduct gs burnGas useGas
  let d := gs'.burnt - gs.burnt
  let gs' := { gs' with action := gs'.action + d,
                        sendCompute := gs'.sendCompute + (if e.isNone then burnCompute else d) }
  (gs', e)

structure Label where
  target : Nat
  arity : Nat
  height : Nat
  isLoop : Bool
  deriving Inhabited

structure Frame where
  fn : Nat              -- index into `Prepared.funcs`
  pc : Nat
  locals : Array Val
  labels : List Label
  base : Nat
  deriving Inhabited

/-- `PromiseResult` of the call's context -/
inductive PRes where
  | notReady | ok (data : ByteArray) | failed
  deriving Inhabited

/-- The function call's `VMContext` (`logic/context.rs`) plus the `External` facts the D3α host
functions read. Defaults are the difftest harness's (`oracle/wasm-d3/src/main.rs`). -/
structure CallCtx where
  currentAccount : String := "alice.near"
  signer : String := "bob.near"
  signerPk : ByteArray := ⟨#[0, 1, 2]⟩
  predecessor : String := "bob.near"
  refundTo : String := "bob.near"
  input : ByteArray := .empty
  promiseResults : Array PRes := #[]
  blockHeight : Nat := 10
  blockTimestamp : Nat := 42
  epochHeight : Nat := 1
  accountBalance : Nat := 1000000000000000000000000
  accountLocked : Nat := 0
  storageUsage : Nat := 1000
  attachedDeposit : Nat := 0
  prepaidGas : Nat := 0
  randomSeed : ByteArray := ⟨Array.replicate 32 0⟩
  receivers : Array String := #[]
  /-- `External::chain_id` -/
  chainId : String := "test"
  /-- `External::validator_stake` (yocto); absent = 0 -/
  validators : Array (String × Nat) := #[]
  deriving Inhabited

/-- A `Promise` (`logic/logic.rs:197-200`): a receipt index or a joint (`promise_and`) set. -/
inductive PromiseV where
  | receipt (idx : Nat)
  | joint (idxs : Array Nat)
  deriving Inhabited

/-- One entry of the mock `External`'s action log (`logic/mocks/mock_external.rs`). In the mock,
receipt indices are action-log indices. `text` is the harness's canonical rendering. -/
structure MAct where
  text : String
  /-- receiver, for `CreateReceipt` and `YieldCreate` entries -/
  receiver : Option String := none
  /-- `(data_id, yield_id?)` for `YieldCreate` -/
  yieldCreate : Option (ByteArray × Option ByteArray) := none
  /-- `(receipt_index, keys)` for `DeterministicStateInit` (data entries set so far) -/
  stateInit : Option (Nat × Array ByteArray) := none
  deriving Inhabited

structure St where
  stack : Array Val := #[]
  frames : List Frame := []
  pages : Array ByteArray
  globals : Array Val
  table : Array (Option Nat)
  tableMax : Nat
  elems : Array (Array (Option Nat))
  datas : Array ByteArray
  stackRem : Nat
  gas : Gas
  ctx : CallCtx := {}
  /-- `ReturnData`: `none`, a value, or a receipt index (`promise_return`) -/
  ret : Option (ByteArray ⊕ Nat) := none
  /-- `current_account_balance` (yocto) -/
  balance : Nat := 0
  storageUsage : Nat := 0
  registers : Array (Nat × ByteArray) := #[]
  regUsage : Nat := 0
  logs : Array ByteArray := #[]
  totalLogLen : Nat := 0
  promises : Array PromiseV := #[]
  /-- mock `External`: storage map, action log, data-id counter -/
  trie : Array (ByteArray × ByteArray) := #[]
  actions : Array MAct := #[]
  dataCount : Nat := 0
  /-- trie-backed `External` (chunk replay): when set, storage goes through `TrieAccounting`
  instead of the mock `trie` map -/
  real : Option TTN.RealStore := none

inductive Res where
  | cont (s : St)
  | fin (s : St)
  | abort (s : St) (err : String)
  | unmodeled (why : String)

/-! ## Memory -/

def zeroPage : ByteArray := ⟨Array.replicate pageSize 0⟩

def memBytes (s : St) : Nat := s.pages.size * pageSize

def readByte (s : St) (a : Nat) : UInt8 :=
  match s.pages[a / pageSize]? with
  | some p => p.get! (a % pageSize)
  | none => 0

def writeByte (s : St) (a : Nat) (v : UInt8) : St :=
  { s with pages := s.pages.modify (a / pageSize) (fun p => p.set! (a % pageSize) v) }

def readLE (s : St) (a w : Nat) : Nat := Id.run do
  let mut v := 0
  for i in [0:w] do
    v := v + (readByte s (a + i)).toNat * 256 ^ i
  v

def writeLE (s : St) (a w v : Nat) : St := Id.run do
  let mut s := s
  for i in [0:w] do
    s := writeByte s (a + i) (UInt8.ofNat ((v / 256 ^ i) % 256))
  s

def readBytes (s : St) (a n : Nat) : ByteArray := Id.run do
  let mut d := ByteArray.empty
  for i in [0:n] do d := d.push (readByte s (a + i))
  d

def writeBytes (s : St) (a : Nat) (d : ByteArray) : St := Id.run do
  let mut s := s
  for h : i in [0:d.size] do s := writeByte s (a + i) (d[i]'(Membership.get_elem_helper h rfl))
  s

/-! ## Stack helpers -/

def popV (s : St) : Val × St := (s.stack.back?.getD (.i32 0), { s with stack := s.stack.pop })

def popN (s : St) : Nat × St :=
  match popV s with
  | (.i32 v, s') => (v.toNat, s')
  | (.i64 v, s') => (v.toNat, s')
  | (.ref _, s') => (0, s')

def popRef (s : St) : Option Nat × St :=
  match popV s with
  | (.ref r, s') => (r, s')
  | (_, s') => (none, s')

def pushV (s : St) (v : Val) : St := { s with stack := s.stack.push v }
def pushI32 (s : St) (v : Nat) : St := pushV s (.i32 (UInt32.ofNat v))
def pushI64 (s : St) (v : Nat) : St := pushV s (.i64 (UInt64.ofNat v))

def setFrame (s : St) (f : Frame) : St :=
  match s.frames with
  | _ :: fs => { s with frames := f :: fs }
  | [] => s

/-! ## Gas hooks -/

/-- `CallingHost` / `ReturningFromWasm`. A failure here would be a `LinkError` (`mod.rs:369-420`),
impossible while `prepaid ≤ max_gas_burnt` (requirement H5); it is reported as unmodeled. -/
def sync (s : St) : Except String St :=
  let burned := s.gas.remaining - s.gas.g
  if burned = 0 then .ok s
  else match burn s.gas burned with
    | (gs, none) => .ok { s with gas := gs }
    | (_, some _) => .error "gas hook failure (LinkError path, H5)"

/-- One instrumentation point; `count` is the top operand for linear fees. -/
def charge (s : St) (fee : Fee) (count : Nat) : Res :=
  let amt := count * fee.l + fee.c
  if amt ≥ u64Bound then
    -- 128-bit overflow check → finite_wasm_gas_exhausted: burn all remaining, IntegerOverflow
    match sync s with
    | .error e => .unmodeled e
    | .ok s =>
      match burn s.gas s.gas.remaining with
      | (gs, none) => .abort { s with gas := gs } errIntOverflow
      | (gs, some e) => .abort { s with gas := gs } e
  else if amt > s.gas.g then
    match sync s with
    | .error e => .unmodeled e
    | .ok s =>
      match burn s.gas amt with
      | (gs, some e) => .abort { s with gas := gs } e
      | (gs, none) => .unmodeled s!"finite_wasm_gas({amt}) did not fail ({gs.burnt})"
  else .cont { s with gas := { s.gas with g := s.gas.g - amt } }
