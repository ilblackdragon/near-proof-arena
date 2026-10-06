import NearSpecV3.Wasm.Machine
import NearSpecV3.Wasm.Crypto
/-!
# NEAR WASM (D3α): host functions

Each host function is a transliteration of its live implementation in
`runtime/near-vm-runner/src/wasmtime_runner/logic.rs` (PV86), in nearcore's order of charges and
checks: gas is paid **before** bounds checks; every error aborts with the gas burnt so far. They run in
`HM = EStateM String St`, so an error carries the state reached.

`External` is the mock of `logic/mocks/mock_external.rs` (in-memory storage, no trie-node charges,
receipt index = action-log index). `RuntimeD3` will instantiate the real trie-backed `External`;
everything above `External` is shared.

D3α scope: every host function except the curve ones (`alt_bn128_*`, `bls12381_*`, `ecrecover`,
`p256_verify`: out of domain) and, pending D1's merge, `ed25519_verify`. The global-contract,
deterministic-state-init and gas-key actions report `unmodeled` until their fee formulas are modelled.
-/
namespace NearSpecV3.Wasm

abbrev HM := EStateM String St

def hErr {α} (e : String) : HM α := throw s!"HostError({e})"

/-- run a gas operation; on failure keep the updated counter and abort -/
def withGas (f : Gas → Gas × Option String) : HM Unit := do
  let (gs, e) := f (← get).gas
  modify fun s => { s with gas := gs }
  match e with
  | some e => throw e
  | none => pure ()

def payBaseH (c : Cost) : HM Unit := withGas (payBase · c)
def payPerH (c : Cost) (n : Nat) : HM Unit := withGas (payPer · c n)
def payActionH (b bc u : Nat) : HM Unit := withGas (payAction · b bc u)
def burnH (x : Nat) : HM Unit := withGas (burn · x)

/-! ## Memory and registers (`logic.rs:85-180`, `logic/vmstate.rs:137-262`) -/

def readMemH (ptr len : Nat) : HM ByteArray := do
  payBaseH C.readMemoryBase
  payPerH C.readMemoryByte len
  let s ← get
  if ptr + len > memBytes s then hErr "MemoryAccessViolation"
  pure (readBytes s ptr len)

def writeMemH (ptr : Nat) (d : ByteArray) : HM Unit := do
  payBaseH C.writeMemoryBase
  payPerH C.writeMemoryByte d.size
  let s ← get
  if ptr + d.size > memBytes s then hErr "MemoryAccessViolation"
  set (writeBytes s ptr d)

def regGetH (id : Nat) : HM ByteArray := do
  match (← get).registers.find? (·.1 = id) with
  | some (_, d) =>
    payBaseH C.readRegisterBase
    payPerH C.readRegisterByte d.size
    pure d
  | none => hErr s!"InvalidRegisterId \{ register_id: {id} }"

def maxRegisterSize : Nat := 104857600
def maxNumberRegisters : Nat := 100
def registersMemoryLimit : Nat := 1073741824

/-- `Registers::set_impl` (`vmstate.rs:197-262`), including the protocol bug that a full register
file rejects even a replacement. -/
def regSetH (id : Nat) (d : ByteArray) (chargeBytes : Bool := true) : HM Unit := do
  payBaseH C.writeRegisterBase
  if chargeBytes then payPerH C.writeRegisterByte d.size
  let s ← get
  if d.size > maxRegisterSize then hErr "MemoryAccessViolation"
  if s.registers.size ≥ maxNumberRegisters then hErr "MemoryAccessViolation"
  let old := match s.registers.find? (·.1 = id) with
    | some (_, o) => o.size + 8
    | none => 0
  let usage := s.regUsage - old + (d.size + 8)
  if usage > registersMemoryLimit then hErr "MemoryAccessViolation"
  let regs := match s.registers.findIdx? (·.1 = id) with
    | some i => s.registers.set! i (id, d)
    | none => s.registers.push (id, d)
  set { s with registers := regs, regUsage := usage }

/-- `get_memory_or_register` -/
def memOrRegH (ptr len : Nat) : HM ByteArray :=
  if len = u64Bound - 1 then regGetH ptr else readMemH ptr len

def leNat (d : ByteArray) : Nat := (List.range d.size).foldl (fun a i => a + d[i]!.toNat * 256 ^ i) 0
def natLE (n w : Nat) : ByteArray := ⟨(Array.range w).map fun i => UInt8.ofNat ((n / 256 ^ i) % 256)⟩

def getU128H (ptr : Nat) : HM Nat := do pure (leNat (← readMemH ptr 16))
def setU128H (ptr v : Nat) : HM Unit := writeMemH ptr (natLE v 16)

/-! ## Strings and logs (`logic.rs:392-508`, `logic/logic.rs:95-124`) -/

def maxNumberLogs : Nat := 100
def maxTotalLogLength : Nat := 16384

def logLenExceeded {α} (add : Nat) : HM α := do
  hErr s!"TotalLogLengthExceeded \{ length: {(← get).totalLogLen + add}, limit: {maxTotalLogLength} }"

def utf8H (len ptr : Nat) : HM String := do
  payBaseH C.utf8DecodingBase
  let maxLen := maxTotalLogLength - (← get).totalLogLen
  let buf ← if len ≠ u64Bound - 1 then do
      if len > maxLen then logLenExceeded len
      readMemH ptr len
    else do
      let mut b := ByteArray.empty
      let mut done := false
      for i in [0:maxLen + 1] do
        if done then break
        payBaseH C.readMemoryBase
        payPerH C.readMemoryByte 1
        let s ← get
        if ptr + i ≥ memBytes s then hErr "MemoryAccessViolation"
        let el := readByte s (ptr + i)
        if el = 0 then done := true
        else
          if i = maxLen then logLenExceeded (maxLen + 1)
          b := b.push el
      pure b
  payPerH C.utf8DecodingByte buf.size
  match String.fromUTF8? buf with
  | some str => pure str
  | none => hErr "BadUTF8"

/-- UTF-16LE → String (`char::decode_utf16`; unpaired surrogates are an error). -/
def decodeUtf16 (d : ByteArray) : Option String := Id.run do
  let n := d.size / 2
  let u (i : Nat) : Nat := d[2 * i]!.toNat + 256 * d[2 * i + 1]!.toNat
  let mut out : String := ""
  let mut i := 0
  for _ in [0:n] do
    if i ≥ n then break
    let c := u i
    if 0xD800 ≤ c ∧ c ≤ 0xDBFF then
      if i + 1 < n ∧ 0xDC00 ≤ u (i + 1) ∧ u (i + 1) ≤ 0xDFFF then
        out := out.push (Char.ofNat (0x10000 + (c - 0xD800) * 0x400 + (u (i + 1) - 0xDC00)))
        i := i + 2
      else return none
    else if 0xDC00 ≤ c ∧ c ≤ 0xDFFF then return none
    else
      out := out.push (Char.ofNat c)
      i := i + 1
  return some out

def utf16H (len ptr : Nat) : HM String := do
  payBaseH C.utf16DecodingBase
  let maxLen := maxTotalLogLength - (← get).totalLogLen
  let (len, d) ← if len = u64Bound - 1 then do
      let mut l := 0
      let mut fin := false
      for _ in [0:maxLen / 2 + 2] do
        if fin then break
        let w ← readMemH (ptr + l) 2
        if w[0]! = 0 ∧ w[1]! = 0 then fin := true
        else
          l := l + 2
          if l > maxLen then logLenExceeded l
      let s ← get
      if ptr + l > memBytes s then hErr "MemoryAccessViolation"
      pure (l, readBytes s ptr l)
    else do
      let d ← readMemH ptr len
      pure (len, d)
  if d.size % 2 ≠ 0 then hErr "BadUTF16"
  if len > maxLen then logLenExceeded len
  payPerH C.utf16DecodingByte len
  match decodeUtf16 d with
  | some str => pure str
  | none => hErr "BadUTF16"

def checkCanLogH : HM Unit := do
  if (← get).logs.size ≥ maxNumberLogs then hErr s!"NumberOfLogsExceeded \{ limit: {maxNumberLogs} }"

/-- `checked_push_log`: the total is updated *before* the limit check (so the error reports it twice). -/
def pushLogH (msg : String) : HM Unit := do
  let b := msg.toUTF8
  let s ← get
  let t := s.totalLogLen + b.size
  set { s with totalLogLen := t }
  if t > maxTotalLogLength then logLenExceeded b.size
  modify fun s => { s with logs := s.logs.push b }

/-- Rust `{:?}` of a `String` for the ASCII range (`str::escape_debug`); non-ASCII is kept as is. -/
def rustDebugStr (str : String) : String :=
  "\"" ++ str.foldl (fun acc c =>
    acc ++ (match c with
      | '\t' => "\\t" | '\r' => "\\r" | '\n' => "\\n" | '\\' => "\\\\" | '"' => "\\\""
      | c => if c.toNat < 0x20 ∨ c.toNat = 0x7F then s!"\\u\{{(Nat.toDigits 16 c.toNat).asString}}"
             else c.toString)) "" ++ "\""

def guestPanic {α} (msg : String) : HM α := hErr s!"GuestPanic \{ panic_msg: {rustDebugStr msg} }"

/-! ## Account ids, public keys -/

/-- `near-account-id` 2.0.0 `validate` (strict, `account_id_validity_rules_version = 2`). -/
def validAccountId (s : String) : Bool :=
  let b := s.toUTF8
  if b.size < 2 ∨ b.size > 64 then false
  else Id.run do
    let mut lastSep := true
    for c in b.toList do
      let isSep := c = 0x2D ∨ c = 0x5F ∨ c = 0x2E
      let ok := (0x61 ≤ c ∧ c ≤ 0x7A) ∨ (0x30 ≤ c ∧ c ≤ 0x39) ∨ isSep
      if !ok then return false
      if isSep ∧ lastSep then return false
      lastSep := isSep
    return !lastSep

def readAccountIdH (len ptr : Nat) : HM String := do
  let buf ← memOrRegH ptr len
  payBaseH C.utf8DecodingBase
  payPerH C.utf8DecodingByte buf.size
  match String.fromUTF8? buf with
  | none => hErr "BadUTF8"
  | some str => if validAccountId str then pure str else hErr "InvalidAccountId"

/-- `PublicKeyBuffer` (`logic/logic.rs:233-259`): borsh `PublicKey` (ED25519 32 B, SECP256K1 64 B,
ML-DSA-65 1,952 B; the mock enables post-quantum keys), no trailing bytes. -/
def pkValid (d : ByteArray) : Bool :=
  d.size ≥ 1 ∧ ((d[0]! = 0 ∧ d.size = 33) ∨ (d[0]! = 1 ∧ d.size = 65) ∨ (d[0]! = 2 ∧ d.size = 1953))

def hexStr (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList
  b.foldl (fun acc x => acc.push (d[x.toNat / 16]!) |>.push (d[x.toNat % 16]!)) ""

/-! ## Mock `External` (`logic/mocks/mock_external.rs`) -/

def trieGet (s : St) (k : ByteArray) : Option ByteArray := (s.trie.find? (·.1 == k)).map (·.2)

def pushAction (a : MAct) : HM Nat := do
  let s ← get
  set { s with actions := s.actions.push a }
  pure s.actions.size

def receiptReceiver (s : St) (idx : Nat) : String := (s.actions[idx]?.bind (·.receiver)).getD ""

def maxPromises : Nat := 1024
def maxInputDataDependencies : Nat := 128

def pushPromiseH (p : PromiseV) : HM Nat := do
  let s ← get
  set { s with promises := s.promises.push p }
  if s.promises.size + 1 > maxPromises then
    hErr s!"NumberPromisesExceeded \{ number_of_promises: {s.promises.size + 1}, limit: {maxPromises} }"
  pure s.promises.size

/-- `promise_idx_to_receipt_idx_with_sir` -/
def promiseReceiptH (idx : Nat) : HM (Nat × Bool) := do
  let s ← get
  match s.promises[idx]? with
  | none => hErr s!"InvalidPromiseIndex \{ promise_idx: {idx} }"
  | some (.joint _) => hErr "CannotAppendActionToJointPromise"
  | some (.receipt r) => pure (r, receiptReceiver s r = s.ctx.currentAccount)

/-! ## Fees (PV86 `RuntimeFeesConfig`) -/

structure Fee3 where
  sendSir : Nat
  sendNotSir : Nat
  exec : Nat

def Fee3.send (f : Fee3) (sir : Bool) : Nat := if sir then f.sendSir else f.sendNotSir

namespace F
def newActionReceipt : Fee3 := ⟨108059500000, 108059500000, 108059500000⟩
def newDataReceiptBase : Fee3 := ⟨36486732312, 36486732312, 36486732312⟩
def newDataReceiptByte : Fee3 := ⟨17212011, 47683715, 17212011⟩
def createAccount : Fee3 := ⟨500000000000, 500000000000, 7200000000000⟩
def deployContract : Fee3 := ⟨184765750000, 184765750000, 184765750000⟩
def deployContractByte : Fee3 := ⟨6812999, 47683715, 64572944⟩
def functionCall : Fee3 := ⟨200000000000, 200000000000, 780000000000⟩
def functionCallByte : Fee3 := ⟨2235934, 47683715, 2235934⟩
def transfer : Fee3 := ⟨115123062500, 115123062500, 115123062500⟩
def stake : Fee3 := ⟨141715687500, 141715687500, 102217625000⟩
def addFullAccessKey : Fee3 := ⟨101765125000, 101765125000, 101765125000⟩
def addFunctionCallKey : Fee3 := ⟨102217625000, 102217625000, 102217625000⟩
def addFunctionCallKeyByte : Fee3 := ⟨1925331, 47683715, 1925331⟩
def deleteKey : Fee3 := ⟨94946625000, 94946625000, 94946625000⟩
def deleteAccount : Fee3 := ⟨147489000000, 147489000000, 147489000000⟩
end F

/-- `pay_action_base`: burn send, reserve send + exec (send compute = gas for all PV86 send fees) -/
def payActionBaseH (f : Fee3) (sir : Bool) : HM Unit :=
  payActionH (f.send sir) (f.send sir) (f.send sir + f.exec)

def payActionPerByteH (f : Fee3) (n : Nat) (sir : Bool) : HM Unit := do
  let b := f.send sir * n
  let u := b + f.exec * n
  if b ≥ u64Bound ∨ f.exec * n ≥ u64Bound ∨ u ≥ u64Bound then hErr "IntegerOverflow"
  payActionH b b u

/-- `pay_gas_for_new_receipt` -/
def payNewReceiptH (sir : Bool) (deps : Array Bool) : HM Unit := do
  let burn := F.newActionReceipt.send sir +
    deps.foldl (fun a d => a + F.newDataReceiptBase.send d + F.newDataReceiptBase.exec) 0
  payActionH burn burn (F.newActionReceipt.exec + burn)

/-- account-type extra fees of `transfer_{send,exec}_fee` (`core/parameters/src/cost.rs:722-777`) -/
def isHexLower (s : String) : Bool := s.toList.all fun c => ('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f')
def accountType (a : String) : Nat :=   -- 0 named, 1 eth-implicit, 2 near-implicit, 3 deterministic
  if a.length = 42 ∧ a.startsWith "0x" ∧ isHexLower (a.drop 2).toString then 1
  else if a.length = 64 ∧ isHexLower a then 2
  else if a.length = 42 ∧ a.startsWith "0s" ∧ isHexLower (a.drop 2).toString then 3
  else 0

def transferFees (sir : Bool) (recv : String) : Nat × Nat :=
  let t := accountType recv
  let send := F.transfer.send sir + (if t = 0 then 0 else F.createAccount.send sir) +
    (if t = 2 then F.addFullAccessKey.send sir else 0)
  let exec := F.transfer.exec + (if t = 0 then 0 else F.createAccount.exec) +
    (if t = 2 then F.addFullAccessKey.exec else 0)
  (send, exec)

def deductBalanceH (amount : Nat) : HM Unit := do
  let s ← get
  if amount > s.balance then hErr "BalanceExceeded"
  set { s with balance := s.balance - amount }

def splitMethodNames (d : ByteArray) : Option (Array ByteArray) :=
  if d.size = 0 then some #[]
  else
    let parts := (d.toList.splitOn 0x2C).map (fun l => ByteArray.mk l.toArray)
    if parts.any (·.size = 0) then none else some parts.toArray

def maxContractSize : Nat := 4194304
def maxLengthStorageKey : Nat := 2048
def maxLengthStorageValue : Nat := 4194304
def maxYieldPayloadSize : Nat := 1024
def numExtraBytesRecord : Nat := 40

/-! ## The host functions -/

def popArgs (n : Nat) : HM (Array Nat) := do
  let mut out := #[]
  for _ in [0:n] do
    let (v, s) := popN (← get)
    set s
    out := out.push v
  pure out.reverse

def pushRet (v : Nat) (is64 : Bool := true) : HM Unit :=
  modify fun s => if is64 then pushI64 s v else pushI32 s v

def dataId (n : Nat) : ByteArray := Crypto.sha256 (natLE n 8)

def hashHost (cBase cByte : Cost) (h : ByteArray → ByteArray) (len ptr reg : Nat) : HM Unit := do
  payBaseH cBase
  let v ← memOrRegH ptr len
  payPerH cByte v.size
  regSetH reg (h v)

def functionCallActionH (idx mlen mptr alen aptr amountPtr gas weight : Nat) : HM Unit := do
  payBaseH C.base
  let amount ← getU128H amountPtr
  let m ← memOrRegH mptr mlen
  if m.size = 0 then hErr "EmptyMethodName"
  let a ← memOrRegH aptr alen
  let (r, sir) ← promiseReceiptH idx
  let nb := m.size + a.size
  payActionBaseH F.functionCall sir
  payActionPerByteH F.functionCallByte nb sir
  withGas (deduct · 0 gas)
  let s ← get
  -- one_yocto_on_promise
  if amount = 1 ∧ s.balance = 0 then pure () else deductBalanceH amount
  let _ ← pushAction { text := s!"FC@{r}:{hexStr m}:{hexStr a}:{amount}:{gas}:{weight}" }

/-- Dispatch. `none` = not a D3α host function handled here. -/
def hostCall (name : String) : Option (HM Unit) :=
  match name with
  -- registers
  | "read_register" => some do
    let a ← popArgs 2
    payBaseH C.base
    let d ← regGetH a[0]!
    writeMemH a[1]! d
  | "register_len" => some do
    let a ← popArgs 1
    payBaseH C.base
    pushRet (((← get).registers.find? (·.1 = a[0]!)).map (·.2.size) |>.getD (u64Bound - 1))
  | "write_register" => some do
    let a ← popArgs 3
    payBaseH C.base
    let d ← readMemH a[2]! a[1]!
    regSetH a[0]! d
  -- context
  | "current_account_id" => some do
    let a ← popArgs 1; payBaseH C.base; regSetH a[0]! (← get).ctx.currentAccount.toUTF8
  | "signer_account_id" => some do
    let a ← popArgs 1; payBaseH C.base; regSetH a[0]! (← get).ctx.signer.toUTF8
  | "signer_account_pk" => some do
    let a ← popArgs 1; payBaseH C.base; regSetH a[0]! (← get).ctx.signerPk
  | "predecessor_account_id" => some do
    let a ← popArgs 1; payBaseH C.base; regSetH a[0]! (← get).ctx.predecessor.toUTF8
  | "refund_to_account_id" => some do
    let a ← popArgs 1; payBaseH C.base; regSetH a[0]! (← get).ctx.refundTo.toUTF8
  | "chain_id" => some do
    let a ← popArgs 1; payBaseH C.base; regSetH a[0]! (← get).ctx.chainId.toUTF8
  | "input" => some do
    let a ← popArgs 1; payBaseH C.base; regSetH a[0]! (← get).ctx.input (chargeBytes := false)
  | "random_seed" => some do
    let a ← popArgs 1; payBaseH C.base; regSetH a[0]! (← get).ctx.randomSeed
  | "block_index" => some do payBaseH C.base; pushRet (← get).ctx.blockHeight
  | "block_timestamp" => some do payBaseH C.base; pushRet (← get).ctx.blockTimestamp
  | "epoch_height" => some do payBaseH C.base; pushRet (← get).ctx.epochHeight
  | "storage_usage" => some do payBaseH C.base; pushRet (← get).storageUsage
  | "prepaid_gas" => some do payBaseH C.base; pushRet (← get).ctx.prepaidGas
  | "used_gas" => some do payBaseH C.base; pushRet (← get).gas.used
  | "account_balance" => some do
    let a ← popArgs 1; payBaseH C.base; setU128H a[0]! (← get).balance
  | "account_locked_balance" => some do
    let a ← popArgs 1; payBaseH C.base; setU128H a[0]! (← get).ctx.accountLocked
  | "attached_deposit" => some do
    let a ← popArgs 1; payBaseH C.base; setU128H a[0]! (← get).ctx.attachedDeposit
  | "current_contract_code" => some do
    let _ ← popArgs 1; payBaseH C.base; pushRet 0   -- AccountContract::None in the harness context
  | "validator_stake" => some do
    let a ← popArgs 3
    payBaseH C.base
    let acct ← readAccountIdH a[0]! a[1]!
    payBaseH C.validatorStakeBase
    let st := (((← get).ctx.validators.find? (·.1 = acct)).map (·.2)).getD 0
    setU128H a[2]! st
  | "validator_total_stake" => some do
    let a ← popArgs 1
    payBaseH C.base
    payBaseH C.validatorTotalStakeBase
    setU128H a[0]! ((← get).ctx.validators.foldl (fun acc v => acc + v.2) 0)
  -- hashes
  | "sha256" => some do
    let a ← popArgs 3; hashHost C.sha256Base C.sha256Byte Crypto.sha256 a[0]! a[1]! a[2]!
  | "keccak256" => some do
    let a ← popArgs 3; hashHost C.keccak256Base C.keccak256Byte Crypto.keccak256 a[0]! a[1]! a[2]!
  | "keccak512" => some do
    let a ← popArgs 3; hashHost C.keccak512Base C.keccak512Byte Crypto.keccak512 a[0]! a[1]! a[2]!
  | "ripemd160" => some do
    let a ← popArgs 3
    payBaseH C.ripemd160Base
    let v ← memOrRegH a[1]! a[0]!
    payPerH C.ripemd160Block ((v.size + 8) / 64 + 1)
    regSetH a[2]! (Crypto.ripemd160 v)
  -- logs and panics
  | "value_return" => some do
    let a ← popArgs 2
    payBaseH C.base
    let v ← memOrRegH a[1]! a[0]!
    if v.size > maxLengthReturnedData then
      hErr s!"ReturnedValueLengthExceeded \{ length: {v.size}, limit: {maxLengthReturnedData} }"
    let s ← get
    let burn := s.ctx.receivers.foldl (fun acc r =>
      let sir := r = s.ctx.currentAccount
      acc + (F.newDataReceiptByte.send sir + F.newDataReceiptByte.exec) * v.size) 0
    if burn ≥ u64Bound then hErr "IntegerOverflow"
    payActionH burn burn burn
    modify fun s => { s with ret := some (.inl v) }
  | "panic" => some do payBaseH C.base; guestPanic "explicit guest panic"
  | "panic_utf8" => some do
    let a ← popArgs 2; payBaseH C.base; guestPanic (← utf8H a[0]! a[1]!)
  | "log_utf8" => some do
    let a ← popArgs 2
    payBaseH C.base
    checkCanLogH
    let m ← utf8H a[0]! a[1]!
    payBaseH C.logBase
    payPerH C.logByte m.utf8ByteSize
    pushLogH m
  | "log_utf16" => some do
    let a ← popArgs 2
    payBaseH C.base
    checkCanLogH
    let m ← utf16H a[0]! a[1]!
    payBaseH C.logBase
    payPerH C.logByte m.utf8ByteSize
    pushLogH m
  | "abort" => some do
    let a ← popArgs 4
    payBaseH C.base
    let (mp, fp, line, col) := (a[0]! % 2 ^ 32, a[1]! % 2 ^ 32, a[2]! % 2 ^ 32, a[3]! % 2 ^ 32)
    if mp < 4 ∨ fp < 4 then hErr "BadUTF16"
    checkCanLogH
    let ml := leNat (← readMemH (mp - 4) 4)
    let fl := leNat (← readMemH (fp - 4) 4)
    let msg ← utf16H ml mp
    let file ← utf16H fl fp
    let message := s!"{msg}, filename: \"{file}\" line: {line} col: {col}"
    payBaseH C.logBase
    payPerH C.logByte message.utf8ByteSize
    pushLogH s!"ABORT: {message}"
    guestPanic message
  | "gas" => some do
    let a ← popArgs 1
    burnH (a[0]! * 822756)
  -- storage (mock External: no trie-node charges, recorded size 0)
  | "storage_write" => some do
    let a ← popArgs 5
    payBaseH C.base
    payBaseH C.storageWriteBase
    let k ← memOrRegH a[1]! a[0]!
    if k.size > maxLengthStorageKey then
      hErr s!"KeyLengthExceeded \{ length: {k.size}, limit: {maxLengthStorageKey} }"
    let v ← memOrRegH a[3]! a[2]!
    if v.size > maxLengthStorageValue then
      hErr s!"ValueLengthExceeded \{ length: {v.size}, limit: {maxLengthStorageValue} }"
    payPerH C.storageWriteKeyByte k.size
    payPerH C.storageWriteValueByte v.size
    let s ← get
    let old := trieGet s k
    let trie := match s.trie.findIdx? (·.1 == k) with
      | some i => s.trie.set! i (k, v)
      | none => s.trie.push (k, v)
    set { s with trie := trie }
    match old with
    | some o =>
      modify fun s => { s with storageUsage := s.storageUsage - o.size + v.size }
      regSetH a[4]! o
      pushRet 1
    | none =>
      modify fun s => { s with storageUsage := s.storageUsage + v.size + k.size + numExtraBytesRecord }
      pushRet 0
  | "storage_read" => some do
    let a ← popArgs 3
    payBaseH C.base
    payBaseH C.storageReadBase
    let k ← memOrRegH a[1]! a[0]!
    if k.size > maxLengthStorageKey then
      hErr s!"KeyLengthExceeded \{ length: {k.size}, limit: {maxLengthStorageKey} }"
    payPerH C.storageReadKeyByte k.size
    match trieGet (← get) k with
    | some v =>
      payPerH C.storageReadValueByte v.size
      if v.size > 4000 then
        payBaseH C.storageLargeReadOverheadBase
        payPerH C.storageLargeReadOverheadByte v.size
      regSetH a[2]! v
      pushRet 1
    | none => pushRet 0
  | "storage_remove" => some do
    let a ← popArgs 3
    payBaseH C.base
    payBaseH C.storageRemoveBase
    let k ← memOrRegH a[1]! a[0]!
    if k.size > maxLengthStorageKey then
      hErr s!"KeyLengthExceeded \{ length: {k.size}, limit: {maxLengthStorageKey} }"
    payPerH C.storageRemoveKeyByte k.size
    let s ← get
    match trieGet s k with
    | some v =>
      set { s with trie := s.trie.filter (·.1 != k),
                   storageUsage := s.storageUsage - (v.size + k.size + numExtraBytesRecord) }
      regSetH a[2]! v
      pushRet 1
    | none => pushRet 0
  | "storage_has_key" => some do
    let a ← popArgs 2
    payBaseH C.base
    payBaseH C.storageHasKeyBase
    let k ← memOrRegH a[1]! a[0]!
    if k.size > maxLengthStorageKey then
      hErr s!"KeyLengthExceeded \{ length: {k.size}, limit: {maxLengthStorageKey} }"
    payPerH C.storageHasKeyByte k.size
    pushRet (if (trieGet (← get) k).isSome then 1 else 0)
  | "storage_iter_prefix" => some do
    let _ ← popArgs 2; hErr "Deprecated { method_name: \"storage_iter_prefix\" }"
  | "storage_iter_range" => some do
    let _ ← popArgs 4; hErr "Deprecated { method_name: \"storage_iter_range\" }"
  | "storage_iter_next" => some do
    let _ ← popArgs 3; hErr "Deprecated { method_name: \"storage_iter_next\" }"
  -- promises
  | "promise_batch_create" => some do
    let a ← popArgs 2
    payBaseH C.base
    let acct ← readAccountIdH a[0]! a[1]!
    payNewReceiptH (acct = (← get).ctx.currentAccount) #[]
    let r ← pushAction { text := s!"CR()>{acct}", receiver := some acct }
    pushRet (← pushPromiseH (.receipt r))
  | "promise_batch_then" => some do
    let a ← popArgs 3
    payBaseH C.base
    let acct ← readAccountIdH a[1]! a[2]!
    let s ← get
    let deps ← match s.promises[a[0]!]? with
      | none => hErr s!"InvalidPromiseIndex \{ promise_idx: {a[0]!} }"
      | some (.receipt r) => pure #[r]
      | some (.joint rs) => pure rs
    payNewReceiptH (acct = s.ctx.currentAccount) (deps.map fun r => receiptReceiver s r = acct)
    let r ← pushAction { text := s!"CR({",".intercalate (deps.toList.map toString)})>{acct}",
                         receiver := some acct }
    pushRet (← pushPromiseH (.receipt r))
  | "promise_and" => some do
    let a ← popArgs 2
    payBaseH C.base
    payBaseH C.promiseAndBase
    let ml := a[1]! * 8
    if ml ≥ u64Bound then hErr "IntegerOverflow"
    payPerH C.promiseAndPerPromise ml
    let d ← readMemH a[0]! ml
    let mut deps : Array Nat := #[]
    for i in [0:a[1]!] do
      let pi := leNat (d.extract (8 * i) (8 * i + 8))
      match (← get).promises[pi]? with
      | none => hErr s!"InvalidPromiseIndex \{ promise_idx: {pi} }"
      | some (.receipt r) => deps := deps.push r
      | some (.joint rs) => deps := deps ++ rs
      if deps.size > maxInputDataDependencies then
        hErr s!"NumberInputDataDependenciesExceeded \{ number_of_input_data_dependencies: {deps.size}, limit: {maxInputDataDependencies} }"
    pushRet (← pushPromiseH (.joint deps))
  | "promise_create" => some do
    let a ← popArgs 8
    payBaseH C.base
    let acct ← readAccountIdH a[0]! a[1]!
    payNewReceiptH (acct = (← get).ctx.currentAccount) #[]
    let r ← pushAction { text := s!"CR()>{acct}", receiver := some acct }
    let pi ← pushPromiseH (.receipt r)
    functionCallActionH pi a[2]! a[3]! a[4]! a[5]! a[6]! a[7]! 0
    pushRet pi
  | "promise_then" => some do
    let a ← popArgs 9
    payBaseH C.base
    let acct ← readAccountIdH a[1]! a[2]!
    let s ← get
    let deps ← match s.promises[a[0]!]? with
      | none => hErr s!"InvalidPromiseIndex \{ promise_idx: {a[0]!} }"
      | some (.receipt r) => pure #[r]
      | some (.joint rs) => pure rs
    payNewReceiptH (acct = s.ctx.currentAccount) (deps.map fun r => receiptReceiver s r = acct)
    let r ← pushAction { text := s!"CR({",".intercalate (deps.toList.map toString)})>{acct}",
                         receiver := some acct }
    let pi ← pushPromiseH (.receipt r)
    functionCallActionH pi a[3]! a[4]! a[5]! a[6]! a[7]! a[8]! 0
    pushRet pi
  | "promise_set_refund_to" => some do
    let a ← popArgs 3
    payBaseH C.base
    let acct ← readAccountIdH a[1]! a[2]!
    match (← get).promises[a[0]!]? with
    | none => hErr s!"InvalidPromiseIndex \{ promise_idx: {a[0]!} }"
    | some (.joint _) => hErr "CannotSetRefundToOnJointPromise"
    | some (.receipt r) => let _ ← pushAction { text := s!"RT@{r}:{acct}" }
  | "promise_batch_action_create_account" => some do
    let a ← popArgs 1
    payBaseH C.base
    let (r, sir) ← promiseReceiptH a[0]!
    payActionBaseH F.createAccount sir
    let _ ← pushAction { text := s!"CA@{r}" }
  | "promise_batch_action_deploy_contract" => some do
    let a ← popArgs 3
    payBaseH C.base
    let code ← memOrRegH a[2]! a[1]!
    if code.size > maxContractSize then
      hErr s!"ContractSizeExceeded \{ size: {code.size}, limit: {maxContractSize} }"
    let (r, sir) ← promiseReceiptH a[0]!
    payActionBaseH F.deployContract sir
    payActionPerByteH F.deployContractByte code.size sir
    let _ ← pushAction { text := s!"DC@{r}:{hexStr code}" }
  | "promise_batch_action_function_call" => some do
    let a ← popArgs 7
    functionCallActionH a[0]! a[1]! a[2]! a[3]! a[4]! a[5]! a[6]! 0
  | "promise_batch_action_function_call_weight" => some do
    let a ← popArgs 8
    functionCallActionH a[0]! a[1]! a[2]! a[3]! a[4]! a[5]! a[6]! a[7]!
  | "promise_batch_action_transfer" => some do
    let a ← popArgs 2
    payBaseH C.base
    let amount ← getU128H a[1]!
    let (r, sir) ← promiseReceiptH a[0]!
    let (send, exec) := transferFees sir (receiptReceiver (← get) r)
    payActionH send send (send + exec)
    deductBalanceH amount
    let _ ← pushAction { text := s!"TR@{r}:{amount}" }
  | "promise_batch_action_stake" => some do
    let a ← popArgs 4
    payBaseH C.base
    let amount ← getU128H a[1]!
    let pk ← memOrRegH a[3]! a[2]!
    let (r, sir) ← promiseReceiptH a[0]!
    payActionBaseH F.stake sir
    if !pkValid pk then hErr "InvalidPublicKey"
    let _ ← pushAction { text := s!"ST@{r}:{amount}:{hexStr pk}" }
  | "promise_batch_action_add_key_with_full_access" => some do
    let a ← popArgs 4
    payBaseH C.base
    let pk ← memOrRegH a[2]! a[1]!
    let (r, sir) ← promiseReceiptH a[0]!
    payActionBaseH F.addFullAccessKey sir
    if !pkValid pk then hErr "InvalidPublicKey"
    let _ ← pushAction { text := s!"AF@{r}:{hexStr pk}:{a[3]!}" }
  | "promise_batch_action_add_key_with_function_call" => some do
    let a ← popArgs 9
    payBaseH C.base
    let pk ← memOrRegH a[2]! a[1]!
    let allowance ← getU128H a[4]!
    let recv ← readAccountIdH a[5]! a[6]!
    let raw ← memOrRegH a[8]! a[7]!
    let names ← match splitMethodNames raw with
      | some n => pure n
      | none => hErr "EmptyMethodName"
    let (r, sir) ← promiseReceiptH a[0]!
    let nb := names.foldl (fun acc n => acc + n.size + 1) 0
    payActionBaseH F.addFunctionCallKey sir
    payActionPerByteH F.addFunctionCallKeyByte nb sir
    if !pkValid pk then hErr "InvalidPublicKey"
    let al := if allowance > 0 then toString allowance else "-"
    let _ ← pushAction { text := s!"AC@{r}:{hexStr pk}:{a[3]!}:{al}:{recv}:{"/".intercalate (names.toList.map hexStr)}" }
  | "promise_batch_action_delete_key" => some do
    let a ← popArgs 3
    payBaseH C.base
    let pk ← memOrRegH a[2]! a[1]!
    let (r, sir) ← promiseReceiptH a[0]!
    payActionBaseH F.deleteKey sir
    if !pkValid pk then hErr "InvalidPublicKey"
    let _ ← pushAction { text := s!"DK@{r}:{hexStr pk}" }
  | "promise_batch_action_delete_account" => some do
    let a ← popArgs 3
    payBaseH C.base
    let b ← readAccountIdH a[1]! a[2]!
    let (r, sir) ← promiseReceiptH a[0]!
    payActionBaseH F.deleteAccount sir
    let _ ← pushAction { text := s!"DA@{r}:{b}" }
  | "promise_results_count" => some do payBaseH C.base; pushRet (← get).ctx.promiseResults.size
  | "promise_result" => some do
    let a ← popArgs 2
    payBaseH C.base
    match (← get).ctx.promiseResults[a[0]!]? with
    | none => hErr s!"InvalidPromiseResultIndex \{ result_idx: {a[0]!} }"
    | some .notReady => pushRet 0
    | some (.ok d) => regSetH a[1]! d (chargeBytes := false); pushRet 1
    | some .failed => pushRet 2
  | "promise_return" => some do
    let a ← popArgs 1
    payBaseH C.base
    payBaseH C.promiseReturn
    match (← get).promises[a[0]!]? with
    | none => hErr s!"InvalidPromiseIndex \{ promise_idx: {a[0]!} }"
    | some (.joint _) => hErr "CannotReturnJointPromise"
    | some (.receipt r) => modify fun s => { s with ret := some (.inr r) }
  -- yield / resume
  | "promise_yield_create" => some do
    let a ← popArgs 7
    payBaseH C.base
    payBaseH C.yieldCreateBase
    let m ← memOrRegH a[1]! a[0]!
    if m.size = 0 then hErr "EmptyMethodName"
    let args ← memOrRegH a[3]! a[2]!
    let nb := m.size + args.size
    payPerH C.yieldCreateByte nb
    withGas (deduct · 0 a[4]!)
    payNewReceiptH true #[true]
    let s ← get
    let did := dataId s.dataCount
    set { s with dataCount := s.dataCount + 1 }
    let r ← pushAction { text := s!"YC:{hexStr did}>{s.ctx.currentAccount}:-",
                         receiver := some s.ctx.currentAccount, yieldCreate := some (did, none) }
    let pi ← pushPromiseH (.receipt r)
    payActionBaseH F.functionCall true
    payActionPerByteH F.functionCallByte nb true
    let _ ← pushAction { text := s!"FC@{r}:{hexStr m}:{hexStr args}:0:{a[4]!}:{a[5]!}" }
    regSetH a[6]! did
    pushRet pi
  | "promise_yield_resume" => some do
    let a ← popArgs 4
    payBaseH C.base
    payBaseH C.yieldResumeBase
    payPerH C.yieldResumeByte a[2]!
    let did ← memOrRegH a[1]! a[0]!
    let payload ← memOrRegH a[3]! a[2]!
    if payload.size > maxYieldPayloadSize then
      hErr s!"YieldPayloadLength \{ length: {payload.size}, limit: {maxYieldPayloadSize} }"
    if did.size ≠ 32 then hErr "DataIdMalformed"
    let _ ← pushAction { text := s!"YR:{hexStr did}:{hexStr payload}" }
    let found := (← get).actions.any fun x => match x.yieldCreate with
      | some (d, _) => d == did
      | none => false
    pushRet (if found then 1 else 0) (is64 := false)
  | _ => none

end NearSpecV3.Wasm
