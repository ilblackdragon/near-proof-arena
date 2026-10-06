import NearSpecV3.D2.Types
import NearSpecV3.Ed25519

/-!
# D2 parameters, fees, `validate_actions` / `validate_receipt`

spec/near-chunk-validation-d2.md §4, §6.6. PV 86 uses the PV 85 runtime config (no
`86.yaml`): `core/parameters/res/runtime_configs/parameters.yaml` + version diffs,
cross-checked with `core/parameters/src/snapshots/near_parameters__config_store__tests__85.json.snap`.
A fee is `(send_sir, send_not_sir, exec gas, exec compute)`; compute = gas except the
`deploy_contract` execution fees (`84.yaml:11-35`).

All sums are checked: `none` = `IntegerOverflowError` (a `CostOverflow` failed outcome for a
transaction, `UnexpectedIntegerOverflow` (panic) inside receipt processing).
-/

namespace NearSpecV3.D2

open NearSpec NearSpecV3

structure Fee where
  sir : Nat
  notSir : Nat
  exec : Nat
  execCompute : Nat

def Fee.mk3 (s n e : Nat) : Fee := ⟨s, n, e, e⟩

namespace Fees
def nar : Fee := .mk3 108059500000 108059500000 108059500000
def createAccount : Fee := .mk3 500000000000 500000000000 7200000000000
def deployBase : Fee := ⟨184765750000, 184765750000, 184765750000, 20000000000000⟩
def deployByte : Fee := ⟨6812999, 47683715, 64572944, 250000000⟩
def fcBase : Fee := .mk3 200000000000 200000000000 780000000000
def fcByte : Fee := .mk3 2235934 47683715 2235934
def transfer : Fee := .mk3 115123062500 115123062500 115123062500
def stake : Fee := .mk3 141715687500 141715687500 102217625000
def addFull : Fee := .mk3 101765125000 101765125000 101765125000
def addFcBase : Fee := .mk3 102217625000 102217625000 102217625000
def addFcByte : Fee := .mk3 1925331 47683715 1925331
def deleteKey : Fee := .mk3 94946625000 94946625000 94946625000
def deleteAccount : Fee := .mk3 147489000000 147489000000 147489000000
def delegate : Fee := .mk3 200000000000 200000000000 200000000000
def gkTransfer : Fee := .mk3 115123062500 115123062500 235676644250
def gkByte : Fee := .mk3 59357464 59357464 101435400
def gkNonceWrite : Fee := .mk3 0 0 64196736000
end Fees

namespace Lim
def maxActions : Nat := 100
def maxDeployActions : Nat := 10
def maxTotalPrepaidGas : Nat := 1000000000000000
def maxReceiptSize : Nat := 4194304
def maxContractSize : Nat := 4194304
def maxMethodName : Nat := 256
def maxArgs : Nat := 4194304
def maxMethodNamesBytes : Nat := 2000
def maxInputDeps : Nat := 128
def maxReturnedData : Nat := 4194304
def maxNoncesForGasKey : Nat := 1024
def minTopLevelLen : Nat := 65
/-- `"registrar"` -/
def registrar : Bytes := [114, 101, 103, 105, 115, 116, 114, 97, 114]
def numBytesAccount : Nat := 100
def numExtraBytesRecord : Nat := 40
def maxAccountDeletionUsage : Nat := 10000
/-- `GasKeyInfo::MAX_BALANCE_TO_BURN` = 1 NEAR. -/
def maxGasKeyBurn : Nat := 1000000000000000000000000
def accountCreationCharge : Nat := 7000000000000000000000
def minGasPurchasePrice : Nat := 1000000000
def nonceMult : Nat := 1000000
/-- `wasm_storage_remove_*` compute costs (`61.yaml:5`, `parameters.yaml:198-200`). -/
def removeBaseCompute : Nat := 200000000000
def removeKeyByteCompute : Nat := 38220384
def removeValueByteCompute : Nat := 11531556
end Lim

def two64 : Nat := Params.two64
def two128 : Nat := Params.two128

/-- A `ParameterCost` (gas, compute). -/
structure Cost where
  gas : Nat
  compute : Nat
  deriving Repr, DecidableEq

def Cost.zero : Cost := ⟨0, 0⟩

/-- `ParameterCost::checked_add_result` (both components u64-checked). -/
def Cost.add (a b : Cost) : Option Cost :=
  let g := a.gas + b.gas
  let c := a.compute + b.compute
  if g < two64 && c < two64 then some ⟨g, c⟩ else none

def Fee.send (f : Fee) (sir : Bool) : Cost := let x := if sir then f.sir else f.notSir; ⟨x, x⟩
def Fee.ex (f : Fee) : Cost := ⟨f.exec, f.execCompute⟩
def Cost.scale (c : Cost) (n : Nat) : Cost := ⟨c.gas * n, c.compute * n⟩

def sumCosts : List Cost → Option Cost
  | [] => some Cost.zero
  | c :: cs => do Cost.add c (← sumCosts cs)

/-- `checked_add` of u64 values. -/
def add64 (a b : Nat) : Option Nat := if a + b < two64 then some (a + b) else none
def add128 (a b : Nat) : Option Nat := if a + b < two128 then some (a + b) else none

/-! ## Account types -/

inductive AType where
  | named | nearImplicit | ethImplicit | deterministic
  deriving DecidableEq, Repr

def accountType (a : Bytes) : AType :=
  if AccountId.isEthImplicit a then .ethImplicit
  else if AccountId.isNearImplicit a then .nearImplicit
  else if AccountId.isNearDeterministic a then .deterministic
  else .named

/-! ## Per-action fees (`config.rs:71-398`, `core/parameters/src/cost.rs:722-876`) -/

/-- `access_key_key_len(account_len, pk_len)` = `1 + account + 1 + pk`. -/
def akKeyLen (acct : Bytes) (pk : PublicKey) : Nat := 1 + acct.length + 1 + pk.trieIdLen

def transferSend (sir : Bool) (r : Bytes) : Cost :=
  let t := Fees.transfer.send sir
  match accountType r with
  | .named => t
  | .ethImplicit | .deterministic => ⟨t.gas + (Fees.createAccount.send sir).gas, t.compute + (Fees.createAccount.send sir).compute⟩
  | .nearImplicit =>
    ⟨t.gas + (Fees.createAccount.send sir).gas + (Fees.addFull.send sir).gas,
     t.compute + (Fees.createAccount.send sir).compute + (Fees.addFull.send sir).compute⟩

def transferExec (r : Bytes) : Cost :=
  let t := Fees.transfer.ex
  match accountType r with
  | .named => t
  | .ethImplicit | .deterministic => ⟨t.gas + Fees.createAccount.exec, t.compute + Fees.createAccount.execCompute⟩
  | .nearImplicit =>
    ⟨t.gas + Fees.createAccount.exec + Fees.addFull.exec,
     t.compute + Fees.createAccount.execCompute + Fees.addFull.execCompute⟩

def methodBytes (ms : List Bytes) : Nat := (ms.map fun m => m.length + 1).foldl (· + ·) 0

def permSend (p : Perm) (sir : Bool) : Cost :=
  let key := match p.fcPerm with
    | some fc => let b := Fees.addFcBase.send sir; let y := (Fees.addFcByte.send sir).scale (methodBytes fc.methods)
                 ⟨b.gas + y.gas, b.compute + y.compute⟩
    | none => Fees.addFull.send sir
  match p.gasInfo with
  | some _ => let g := (Fees.gkByte.send sir).scale 18; ⟨key.gas + g.gas, key.compute + g.compute⟩
  | none => key

def permExec (p : Perm) (acct : Bytes) (pk : PublicKey) : Cost :=
  let key := match p.fcPerm with
    | some fc => let b := Fees.addFcBase.ex; let y := Fees.addFcByte.ex.scale (methodBytes fc.methods)
                 ⟨b.gas + y.gas, b.compute + y.compute⟩
    | none => Fees.addFull.ex
  match p.gasInfo with
  | some (_, n) =>
    let base := Fees.gkNonceWrite.ex.scale n
    let pb := (Fees.gkByte.ex.scale (akKeyLen acct pk + 2 + 8)).scale n
    ⟨key.gas + base.gas + pb.gas, key.compute + base.compute + pb.compute⟩
  | none => key

/-- Send fee of a non-delegate action. -/
def baseSend (sir : Bool) (r : Bytes) : Base → Cost
  | .createAccount => Fees.createAccount.send sir
  | .deploy code => let b := Fees.deployBase.send sir; let y := (Fees.deployByte.send sir).scale code.length
                    ⟨b.gas + y.gas, b.compute + y.compute⟩
  | .fcall m a _ _ => let b := Fees.fcBase.send sir; let y := (Fees.fcByte.send sir).scale (m.length + a.length)
                      ⟨b.gas + y.gas, b.compute + y.compute⟩
  | .transfer _ => transferSend sir r
  | .stake _ _ => Fees.stake.send sir
  | .addKey _ ak => permSend ak.perm sir
  | .deleteKey _ => Fees.deleteKey.send sir
  | .deleteAccount _ => Fees.deleteAccount.send sir
  | .toGasKey pk _ | .fromGasKey pk _ =>
    let b := Fees.gkTransfer.send sir; let y := (Fees.gkByte.send sir).scale pk.trieIdLen
    ⟨b.gas + y.gas, b.compute + y.compute⟩

/-- Exec fee of a non-delegate action (`exec_fee`, `config.rs:279-356`). -/
def baseExec (r : Bytes) : Base → Cost
  | .createAccount => Fees.createAccount.ex
  | .deploy code => let b := Fees.deployBase.ex; let y := Fees.deployByte.ex.scale code.length
                    ⟨b.gas + y.gas, b.compute + y.compute⟩
  | .fcall m a _ _ => let b := Fees.fcBase.ex; let y := Fees.fcByte.ex.scale (m.length + a.length)
                      ⟨b.gas + y.gas, b.compute + y.compute⟩
  | .transfer _ => transferExec r
  | .stake _ _ => Fees.stake.ex
  | .addKey pk ak => permExec ak.perm r pk
  | .deleteKey _ => Fees.deleteKey.ex
  | .deleteAccount _ => Fees.deleteAccount.ex
  | .toGasKey pk _ | .fromGasKey pk _ =>
    let b := Fees.gkTransfer.ex; let y := Fees.gkByte.ex.scale (akKeyLen r pk + 27)
    ⟨b.gas + y.gas, b.compute + y.compute⟩

/-- Sequence a list of optional values. -/
def optAll {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | x :: xs => do pure ((← x) :: (← optAll xs))

/-- `total_send_fees(sir, actions, receiver)` (`config.rs:71-199`); a Delegate adds its inner
actions' send fees with the **outer** `sir` and the inner receiver. -/
def totalSend (sir : Bool) (r : Bytes) (acts : List Act) : Option Cost := do
  let cs ← optAll (acts.map fun a => match a with
    | .base b => some (baseSend sir r b.b)
    | .delegate _ d => do
      let inner ← sumCosts (d.actions.map fun b => baseSend sir d.receiver b.b)
      Cost.add (Fees.delegate.send sir) inner)
  sumCosts cs

/-- `total_prepaid_send_fees` (`config.rs:240-277`): only Delegate, inner send fees with
`sir' = (sender = inner receiver)`. -/
def prepaidSend (acts : List Act) : Option Cost := do
  let cs ← optAll (acts.map fun a => match a with
    | .base _ => some Cost.zero
    | .delegate _ d => sumCosts (d.actions.map fun b => baseSend (d.sender == d.receiver) d.receiver b.b))
  sumCosts cs

/-- `total_prepaid_exec_fees(actions, receiver)` (`config.rs:529-556`). -/
def prepaidExec (r : Bytes) (acts : List Act) : Option Cost := do
  let cs ← optAll (acts.map fun a => match a with
    | .base b => some (baseExec r b.b)
    | .delegate _ d => do
      let inner ← sumCosts (d.actions.map fun b => baseExec d.receiver b.b)
      let x ← Cost.add inner Fees.delegate.ex
      Cost.add x Fees.nar.ex)
  sumCosts cs

/-- `exec_fee(action, receiver)` — for a Delegate action its own `delegate` exec fee. -/
def actExec (r : Bytes) : Act → Cost
  | .base b => baseExec r b.b
  | .delegate _ _ => Fees.delegate.ex

def sumNat128 : List Nat → Option Nat
  | [] => some 0
  | x :: xs => do add128 x (← sumNat128 xs)

def sumNat64 : List Nat → Option Nat
  | [] => some 0
  | x :: xs => do add64 x (← sumNat64 xs)

/-- `total_deposit` (`config.rs:558-586`). -/
def totalDeposit (acts : List Act) : Option Nat := do
  let ds ← optAll (acts.map fun a => match a with
    | .base b => some b.b.deposit
    | .delegate _ d => sumNat128 (d.actions.map fun b => b.b.deposit))
  sumNat128 ds

/-- `total_prepaid_gas` (`config.rs:588-602`). -/
def totalPrepaidGas (acts : List Act) : Option Nat := do
  let gs ← optAll (acts.map fun a => match a with
    | .base b => some b.b.prepaidGas
    | .delegate _ d => sumNat64 (d.actions.map fun b => b.b.prepaidGas))
  sumNat64 gs

/-! ## `tx_cost` (`config.rs:400-479`) -/

structure TxCostD2 where
  gasBurnt : Nat
  computeBurnt : Nat
  gasRemaining : Nat
  receiptGasPrice : Nat
  burntAmount : Nat
  gasCost : Nat
  depositCost : Nat
  totalCost : Nat
  deriving Repr

/-- `none` ⇔ `CostOverflow`. Signature verification costs 0 for ED25519 / SECP256K1 keys
(`85.yaml`, ML-DSA keys are out of domain). -/
def txCostD2 (signer receiver : Bytes) (acts : List Act) (gasPrice : Nat) : Option TxCostD2 := do
  let sir := receiver == signer
  let burnt ← Cost.add (Fees.nar.send sir) (← totalSend sir receiver acts)
  let pg ← totalPrepaidGas acts
  let ps ← prepaidSend acts
  let pe ← prepaidExec receiver acts
  let rem ← add64 pg ps.gas
  let rem ← add64 rem Fees.nar.exec
  let rem ← add64 rem pe.gas
  let burntAmount := gasPrice * burnt.gas
  if burntAmount ≥ two128 then none
  let rgp := max gasPrice Lim.minGasPurchasePrice
  let remAmount := rgp * rem
  if remAmount ≥ two128 then none
  let gasCost ← add128 burntAmount remAmount
  let dep ← totalDeposit acts
  let total ← add128 gasCost dep
  pure ⟨burnt.gas, burnt.compute, rem, rgp, burntAmount, gasCost, dep, total⟩

/-! ## `validate_actions_with_mode` (`action_validation.rs:62-482`) -/

/-- `is_valid_staking_key` (`core/crypto/src/key_conversion.rs:6-23`): ED25519, decompresses,
torsion-free (`[ℓ]P = O`). -/
def validStakingKey (pk : PublicKey) : Bool :=
  pk.tag == 0 && pk.data.length == 32 &&
  match Ed25519.decode pk.data with
  | none => false
  | some P => Ed25519.encode (Ed25519.smul Ed25519.L P) == Ed25519.encode Ed25519.Point.zero

def validPerm (p : Perm) : Bool :=
  match p.fcPerm with
  | none => true
  | some fc =>
    AccountId.valid fc.receiver &&
    fc.methods.all (fun m => m.length ≤ Lim.maxMethodName) &&
    methodBytes fc.methods ≤ Lim.maxMethodNamesBytes

def validAddKey (ak : AK) : Bool :=
  validPerm ak.perm &&
  match ak.perm.gasInfo with
  | none => true
  | some (bal, n) =>
    (match ak.perm.fcPerm with | some fc => fc.allowance.isNone | none => true) &&
    1 ≤ n && n ≤ Lim.maxNoncesForGasKey && bal == 0

def validBase : Base → Bool
  | .deploy code => code.length ≤ Lim.maxContractSize
  | .fcall m a g _ => g != 0 && m.length ≤ Lim.maxMethodName && a.length ≤ Lim.maxArgs
  | .stake _ pk => validStakingKey pk
  | .addKey _ ak => validAddKey ak
  | .deleteAccount b => AccountId.valid b
  | _ => true

def isDeploy : Base → Bool
  | .deploy _ => true
  | _ => false

def isDeleteAccount : Base → Bool
  | .deleteAccount _ => true
  | _ => false

/-- `DeleteAccount` only as the last action. -/
def deleteLast : List Bool → Bool
  | [] => true
  | [_] => true
  | d :: rest => !d && deleteLast rest

/-- Validation of a non-delegate action list (also used for Delegate inner actions). -/
def validBaseList (newMode : Bool) (bs : List Base) : Bool :=
  bs.length ≤ Lim.maxActions &&
  (!newMode || (bs.filter isDeploy).length ≤ Lim.maxDeployActions) &&
  deleteLast (bs.map isDeleteAccount) &&
  bs.all validBase &&
  match sumNat64 (bs.map Base.prepaidGas) with
  | some g => g ≤ Lim.maxTotalPrepaidGas
  | none => false

/-- `validate_actions_with_mode(actions, receiver, mode)`. The per-action order of nearcore's
checks does not matter (every failure has the same effect). -/
def validActs (newMode : Bool) (acts : List Act) : Bool :=
  acts.length ≤ Lim.maxActions &&
  (!newMode || (acts.filter fun a => match a with | .base b => isDeploy b.b | _ => false).length
      ≤ Lim.maxDeployActions) &&
  deleteLast (acts.map fun a => match a with | .base b => isDeleteAccount b.b | _ => false) &&
  (acts.filter fun a => match a with | .delegate _ _ => true | _ => false).length ≤ 1 &&
  acts.all (fun a => match a with
    | .base b => validBase b.b
    | .delegate _ d => validBaseList newMode (d.actions.map (·.b))) &&
  match totalPrepaidGas acts with
  | some g => g ≤ Lim.maxTotalPrepaidGas
  | none => false

/-- `validate_receipt(receipt, mode)` (`verifier.rs:540-644`). -/
def validReceipt (newMode : Bool) (r : Rcpt) : Bool :=
  (!newMode || r.encode.length ≤ Lim.maxReceiptSize) &&
  AccountId.valid r.pred && AccountId.valid r.recv &&
  match r.body with
  | .action _ a =>
    a.inputs.length ≤ Lim.maxInputDeps &&
    (match a.refundTo with | some t => AccountId.valid t | none => true) &&
    validActs newMode a.actions
  | .data _ _ x => (x.map List.length |>.getD 0) ≤ Lim.maxReturnedData

/-! ## Congestion gas and receipt size (`congestion_control.rs:657-741, 946-967`) -/

/-- `compute_receipt_congestion_gas`; `none` = overflow. -/
def congestionGas (r : Rcpt) : Option Nat :=
  match r.body with
  | .action false a => do
    let pe ← prepaidExec r.recv a.actions
    let x ← add64 pe.gas Fees.nar.exec
    let ps ← prepaidSend a.actions
    let x ← add64 x ps.gas
    let g ← totalPrepaidGas a.actions
    add64 g x
  | _ => some 0

def receiptSize (r : Rcpt) : Nat := r.encode.length

end NearSpecV3.D2
