import NearSpecV3.Logged.D2Actions
import NearSpecV3.D3.GlobalContract
import NearSpecV3.D2.Receipts

/-! PV86 global action execution over read-logged storage. Action failures return AR.fail;
missing authenticated storage and arithmetic inconsistency remain runtime errors. Distribution
commits independently, charges compute only, and returns its forwarded receipt and materialized
code to the chunk driver. Pinned runtime/runtime/src/{global_contracts,deterministic_account_id}.rs. -/
namespace NearSpecV3.Successor.GlobalExecution
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged NearSpecV3.D3.L4

def refundReceipt (receiver : Bytes) (amount : Nat) : Rcpt :=
  ⟨AccountId.system, receiver, zero32, .action false
    ⟨false, AccountId.system, none, ⟨0, zero32⟩, 0, [], [],
     [.base ⟨[3] ++ u128 amount, .transfer amount⟩]⟩⟩

def contractUsage (c : Contract) : Nat :=
  match c with
  | .global _ => 32
  | .byAccount id => id.length
  | _ => 0

/-- `use_global_contract`: presence reads a value reference; local code length also uses a ref. -/
def useGlobalL (c : ActCtx) (st : ActSt) (res : AR) (gci : Gci) : LM (ActSt × AR) := do
  let some acct := st.account | throw (panicked "global use requires account")
  if !(← st.o.containsL (kGlobalContractCode gci) "global contract code") then
    return (st, res.fail)
  let old ← match acct.contract with
    | .local _ => do pure ((← st.o.refLenL (kCode c.r.recv) "local contract code").getD 0)
    | other => pure (contractUsage other)
  let o := match acct.contract with | .local _ => st.o.remove (kCode c.r.recv) | _ => st.o
  let contract := match gci with | .codeHash h => Contract.global h | .accountId id => .byAccount id
  let usage ← LM.okL (add64 (acct.usage - old) gci.len) (inconsistent "storage usage overflow")
  let acct := { acct.setContract contract with usage }
  pure ({ st with o, account := some acct }, res)

def deployGlobalL (c : ActCtx) (st : ActSt) (res : AR) (d : DeployGlobal) : LM (ActSt × AR) := do
  let some acct := st.account | throw (panicked "global deploy requires account")
  let cost := min (two128 - 1) (globalContractStoragePerByte * d.code.length)
  if acct.amount < cost then return (st, res.fail)
  let burnt ← LM.okL (add128 res.tokensBurnt cost) (panicked "IntegerOverflowError")
  let id := match d.mode with | .codeHash => Gci.codeHash (sha256 d.code) | .accountId => .accountId c.r.recv
  let nonce := (← st.o.getU64L (kGlobalContractNonce id) "global contract nonce").getD 0
  let nonce ← LM.okL (add64 nonce 1) "invalid: UnexpectedIntegerOverflow (GlobalContractDistributionNonce)"
  let o := st.o.set (kGlobalContractNonce id) (u64 nonce)
  let distribution : Distribution := ⟨true, id, c.env.ctx.own, [], d.code, nonce⟩
  let receipt : Rcpt := ⟨c.r.recv, AccountId.system, zero32, .distribution distribution⟩
  pure ({ st with o, account := some { acct with amount := acct.amount - cost } },
        { res with tokensBurnt := burnt, newReceipts := res.newReceipts ++ [receipt] })

/-- Third-party callers may initialize a deterministic account, but do not gain owner authority.
Storage staking counts locked funds and the zero-balance storage exemption. -/
def stateInitL (c : ActCtx) (st : ActSt) (res : AR) (d : Dsi) : LM (ActSt × AR) := do
  let st := { st with account := some (st.account.getD (Acct.new 0 0 .none Lim.numBytesAccount)) }
  let some acct := st.account | throw (panicked "state init account")
  let (st, res) ← if acct.contract == .none then do
      let (st, res) ← useGlobalL c st res d.stateInit.code
      if !res.ok then return (st, res)
      let some acct := st.account | throw (panicked "state init account")
      let (o, usage) ← d.stateInit.data.foldlM (fun (o, usage) (key, value) => do
        let bytes ← LM.okL (add64 key.length value.length) (panicked "IntegerOverflowError")
        let bytes ← LM.okL (add64 bytes Lim.numExtraBytesRecord) (panicked "IntegerOverflowError")
        let usage ← LM.okL (add64 usage bytes) (panicked "IntegerOverflowError")
        pure (o.set (kDataPrefix c.r.recv ++ key) value, usage)) (st.o, acct.usage)
      pure ({ st with o, account := some { acct with usage } }, res)
    else pure (st, res)
  if !res.ok then return (st, res)
  let some acct := st.account | throw (panicked "state init account")
  let enough ← LM.okL (storageStakeOk acct acct.amount) (inconsistent "storage stake overflow")
  let needed := if enough then 0 else Params.storageAmountPerByte * acct.usage - (acct.amount + acct.locked)
  if needed > d.deposit then return (st, res.fail)
  let amount ← LM.okL (add128 acct.amount needed) (panicked "IntegerOverflowError")
  let refund := d.deposit - needed
  let receipts := if refund > 0 then res.newReceipts ++ [refundReceipt c.r.refundReceiver refund] else res.newReceipts
  pure ({ st with account := some { acct with amount } }, { res with newReceipts := receipts })

/-- Caller performs `actExec`, `existenceOk`, and `permissionOk`, which include these typed cases. -/
def applyGlobalActionL (c : ActCtx) (st : ActSt) (res : AR) (b : Base) : LM (ActSt × AR) := do
  match b with
  | .deployGlobal d => deployGlobalL c st res d
  | .useGlobal u => useGlobalL c st res u.gci
  | .stateInit d => stateInitL c st res d
  | _ => throw (panicked "global dispatch called with ordinary action")

/-- Apply distribution and return (state, next-shard receipt, freshly materialized code).
Freshness is >=, so an equal nonce re-applies and charges compute; a stale nonce still forwards.
The code supply is an authenticated distribution event, not a ContractStorage.record_deploy. -/
def applyDistributionL (env : Env) (rs : RS) (r : Rcpt) (d : Distribution) :
    LM (RS × Option Rcpt × Option Bytes) := do
  if !(env.ctx.layout.shardIds.contains d.target) then
    throw "out of domain (c.same_layout): distribution targets an obsolete shard"
  let stored := (← rs.o.getU64L (kGlobalContractNonce d.id) "global contract nonce").getD 0
  let nonce := if d.v2 then d.nonce else 0
  let fresh := nonce ≥ stored
  let rs ← if fresh then do
      let o := ((rs.o.set (kGlobalContractNonce d.id) (u64 nonce)).set (kGlobalContractCode d.id) d.code).commit
      let perByte := deployGlobalExecPerByte * d.code.length
      if perByte ≥ two64 then throw (panicked "IntegerOverflowError")
      let compute ← LM.okL (add64 deployGlobalExecBase perByte) (panicked "IntegerOverflowError")
      let compute ← LM.okL (add64 rs.compute compute) (panicked "IntegerOverflowError")
      pure { rs with o, compute }
    else pure rs
  let delivered := ((d.delivered ++ [env.ctx.own]).mergeSort (· ≤ ·)).eraseDups
  let next := env.ctx.layout.shardIds.find? (fun shard => !delivered.contains shard)
  let forward := next.map fun target =>
    (⟨r.pred, AccountId.system, receiptIdFrom r.rid env.ctx.height 0,
      .distribution { d with target, delivered }⟩ : Rcpt)
  pure (rs, forward, if fresh then some d.code else none)

end NearSpecV3.Successor.GlobalExecution
