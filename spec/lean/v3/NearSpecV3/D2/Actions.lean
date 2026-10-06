import NearSpecV3.D2.Queues

/-!
# D2 actions (`Runtime::apply_action`, `runtime/runtime/src/lib.rs:523-774`)

spec/near-chunk-validation-d2.md §7, §8. `applyAction hooks ctx st act` computes nearcore's
`ActionResult` for one action of an action receipt: the initial gas/compute is the action's
exec fee; `check_account_existence` and `check_actor_permissions` (`actions.rs:776-914`) run
first, and a failing check is an action error (`ok = false`). Then the action body runs.

## The D3 interface

`ActionHooks.functionCall` is called at the dispatch point of a `FunctionCall` action (both
checks passed), with the receipt context (`ActCtx`), the current overlay / receiver account /
actor (`ActSt`) and the result so far (exec fee charged). D2 instantiates it with
`out of domain (e.e.wasm)`; D3 supplies WASM execution (which may write state, emit receipts,
logs, burn function-call gas). Global-contract and state-init actions are excluded at
decoding (`w.shape`); D3 extends `Base` and adds hooks for them.
-/

namespace NearSpecV3.D2

open NearSpec NearSpecV3

structure ActSt where
  o : Ovl
  account : Option Acct
  actor : Bytes
  /-- E4: codes deployed by `DeployContract` in the current receipt, not yet committed
  (`ContractsTracker` uncommitted deploys, `contract.rs:42-48`; `actions.rs:336-339`,
  `update.rs:298-300`), in deploy order. Merged into `RS.deployed` when the receipt commits,
  dropped on rollback. D2 never reads it. -/
  deploys : List Bytes := []

/-- `ReturnData` of an action (`lib.rs:459-466`, `fc.rs:228`); E8. Every non-FunctionCall
action returns `.none`. -/
inductive Ret where
  | none
  | value (v : Bytes)
  | receiptIdx (k : Nat)
  deriving Repr, DecidableEq

/-- `merge`: a receipt index local to an action becomes global (`lib.rs:461-464`). -/
def Ret.shift : Ret → Nat → Ret
  | .receiptIdx k, n => .receiptIdx (k + n)
  | r, _ => r

/-- `ActionResult` (`lib.rs:378-414`). The D3 fields (E6–E9) default to D2 behaviour. -/
structure AR where
  gasBurnt : Nat
  gasUsed : Nat
  compute : Nat
  ok : Bool
  newReceipts : List Rcpt
  proposals : List Proposal
  tokensBurnt : Nat
  /-- E6: `gas_burnt_for_function_call`; summed in `merge` always, kept by `set_error`. -/
  gasFC : Nat := 0
  /-- E7: logs, in emission order; appended in `merge` always, kept by `set_error`. -/
  logs : List Bytes := []
  /-- E8: `Ok(return_data)`; meaningful only when `ok`. -/
  ret : Ret := .none
  /-- E9: `subsidized_amount`; added in `merge` on success, cleared by `set_error`. -/
  subsidized : Nat := 0

structure ActCtx where
  env : Env
  r : Rcpt
  a : ActionR
  idx : Nat
  nActs : Nat
  /-- E3: the `ReceivedData` of `a.inputs` (`input_data_ids`), in order: `some v` =
  `PromiseResult::Successful(v)`, `none` = `Failed` (`lib.rs:796-821`). Identical for every
  action of the receipt. -/
  inputs : List (Option Bytes) := []
  /-- E4: codes committed by earlier receipts of this chunk (`ContractsTracker` committed
  deploys; = `RS.deployed` at the start of the receipt). -/
  deployed : List Bytes := []

structure ActionHooks where
  functionCall : ActCtx → ActSt → AR → Base → Except String (ActSt × AR)

def d2Hooks : ActionHooks where
  functionCall _ _ _ _ := .error "out of domain (e.wasm): FunctionCall action dispatched (WASM execution)"

/-- `ActionResult::set_error` (`lib.rs:487-493`): keeps gas, `gasFC`, compute and logs. -/
def AR.fail (r : AR) : AR :=
  { r with ok := false, newReceipts := [], proposals := [], tokensBurnt := 0, subsidized := 0,
           ret := .none }

/-- E4: `ContractStorage::get(code_hash)` (`contract.rs:104-131`): a contract deployed during
this chunk (current receipt's uncommitted deploys, then committed ones), else the recorded
storage `Env.codeOf` (`w.main.values ++ codes`). `none` = not available (cold-cache
`MissingTrieValue`, spec/near-chunk-validation-d3.md §2.2). -/
def codeAvailable (c : ActCtx) (st : ActSt) (h : Bytes) : Option Bytes :=
  match (st.deploys ++ c.deployed).find? (fun code => sha256 code == h) with
  | some code => some code
  | none => c.env.codeOf h

/-! ## Helpers -/

def isImplicit (a : Bytes) : Bool := accountType a != .named

/-- `AccountId::is_top_level`: not `system`, no `.`. -/
def isTopLevel (a : Bytes) : Bool := a != AccountId.system && !a.contains 46

/-- `is_sub_account_of(parent)`: `a = s ‖ "." ‖ parent` with no `.` in `s`. -/
def isSubAccountOf (a parent : Bytes) : Bool :=
  a.length > parent.length && a.drop (a.length - parent.length) == parent &&
  let s := a.take (a.length - parent.length)
  s.getLast? == some 46 && !(s.dropLast).contains 46

def hexVal (c : UInt8) : Nat := if c.toNat ≤ 57 then c.toNat - 48 else c.toNat - 87

def hexDecode : Bytes → Bytes
  | a :: b :: rest => UInt8.ofNat (hexVal a * 16 + hexVal b) :: hexDecode rest
  | _ => []

/-- `eth_wallet_global_contract_hash(chain_id)` (`runtime/near-wallet-contract/src/lib.rs:89-105`). -/
def ethWalletHash (chainId : Bytes) : Bytes :=
  let mainnet : Bytes := [109, 97, 105, 110, 110, 101, 116]
  let mocknet : Bytes := [109, 111, 99, 107, 110, 101, 116]
  let testnet : Bytes := [116, 101, 115, 116, 110, 101, 116]
  if chainId == mainnet || chainId == mocknet then
    [0x1d, 0xaa, 0x83, 0x5c, 0x46, 0x37, 0xf7, 0xae, 0x3d, 0x92, 0x40, 0x95, 0xba, 0x3f,
     0x0b, 0xf2, 0x82, 0x9b, 0xcf, 0xa1, 0x7b, 0x10, 0x68, 0xcd, 0x58, 0xbd, 0x85, 0x3d,
     0xca, 0xd7, 0xce, 0xb5]
  else if chainId == testnet then
    [0x23, 0x8f, 0xea, 0xc1, 0xf8, 0x6c, 0xc9, 0xf9, 0xf4, 0x00, 0x3e, 0x3f, 0x6d, 0x5a,
     0xeb, 0xc0, 0x4e, 0xae, 0xa9, 0xc3, 0x94, 0x03, 0x2b, 0xd2, 0x94, 0x70, 0xe9, 0x60,
     0x9b, 0x67, 0xf6, 0xc5]
  else
    -- sha256(res/wallet_contract_localnet.wasm)
    [0xd2, 0x88, 0x4a, 0x90, 0x0d, 0x4f, 0xa3, 0x70, 0xe4, 0x8f, 0x1e, 0x3d, 0x48, 0x65,
     0xd4, 0xdc, 0x0d, 0xbd, 0x09, 0x3c, 0x89, 0xf0, 0xe7, 0xba, 0xef, 0x2e, 0xdd, 0xc1,
     0x42, 0xc4, 0x9e, 0x8d]

/-- `initial_nonce_value(height) = (height − 1) · 10⁶` (`access_keys.rs:46-50`). -/
def initialNonce (height : Nat) : Nat := (height - 1) * Lim.nonceMult

/-- `access_key_storage_usage` (`access_keys.rs:17-29`). -/
def akUsage (pk : PublicKey) (k : AK) : Nat := pk.trieIdLen + k.encode.length + Lim.numExtraBytesRecord

/-- `gas_key_storage_cost` (`access_keys.rs:31-44`). -/
def gasKeyUsage (pk : PublicKey) (k : AK) (n : Nat) : Nat :=
  n * (pk.trieIdLen + 2 + 8 + Lim.numExtraBytesRecord) + akUsage pk k

/-- `storage_removes_compute(count, key bytes, value bytes)` (`config.rs:56-69`). -/
def removesCompute (count keyBytes valueBytes : Nat) : Nat :=
  Lim.removeBaseCompute * count + Lim.removeKeyByteCompute * keyBytes +
  Lim.removeValueByteCompute * valueBytes

/-- Contract storage of an account (`get_contract_storage_usage`, `actions.rs:454-473`):
local code length by `get_code_len` (path read only), global identifiers by their size. -/
def contractUsage (o : Ovl) (a : Bytes) (x : Acct) : Except String Nat :=
  match x.contract with
  | .none => .ok 0
  | .local _ => do pure ((← o.refLen (kCode a) "contract code length").getD 0)
  | c => .ok c.idUsage

def Base.isFcall : Base → Bool
  | .fcall _ _ _ _ => true
  | _ => false

/-! ## Existence and permission checks -/

/-- `check_account_existence` (`actions.rs:824-892`); `true` = passes. -/
def existenceOk (act : Act) (account : Option Acct) (recv : Bytes) (elig : Bool) : Bool :=
  match act with
  | .base ⟨_, .createAccount⟩ => account.isNone && !isImplicit recv
  | .base ⟨_, .transfer _⟩ => account.isSome || (elig && isImplicit recv)
  | _ => account.isSome

/-- `check_actor_permissions` (`actions.rs:776-822`). -/
def permissionOk (act : Act) (account : Option Acct) (actor recv : Bytes) : Bool :=
  match act with
  | .base ⟨_, .deploy _⟩ | .base ⟨_, .stake _ _⟩ | .base ⟨_, .addKey _ _⟩
  | .base ⟨_, .deleteKey _⟩ | .base ⟨_, .fromGasKey _ _⟩ => actor == recv
  | .base ⟨_, .deleteAccount _⟩ =>
    actor == recv && (match account with | some a => a.locked == 0 | none => false)
  | _ => true

/-! ## Action bodies -/

def needAcct (st : ActSt) : Except String Acct :=
  ok? st.account (panicked "account exists, checked above")

/-- Parse the key handle and optional nonce index of a raw access-key trie key
(`parse_key_handle_from_access_key_key`, `parse_nonce_index_from_gas_key_key`,
`trie_key.rs:683-718`). -/
def parseAKKey (pre k : Bytes) : Option (Bytes × Option Nat) :=
  match k.drop pre.length with
  | t :: r =>
    let len := if t == 0 then 32 else if t == 1 then 64 else if t == 3 then 32 else 0
    if len == 0 || r.length < len then none
    else
      let suffix := r.drop len
      if suffix.isEmpty then some (t :: r.take len, none)
      else if suffix.length == 2 then some (t :: r.take len, some (leNat suffix))
      else none
  | [] => none

def akKeysOf (o : Ovl) (a : Bytes) : Except String (List (Bytes × Bytes × Option Nat)) := do
  let pre := kAKPrefix a
  let keys ← o.iterKeys pre "access keys of a deleted account"
  keys.mapM fun k => match parseAKKey pre k with
    | some (h, i) => pure (k, h, i)
    | none => throw (inconsistent "Can't parse key handle / nonce index from raw key")

/-- `compute_gas_key_balance_sum` (`store/utils.rs:435-474`). -/
def gasKeyBalanceSum (o : Ovl) (a : Bytes) : Except String Nat := do
  let ks ← akKeysOf o a
  ks.foldlM (fun acc (_, h, i) => do
    if i.isSome then return acc
    match ← o.getAKRaw (kAKPrefix a ++ h) with
    | some k => match k.perm.gasInfo with
      | some (b, _) => if acc + b ≥ two128 then throw (inconsistent "gas key balance overflow") else pure (acc + b)
      | none => pure acc
    | none => pure acc) 0

def actDeleteAccount (c : ActCtx) (st : ActSt) (res : AR) (ben : Bytes) : Except String (ActSt × AR) := do
  let recv := c.r.recv
  let x ← needAcct st
  let cs ← contractUsage st.o recv x
  if x.usage - cs > Lim.maxAccountDeletionUsage then return (st, res.fail)
  let gsum ← gasKeyBalanceSum st.o recv
  if gsum > Lim.maxGasKeyBurn then return (st, res.fail)
  let refunds : List Rcpt := if x.amount > 0 then
      [⟨AccountId.system, ben, zero32, .action false ⟨false, AccountId.system, none, ⟨0, zeros 32⟩, 0, [], [],
         [.base ⟨[3] ++ u128 x.amount, .transfer x.amount⟩]⟩⟩]
    else []
  -- remove_account
  let o := (st.o.remove (kAccount recv)).remove (kCode recv)
  let ks ← akKeysOf o recv
  let nonceRows := ks.filter fun (_, _, i) => i.isSome
  let o := ks.foldl (fun o (k, _, _) => o.remove k) o
  let dataKeys ← o.iterKeys (kDataPrefix recv) "contract data of a deleted account"
  let o := dataKeys.foldl (fun o k => o.remove k) o
  if res.tokensBurnt + gsum ≥ two128 then throw (inconsistent "tokens_burnt overflow")
  let compute := if nonceRows.isEmpty then res.compute
    else res.compute + removesCompute nonceRows.length
      ((nonceRows.map fun (k, _, _) => k.length).foldl (· + ·) 0) (8 * nonceRows.length)
  if compute ≥ two64 then throw (inconsistent "compute_usage overflow")
  pure ({ st with o := o, account := none, actor := c.r.pred },
        { res with tokensBurnt := res.tokensBurnt + gsum, newReceipts := res.newReceipts ++ refunds,
                   compute := compute })

def actAddKey (c : ActCtx) (st : ActSt) (res : AR) (pk : PublicKey) (ak : AK) : Except String (ActSt × AR) := do
  let recv := c.r.recv
  let x ← needAcct st
  if (← st.o.getAK recv pk).isSome then return (st, res.fail)
  let h := c.env.ctx.height
  match ak.perm.gasInfo with
  | some (_, n) =>
    let k : AK := { ak with nonce := 0 }
    let o := st.o.setAK recv pk k
    let o := (List.range n).foldl (fun o i => o.set (kNonce recv pk i) (u64 (initialNonce h))) o
    let u := x.usage + gasKeyUsage pk k n
    if u ≥ two64 then throw (inconsistent "Storage usage integer overflow")
    pure ({ st with o := o, account := some { x with usage := u } }, res)
  | none =>
    let k : AK := { ak with nonce := initialNonce h }
    let u := x.usage + akUsage pk k
    if u ≥ two64 then throw (inconsistent "Storage usage integer overflow")
    pure ({ st with o := st.o.setAK recv pk k, account := some { x with usage := u } }, res)

def actDeleteKey (c : ActCtx) (st : ActSt) (res : AR) (pk : PublicKey) : Except String (ActSt × AR) := do
  let recv := c.r.recv
  let x ← needAcct st
  match ← st.o.getAK recv pk with
  | none => pure (st, res.fail)
  | some k =>
    match k.perm.gasInfo with
    | some (bal, n) =>
      if bal > Lim.maxGasKeyBurn then return (st, res.fail)
      if res.tokensBurnt + bal ≥ two128 then throw (panicked "IntegerOverflowError")
      let o := (List.range n).foldl (fun o i => o.remove (kNonce recv pk i)) st.o
      let keyLen := akKeyLen recv pk + 2
      let compute := res.compute + removesCompute n (keyLen * n) (8 * n)
      if compute ≥ two64 then throw (panicked "IntegerOverflowError")
      let o := o.remove (kAK recv pk)
      pure ({ st with o := o, account := some { x with usage := x.usage - gasKeyUsage pk k n } },
            { res with tokensBurnt := res.tokensBurnt + bal, compute })
    | none =>
      pure ({ st with o := st.o.remove (kAK recv pk), account := some { x with usage := x.usage - akUsage pk k } },
            res)

def actStake (c : ActCtx) (st : ActSt) (res : AR) (stake : Nat) (pk : PublicKey) : Except String (ActSt × AR) := do
  let x ← needAcct st
  let inc := stake - x.locked
  if x.amount < inc then return (st, res.fail)
  if x.locked == 0 && stake == 0 then return (st, res.fail)
  if stake > 0 && stake < c.env.minStake then return (st, res.fail)
  let res := { res with proposals := res.proposals ++ [⟨c.r.recv, pk, stake⟩] }
  if stake > x.locked then
    pure ({ st with account := some { x with amount := x.amount - inc, locked := stake } }, res)
  else pure (st, res)

def actTransfer (c : ActCtx) (st : ActSt) (res : AR) (dep : Nat) : Except String (ActSt × AR) := do
  let recv := c.r.recv
  let isRefund := c.r.pred == AccountId.system
  match st.account with
  | some x =>
    let gasRefund := isRefund && c.a.signer == recv
    if gasRefund then
      -- try_refund_gas_key_balance (actions.rs:103-120)
      match ← st.o.getAK recv c.a.signerPk with
      | some k =>
        match k.perm.gasInfo with
        | some (b, _) =>
          if b + dep ≥ two128 then throw (inconsistent "gas key balance integer overflow")
          let k' : AK := { k with perm := k.perm.setGasBalance (b + dep) }
          return ({ st with o := st.o.setAK recv c.a.signerPk k' }, res)
        | none => pure ()
      | none => pure ()
    if x.amount + dep ≥ two128 then throw (inconsistent "Account balance integer overflow")
    let st := { st with account := some { x with amount := x.amount + dep } }
    if gasRefund then
      -- try_refund_allowance (actions.rs:122-146)
      match ← st.o.getAK recv c.a.signerPk with
      | some k =>
        match k.perm with
        | .fc fc =>
          match fc.allowance with
          | some al =>
            let na := min (al + dep) Params.u128Max
            if na > al then
              return ({ st with o := st.o.setAK recv c.a.signerPk { k with perm := .fc { fc with allowance := some na } } }, res)
            else return (st, res)
          | none => return (st, res)
        | _ => return (st, res)
      | none => return (st, res)
    pure (st, res)
  | none =>
    -- action_implicit_account_creation_transfer (actions.rs:201-295)
    match accountType recv with
    | .nearImplicit =>
      let k : AK := ⟨initialNonce c.env.ctx.height, .full⟩
      let pk : PublicKey := ⟨0, hexDecode recv⟩
      let acct := Acct.new dep 0 .none (Lim.numBytesAccount + pk.trieIdLen + k.encode.length + Lim.numExtraBytesRecord)
      pure ({ st with o := st.o.setAK recv pk k, account := some acct, actor := recv }, res)
    | .ethImplicit =>
      let h := ethWalletHash c.env.chainId
      pure ({ st with account := some (Acct.new dep 0 (.global h) (Lim.numBytesAccount + 32)), actor := recv }, res)
    | .deterministic =>
      pure ({ st with account := some (Acct.new dep 0 .none Lim.numBytesAccount), actor := recv }, res)
    | .named => throw (panicked "must be implicit")

def actDeploy (c : ActCtx) (st : ActSt) (res : AR) (code : Bytes) : Except String (ActSt × AR) := do
  let recv := c.r.recv
  let x ← needAcct st
  let cs ← contractUsage st.o recv x
  let u := (x.usage - cs) + code.length
  if u ≥ two64 then throw (inconsistent "Storage usage integer overflow")
  let x' := ({ x with usage := u }).setContract (.local (sha256 code))
  pure ({ st with account := some x', o := st.o.set (kCode recv) code, deploys := st.deploys ++ [code] }, res)

def actToGasKey (c : ActCtx) (st : ActSt) (res : AR) (pk : PublicKey) (dep : Nat) : Except String (ActSt × AR) := do
  let recv := c.r.recv
  match ← st.o.getAK recv pk with
  | none => pure (st, res.fail)
  | some k => match k.perm.gasInfo with
    | none => pure (st, res.fail)
    | some (b, _) =>
      if b + dep ≥ two128 then throw (inconsistent "gas key balance integer overflow")
      pure ({ st with o := st.o.setAK recv pk { k with perm := k.perm.setGasBalance (b + dep) } }, res)

def actFromGasKey (c : ActCtx) (st : ActSt) (res : AR) (pk : PublicKey) (amt : Nat) : Except String (ActSt × AR) := do
  let recv := c.r.recv
  let x ← needAcct st
  match ← st.o.getAK recv pk with
  | none => pure (st, res.fail)
  | some k => match k.perm.gasInfo with
    | none => pure (st, res.fail)
    | some (b, _) =>
      if b < amt then return (st, res.fail)
      let o := st.o.setAK recv pk { k with perm := k.perm.setGasBalance (b - amt) }
      if x.amount + amt ≥ two128 then throw (inconsistent "Account balance integer overflow")
      pure ({ st with o := o, account := some { x with amount := x.amount + amt } }, res)

def actCreateAccount (c : ActCtx) (st : ActSt) (res : AR) : Except String (ActSt × AR) := do
  let recv := c.r.recv
  let pred := c.r.pred
  if isTopLevel recv then
    if recv.length < Lim.minTopLevelLen && pred != Lim.registrar then return (st, res.fail)
  else if !isSubAccountOf recv pred then return (st, res.fail)
  pure ({ st with actor := recv, account := some (Acct.new 0 0 .none Lim.numBytesAccount) }, res)

/-! ## Delegate (`actions.rs:487-774`) -/

def actDelegate (c : ActCtx) (st : ActSt) (res : AR) (d : Delegate) : Except String (ActSt × AR) := do
  let recv := c.r.recv
  let sigOk ← match d.sigTag, d.pk.tag with
    | 0, 0 => pure (Ed25519.verify d.pk.data d.sig d.signedHash)
    | 1, 1 => throw "out of domain (e.secp): SECP256K1 delegate signature verification"
    | _, _ => pure false
  if !sigOk then return (st, res.fail)
  let h := c.env.ctx.height
  if h > d.maxHeight then return (st, res.fail)
  if d.sender != recv then return (st, res.fail)
  -- validate_delegate_action_key
  let some k ← st.o.getAK d.sender d.pk | return (st, res.fail)
  let cur ← match d.nonceIdx with
    | none => if k.perm.gasInfo.isSome then pure none else pure (some k.nonce)
    | some i => match k.perm.gasInfo with
      | none => pure none
      | some (_, n) =>
        if i ≥ n then pure none
        else match ← st.o.getU64 (kNonce d.sender d.pk i) "gas key nonce" with
          | some v => pure (some v)
          | none => throw (inconsistent "gas key nonce row missing")
  let some cur := cur | return (st, res.fail)
  if d.nonce ≤ cur then return (st, res.fail)
  if d.nonce ≥ h * Lim.nonceMult then return (st, res.fail)
  match k.perm.fcPerm with
  | some fc =>
    match d.actions with
    | [⟨_, .fcall m _ _ dep⟩] =>
      if dep > 0 then return (st, res.fail)
      if d.receiver != fc.receiver then return (st, res.fail)
      if !fc.methods.isEmpty && !fc.methods.contains m then return (st, res.fail)
    | _ => return (st, res.fail)
  | none => pure ()
  let o := match d.nonceIdx with
    | none => st.o.setAK d.sender d.pk { k with nonce := d.nonce }
    | some i => st.o.set (kNonce d.sender d.pk i) (u64 d.nonce)
  let nr : Rcpt := ⟨d.sender, d.receiver, zero32,
    .action false ⟨false, c.a.signer, none, c.a.signerPk, c.a.gasPrice, [], [], d.innerActs⟩⟩
  let ps ← ok? (prepaidSend c.a.actions) (panicked "IntegerOverflowError")
  let pe ← ok? (prepaidExec d.receiver d.innerActs) (panicked "IntegerOverflowError")
  let pg ← ok? (totalPrepaidGas d.innerActs) (panicked "IntegerOverflowError")
  let req ← ok? (add64 pe.gas pg >>= fun x => add64 x Fees.nar.exec) (panicked "IntegerOverflowError")
  let gu ← ok? (add64 res.gasUsed req >>= fun x => add64 x ps.gas) (panicked "IntegerOverflowError")
  let gb ← ok? (add64 res.gasBurnt ps.gas) (panicked "IntegerOverflowError")
  let cu ← ok? (add64 res.compute ps.compute) (panicked "IntegerOverflowError")
  let res' : AR := { res with gasUsed := gu, gasBurnt := gb, compute := cu, newReceipts := res.newReceipts ++ [nr] }
  pure ({ st with o := o }, res')

/-! ## `apply_action` -/

def applyAction (hooks : ActionHooks) (c : ActCtx) (st : ActSt) (act : Act) : Except String (ActSt × AR) := do
  let recv := c.r.recv
  let ex := actExec recv act
  let res : AR := { gasBurnt := ex.gas, gasUsed := ex.gas, compute := ex.compute, ok := true,
                    newReceipts := [], proposals := [], tokensBurnt := 0 }
  let isRefund := c.r.pred == AccountId.system
  let elig := c.nActs == 1 && !isRefund
  if !existenceOk act st.account recv elig then return (st, res.fail)
  if !permissionOk act st.account st.actor recv then return (st, res.fail)
  match act with
  | .delegate _ d => actDelegate c st res d
  | .base ⟨_, b⟩ =>
    match b with
    | .createAccount => actCreateAccount c st res
    | .deploy code => actDeploy c st res code
    | .fcall _ _ _ _ => hooks.functionCall c st res b
    | .transfer d => actTransfer c st res d
    | .stake s pk => actStake c st res s pk
    | .addKey pk ak => actAddKey c st res pk ak
    | .deleteKey pk => actDeleteKey c st res pk
    | .deleteAccount ben => actDeleteAccount c st res ben
    | .toGasKey pk d => actToGasKey c st res pk d
    | .fromGasKey pk a => actFromGasKey c st res pk a

end NearSpecV3.D2
