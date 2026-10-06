import NearSpecV3.Logged.D2QueuesSpec
import NearSpecV3.D2.Actions

/-!
# Mirror of `D2/Actions.lean` in `LM`
-/

namespace NearSpecV3.D2

open NearSpec NearSpecV3 NearSpecV3.Logged

/-- `ActionHooks` with the `FunctionCall` arm in `LM`. -/
structure ActionHooksL where
  functionCall : ActCtx → ActSt → AR → Base → LM (ActSt × AR)

def d2HooksL : ActionHooksL where
  functionCall _ _ _ _ := throw "out of domain (e.wasm): FunctionCall action dispatched (WASM execution)"

@[reducible] def ActSt.wt (st : ActSt) (t : PTrie) : ActSt := { st with o := st.o.wt t }
@[reducible] def ActCtx.ws (c : ActCtx) (es : HStore) : ActCtx := { c with env := c.env.ws es }

/-- Contract storage of an account (`get_contract_storage_usage`, `actions.rs:454-473`):
local code length by `get_code_len` (path read only), global identifiers by their size. -/
def contractUsageL (o : Ovl) (a : Bytes) (x : Acct) : LM Nat :=
  match x.contract with
  | .none => pure 0
  | .local _ => do pure ((← o.refLenL (kCode a) "contract code length").getD 0)
  | c => pure c.idUsage

/-! ## Action bodies -/

def needAcctL (st : ActSt) : LM Acct :=
  LM.okL st.account (panicked "account exists, checked above")

def akKeysOfL (o : Ovl) (a : Bytes) : LM (List (Bytes × Bytes × Option Nat)) := do
  let pre := kAKPrefix a
  let keys ← o.iterKeysL pre "access keys of a deleted account"
  keys.mapM fun k => match parseAKKey pre k with
    | some (h, i) => pure (k, h, i)
    | none => throw (inconsistent "Can't parse key handle / nonce index from raw key")

/-- `compute_gas_key_balance_sum` (`store/utils.rs:435-474`). -/
def gasKeyBalanceSumL (o : Ovl) (a : Bytes) : LM Nat := do
  let ks ← akKeysOfL o a
  ks.foldlM (fun acc (_, h, i) => do
    if i.isSome then return acc
    match ← o.getAKRawL (kAKPrefix a ++ h) with
    | some k => match k.perm.gasInfo with
      | some (b, _) => if acc + b ≥ two128 then throw (inconsistent "gas key balance overflow") else pure (acc + b)
      | none => pure acc
    | none => pure acc) 0

def actDeleteAccountL (c : ActCtx) (st : ActSt) (res : AR) (ben : Bytes) : LM (ActSt × AR) := do
  let recv := c.r.recv
  let x ← needAcctL st
  let cs ← contractUsageL st.o recv x
  if x.usage - cs > Lim.maxAccountDeletionUsage then return (st, res.fail)
  let gsum ← gasKeyBalanceSumL st.o recv
  if gsum > Lim.maxGasKeyBurn then return (st, res.fail)
  let refunds : List Rcpt := if x.amount > 0 then
      [⟨AccountId.system, ben, zero32, .action false ⟨false, AccountId.system, none, ⟨0, zeros 32⟩, 0, [], [],
         [.base ⟨[3] ++ u128 x.amount, .transfer x.amount⟩]⟩⟩]
    else []
  -- remove_account
  let o := (st.o.remove (kAccount recv)).remove (kCode recv)
  let ks ← akKeysOfL o recv
  let nonceRows := ks.filter fun (_, _, i) => i.isSome
  let o := ks.foldl (fun o (k, _, _) => o.remove k) o
  let dataKeys ← o.iterKeysL (kDataPrefix recv) "contract data of a deleted account"
  let o := dataKeys.foldl (fun o k => o.remove k) o
  if res.tokensBurnt + gsum ≥ two128 then throw (inconsistent "tokens_burnt overflow")
  let compute := if nonceRows.isEmpty then res.compute
    else res.compute + removesCompute nonceRows.length
      ((nonceRows.map fun (k, _, _) => k.length).foldl (· + ·) 0) (8 * nonceRows.length)
  if compute ≥ two64 then throw (inconsistent "compute_usage overflow")
  pure ({ st with o := o, account := none, actor := c.r.pred },
        { res with tokensBurnt := res.tokensBurnt + gsum, newReceipts := res.newReceipts ++ refunds,
                   compute := compute })

def actAddKeyL (c : ActCtx) (st : ActSt) (res : AR) (pk : PublicKey) (ak : AK) : LM (ActSt × AR) := do
  let recv := c.r.recv
  let x ← needAcctL st
  if (← st.o.getAKL recv pk).isSome then return (st, res.fail)
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

def actDeleteKeyL (c : ActCtx) (st : ActSt) (res : AR) (pk : PublicKey) : LM (ActSt × AR) := do
  let recv := c.r.recv
  let x ← needAcctL st
  match ← st.o.getAKL recv pk with
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

def actStakeL (c : ActCtx) (st : ActSt) (res : AR) (stake : Nat) (pk : PublicKey) : LM (ActSt × AR) := do
  let x ← needAcctL st
  let inc := stake - x.locked
  if x.amount < inc then return (st, res.fail)
  if x.locked == 0 && stake == 0 then return (st, res.fail)
  if stake > 0 && stake < c.env.minStake then return (st, res.fail)
  let res := { res with proposals := res.proposals ++ [⟨c.r.recv, pk, stake⟩] }
  if stake > x.locked then
    pure ({ st with account := some { x with amount := x.amount - inc, locked := stake } }, res)
  else pure (st, res)

def actTransferL (c : ActCtx) (st : ActSt) (res : AR) (dep : Nat) : LM (ActSt × AR) := do
  let recv := c.r.recv
  let isRefund := c.r.pred == AccountId.system
  match st.account with
  | some x =>
    let gasRefund := isRefund && c.a.signer == recv
    if gasRefund then
      -- try_refund_gas_key_balance (actions.rs:103-120)
      match ← st.o.getAKL recv c.a.signerPk with
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
      match ← st.o.getAKL recv c.a.signerPk with
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

def actDeployL (c : ActCtx) (st : ActSt) (res : AR) (code : Bytes) : LM (ActSt × AR) := do
  let recv := c.r.recv
  let x ← needAcctL st
  let cs ← contractUsageL st.o recv x
  let u := (x.usage - cs) + code.length
  if u ≥ two64 then throw (inconsistent "Storage usage integer overflow")
  let x' := ({ x with usage := u }).setContract (.local (sha256 code))
  pure ({ st with account := some x', o := st.o.set (kCode recv) code, deploys := st.deploys ++ [code] }, res)

def actToGasKeyL (c : ActCtx) (st : ActSt) (res : AR) (pk : PublicKey) (dep : Nat) : LM (ActSt × AR) := do
  let recv := c.r.recv
  match ← st.o.getAKL recv pk with
  | none => pure (st, res.fail)
  | some k => match k.perm.gasInfo with
    | none => pure (st, res.fail)
    | some (b, _) =>
      if b + dep ≥ two128 then throw (inconsistent "gas key balance integer overflow")
      pure ({ st with o := st.o.setAK recv pk { k with perm := k.perm.setGasBalance (b + dep) } }, res)

def actFromGasKeyL (c : ActCtx) (st : ActSt) (res : AR) (pk : PublicKey) (amt : Nat) : LM (ActSt × AR) := do
  let recv := c.r.recv
  let x ← needAcctL st
  match ← st.o.getAKL recv pk with
  | none => pure (st, res.fail)
  | some k => match k.perm.gasInfo with
    | none => pure (st, res.fail)
    | some (b, _) =>
      if b < amt then return (st, res.fail)
      let o := st.o.setAK recv pk { k with perm := k.perm.setGasBalance (b - amt) }
      if x.amount + amt ≥ two128 then throw (inconsistent "Account balance integer overflow")
      pure ({ st with o := o, account := some { x with amount := x.amount + amt } }, res)

def actCreateAccountL (c : ActCtx) (st : ActSt) (res : AR) : LM (ActSt × AR) := do
  let recv := c.r.recv
  let pred := c.r.pred
  if isTopLevel recv then
    if recv.length < Lim.minTopLevelLen && pred != Lim.registrar then return (st, res.fail)
  else if !isSubAccountOf recv pred then return (st, res.fail)
  pure ({ st with actor := recv, account := some (Acct.new 0 0 .none Lim.numBytesAccount) }, res)

/-! ## Delegate (`actions.rs:487-774`) -/

def actDelegateL (c : ActCtx) (st : ActSt) (res : AR) (d : Delegate) : LM (ActSt × AR) := do
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
  let some k ← st.o.getAKL d.sender d.pk | return (st, res.fail)
  let cur ← match d.nonceIdx with
    | none => if k.perm.gasInfo.isSome then pure none else pure (some k.nonce)
    | some i => match k.perm.gasInfo with
      | none => pure none
      | some (_, n) =>
        if i ≥ n then pure none
        else match ← st.o.getU64L (kNonce d.sender d.pk i) "gas key nonce" with
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
  let ps ← LM.okL (prepaidSend c.a.actions) (panicked "IntegerOverflowError")
  let pe ← LM.okL (prepaidExec d.receiver d.innerActs) (panicked "IntegerOverflowError")
  let pg ← LM.okL (totalPrepaidGas d.innerActs) (panicked "IntegerOverflowError")
  let req ← LM.okL (add64 pe.gas pg >>= fun x => add64 x Fees.nar.exec) (panicked "IntegerOverflowError")
  let gu ← LM.okL (add64 res.gasUsed req >>= fun x => add64 x ps.gas) (panicked "IntegerOverflowError")
  let gb ← LM.okL (add64 res.gasBurnt ps.gas) (panicked "IntegerOverflowError")
  let cu ← LM.okL (add64 res.compute ps.compute) (panicked "IntegerOverflowError")
  let res' : AR := { res with gasUsed := gu, gasBurnt := gb, compute := cu, newReceipts := res.newReceipts ++ [nr] }
  pure ({ st with o := o }, res')

/-! ## `apply_action` -/

def applyActionL (hooks : ActionHooksL) (c : ActCtx) (st : ActSt) (act : Act) : LM (ActSt × AR) := do
  let recv := c.r.recv
  let ex := actExec recv act
  let res : AR := { gasBurnt := ex.gas, gasUsed := ex.gas, compute := ex.compute, ok := true,
                    newReceipts := [], proposals := [], tokensBurnt := 0 }
  let isRefund := c.r.pred == AccountId.system
  let elig := c.nActs == 1 && !isRefund
  if !existenceOk act st.account recv elig then return (st, res.fail)
  if !permissionOk act st.account st.actor recv then return (st, res.fail)
  match act with
  | .delegate _ d => actDelegateL c st res d
  | .base ⟨_, b⟩ =>
    match b with
    | .createAccount => actCreateAccountL c st res
    | .deploy code => actDeployL c st res code
    | .fcall _ _ _ _ => hooks.functionCall c st res b
    | .transfer d => actTransferL c st res d
    | .stake s pk => actStakeL c st res s pk
    | .addKey pk ak => actAddKeyL c st res pk ak
    | .deleteKey pk => actDeleteKeyL c st res pk
    | .deleteAccount ben => actDeleteAccountL c st res ben
    | .toGasKey pk d => actToGasKeyL c st res pk d
    | .fromGasKey pk a => actFromGasKeyL c st res pk a

end NearSpecV3.D2

namespace NearSpecV3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2


/-- The hooks are related: the mirror hook computes the original one on the related states. -/
def HooksR (s : HStore) (root : Bytes) (es : HStore) (H : ActionHooks) (HL : ActionHooksL) : Prop :=
  ∀ (c : ActCtx) (st : ActSt) (ar : AR) (b : Base),
    R s root (HL.functionCall c st ar b) (H.functionCall (c.ws es) (st.wt (preT s root)) ar b)
      (fun p => (p.1.wt (preT s root), p.2))

section
variable {s : HStore} {root : Bytes}

theorem HooksR_d2 (es : HStore) : HooksR s root es d2Hooks d2HooksL := by
  intro c st ar b; exact R_error _

theorem R_contractUsage (o : Ovl) (a : Bytes) (x : Acct) :
    R s root (contractUsageL o a x) (contractUsage (o.wt (preT s root)) a x) id := by
  unfold contractUsage contractUsageL; lk

theorem R_needAcct (st : ActSt) : R s root (needAcctL st) (needAcct (st.wt (preT s root))) id := by
  unfold needAcct needAcctL; lk

theorem R_akKeysOf (o : Ovl) (a : Bytes) :
    R s root (akKeysOfL o a) (akKeysOf (o.wt (preT s root)) a) id := by
  unfold akKeysOf akKeysOfL; lk

end

section
variable {s : HStore} {root : Bytes}
theorem R_contractUsage' (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root)) (a : Bytes) (x : Acct) :
    R s root (contractUsageL o a x) (contractUsage oO a x) id := h ▸ R_contractUsage o a x
theorem R_needAcct' (st : ActSt) {stO : ActSt} (h : stO = st.wt (preT s root)) :
    R s root (needAcctL st) (needAcct stO) id := h ▸ R_needAcct st
theorem R_akKeysOf' (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root)) (a : Bytes) :
    R s root (akKeysOfL o a) (akKeysOf oO a) id := h ▸ R_akKeysOf o a
end
macro_rules | `(tactic| lk_call) => `(tactic| apply R_contractUsage')
macro_rules | `(tactic| lk_call) => `(tactic| apply R_needAcct')
macro_rules | `(tactic| lk_call) => `(tactic| apply R_akKeysOf')

section
variable {s : HStore} {root : Bytes}

theorem R_gasKeyBalanceSum (o : Ovl) (a : Bytes) :
    R s root (gasKeyBalanceSumL o a) (gasKeyBalanceSum (o.wt (preT s root)) a) id := by
  unfold gasKeyBalanceSum gasKeyBalanceSumL; lk

end

section
variable {s : HStore} {root : Bytes}
theorem R_gasKeyBalanceSum' (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root)) (a : Bytes) :
    R s root (gasKeyBalanceSumL o a) (gasKeyBalanceSum oO a) id := h ▸ R_gasKeyBalanceSum o a
end
macro_rules | `(tactic| lk_call) => `(tactic| apply R_gasKeyBalanceSum')

section
variable {s : HStore} {root : Bytes} (es : HStore)


theorem R_actDeleteAccount (c : ActCtx) (st : ActSt) (res : AR) (ben : Bytes) :
    R s root (actDeleteAccountL c st res ben) (actDeleteAccount (c.ws es) (st.wt (preT s root)) res ben) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actDeleteAccount actDeleteAccountL; lk

theorem R_actAddKey (c : ActCtx) (st : ActSt) (res : AR) (pk : PublicKey) (ak : AK) :
    R s root (actAddKeyL c st res pk ak) (actAddKey (c.ws es) (st.wt (preT s root)) res pk ak) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actAddKey actAddKeyL; lk

theorem R_actDeleteKey (c : ActCtx) (st : ActSt) (res : AR) (pk : PublicKey) :
    R s root (actDeleteKeyL c st res pk) (actDeleteKey (c.ws es) (st.wt (preT s root)) res pk) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actDeleteKey actDeleteKeyL; lk

theorem R_actStake (c : ActCtx) (st : ActSt) (res : AR) (stake : Nat) (pk : PublicKey) :
    R s root (actStakeL c st res stake pk) (actStake (c.ws es) (st.wt (preT s root)) res stake pk) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actStake actStakeL; lk

theorem R_actTransfer (c : ActCtx) (st : ActSt) (res : AR) (dep : Nat) :
    R s root (actTransferL c st res dep) (actTransfer (c.ws es) (st.wt (preT s root)) res dep) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actTransfer actTransferL; lk

theorem R_actDeploy (c : ActCtx) (st : ActSt) (res : AR) (code : Bytes) :
    R s root (actDeployL c st res code) (actDeploy (c.ws es) (st.wt (preT s root)) res code) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actDeploy actDeployL; lk

theorem R_actToGasKey (c : ActCtx) (st : ActSt) (res : AR) (pk : PublicKey) (dep : Nat) :
    R s root (actToGasKeyL c st res pk dep) (actToGasKey (c.ws es) (st.wt (preT s root)) res pk dep) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actToGasKey actToGasKeyL; lk

theorem R_actFromGasKey (c : ActCtx) (st : ActSt) (res : AR) (pk : PublicKey) (amt : Nat) :
    R s root (actFromGasKeyL c st res pk amt) (actFromGasKey (c.ws es) (st.wt (preT s root)) res pk amt) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actFromGasKey actFromGasKeyL; lk

theorem R_actCreateAccount (c : ActCtx) (st : ActSt) (res : AR) :
    R s root (actCreateAccountL c st res) (actCreateAccount (c.ws es) (st.wt (preT s root)) res) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actCreateAccount actCreateAccountL; lk

set_option maxHeartbeats 2000000 in
theorem R_actDelegate (c : ActCtx) (st : ActSt) (res : AR) (d : Delegate) :
    R s root (actDelegateL c st res d) (actDelegate (c.ws es) (st.wt (preT s root)) res d) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actDelegate actDelegateL; lk

end

macro_rules | `(tactic| lk_call) => `(tactic| apply R_actDeleteAccount)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actAddKey)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actDeleteKey)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actStake)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actTransfer)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actDeploy)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actToGasKey)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actFromGasKey)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actCreateAccount)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actDelegate)

section
variable {s : HStore} {root : Bytes}

theorem R_applyAction (H : ActionHooks) (HL : ActionHooksL) (es : HStore) (hH : HooksR s root es H HL)
    (c : ActCtx) (st : ActSt) (act : Act) :
    R s root (applyActionL HL c st act) (applyAction H (c.ws es) (st.wt (preT s root)) act)
      (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold applyAction applyActionL; lk

end

end NearSpecV3.Logged
