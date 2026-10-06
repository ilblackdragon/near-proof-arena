import NearSpecV3.D2.Receipts
import NearSpecV3.ChunkValidationD2
import NearSpecV3.Wasm.Exec

/-!
# RuntimeD3: WASM execution behind D2's `ActionHooks.functionCall`

`spec/near-chunk-validation-d3.md` (§1–§7 nearcore transcription, §8 the D2 extensions this uses).
`d3Hooks cfg` implements the `FunctionCall` arm (`runtime/runtime/src/actions.rs`, `function_call.rs`
= `fc.rs`) on top of the D3α WASM semantics (`NearSpecV3.Wasm`):

1. **Code** (§2): `Contract.local h` ⇒ the blob with hash `h` from the chunk's deploy tracker or the
   merged witness values (`Env.codeOf`); none ⇒ `invalid: MissingTrieValue` (cold-cache rule, §2.2).
   `Contract.none` ⇒ a 0-VM-gas `CodeDoesNotExist` failure. Global identifiers stay out of domain.
2. **Domain** (D3α rung 1): every executed contract prepares inside D3α (no floats, no curve host
   functions) and imports none of the yield / state-init / global-contract / gas-key host functions
   (`oodHosts`); otherwise `out of domain (e.wasm-α) …`. An `unmodeled …` WASM outcome is also out of
   domain.
3. **`VMContext`** (§3) from the receipt, the action, the account and the block (`Env`).
4. **Run** `Wasm.runCall` with the trie-backed `External` (`TTN.RealStore`) over the merged witness
   values at the main transition's pre-state root, with the overlay seeded from the D2 `Ovl`. Trie-node
   accounting uses a per-call cache: at PV86 `touching_trie_node` and `read_cached_trie_node` have equal
   gas and compute (`TTN.ttn_costs_equal`), so the chunk-scoped cache (E5) only changes the gas
   *profile*, which is not hashed (§7). Contract writes are replayed into the D2 overlay in order.
5. **Gas weights** (§5.5), **receipts** from the action log (§5.3–5.4: manager indices, data ids
   `sha256(ah ‖ h ‖ k)` for `then` joins, output data receivers / input data ids), **return data**
   (§6.1), account write-back and `subsidized_amount` on success (§4.2).
-/

namespace NearSpecV3.D3

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm

/-! ## Conversions -/

def toBA (b : Bytes) : ByteArray := ⟨b.toArray⟩
def ofBA (b : ByteArray) : Bytes := b.toList
def strOf (b : Bytes) : String := String.fromUTF8! (toBA b)
def bytesOf (s : String) : Bytes := ofBA s.toUTF8

/-- `create_action_hash_from_receipt_id(rid, h, i)` (`utils.rs:287-297, 327-334`). -/
def actionHash (rid : Bytes) (h i : Nat) : Bytes := sha256 (rid ++ u64 h ++ u64 (2 ^ 64 - 1 - i))

/-- `create_receipt_id_from_action_hash(ah, h, k)` = the k-th data id of the call (`ext.rs:303-311`). -/
def dataIdOf (ah : Bytes) (h k : Nat) : Bytes := sha256 (ah ++ u64 h ++ u64 k)

/-! ## Domain -/

/-- Host functions whose real-`External` semantics are not in this rung (
-- state init, global contracts and gas keys are D2 `w.shape` families. -/
def oodHosts : List String :=
  ["promise_batch_action_state_init",
   "promise_batch_action_state_init_by_account_id", "set_state_init_data_entry",
   "promise_batch_action_deploy_global_contract",
   "promise_batch_action_deploy_global_contract_by_account_id",
   "promise_batch_action_use_global_contract", "promise_batch_action_use_global_contract_by_account_id",
   "promise_batch_action_add_gas_key_with_full_access",
   "promise_batch_action_add_gas_key_with_function_call", "promise_batch_action_transfer_to_gas_key"]

/-- `none` = in domain; `some why` = out of D3α. Preparation/compile errors are in domain (the call
fails in nearcore like here). -/
def contractOOD (cfg : NearCfg) (code : ByteArray) : Option String :=
  match prepare cfg code with
  | .outOfDomain w => some w
  | .unmodeled w => some s!"unmodeled preparation: {w}"
  | .ok p =>
    match p.m.imports.find? (fun i => curveHosts.contains i.name || oodHosts.contains i.name) with
    | some i => some s!"host function {i.name}"
    | none => none
  | _ => none

def oodE (why : String) : String := s!"out of domain (e.wasm-α): {why}"

/-! ## The action log → `ReceiptManager` (§5.3, `receipt_manager.rs`) -/

/-- One manager action receipt under construction. -/
structure MR where
  recv : Bytes
  yield : Bool := false
  refundTo : Option Bytes := none
  outputs : List (Bytes × Bytes) := []
  inputs : List Bytes := []
  /-- actions in order: the borsh bytes, plus `(weight)` for FunctionCalls (gas patched later) -/
  acts : List (Bytes × Option (Nat × Nat × Bytes × Bytes × Nat)) := []

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none

def unhexB (s : String) : Except String Bytes := do
  let cs := s.toList
  if cs.length % 2 ≠ 0 then throw "unmodeled: action log hex"
  let rec go : List Char → Except String Bytes
    | a :: b :: rest => do
      match hexVal a, hexVal b with
      | some x, some y => pure (UInt8.ofNat (16 * x + y) :: (← go rest))
      | _, _ => throw "unmodeled: action log hex"
    | _ => pure []
  go cs

def natOf (s : String) : Except String Nat :=
  match s.toNat? with | some n => .ok n | none => .error "unmodeled: action log number"

/-- Parse `TAG@r:f1:f2…`. -/
def splitTag (t : String) : Option (String × Nat × List String) :=
  match t.splitOn "@" with
  | [tag, rest] =>
    match rest.splitOn ":" with
    | r :: fs => (r.toNat?).map fun r => (tag, r, fs)
    | [] => none
  | _ => none

/-- Build the manager receipts from the mock action log (§9). Returns the receipts and the map
from action-log index to manager index. `ah`, `h`: data-id derivation (§5.2). -/
def manager (log : Array MAct) (ah : Bytes) (h : Nat) :
    Except String (Array MR × List (Nat × Nat) × List (Bytes × Bytes)) := do
  let mut rs : Array MR := #[]
  let mut resumes : List (Bytes × Bytes) := []   -- (data id, payload)
  let mut idx : List (Nat × Nat) := []      -- action-log index ↦ manager index
  let mut k := 0                            -- data-id counter (`data_count`)
  let mi (idx : List (Nat × Nat)) (r : Nat) : Except String Nat :=
    match idx.find? (·.1 == r) with
    | some (_, m) => .ok m
    | none => .error "unmodeled: action on a non-receipt log entry"
  for j in [0:log.size] do
    let some e := log[j]? | throw "unmodeled: action log index"
    let t := e.text
    if let some (did, _) := e.yieldCreate then
      -- `create_promise_yield_receipt`: a self-receipt waiting on a fresh data id
      if ofBA did != dataIdOf ah h k then throw "unmodeled: yield data id"
      k := k + 1
      idx := (j, rs.size) :: idx
      rs := rs.push { recv := bytesOf (e.receiver.getD ""), yield := true, inputs := [ofBA did] }
    else if t.startsWith "YR:" then
      match (t.drop 3).toString.splitOn ":" with
      | [d, p] => resumes := resumes ++ [(← unhexB d, ← unhexB p)]
      | _ => throw "unmodeled: YR entry"
    else if t.startsWith "CR(" then
      let some recv := e.receiver | throw "unmodeled: CR without receiver"
      let inner := ((t.drop 3).toString.splitOn ")").headD ""
      let deps ← (inner.splitOn ",").filter (· ≠ "") |>.mapM natOf
      let mut inputs := []
      for d in deps do
        let dm ← mi idx d
        let did := dataIdOf ah h k
        k := k + 1
        let some r := rs[dm]? | throw "unmodeled: dependency index"
        rs := rs.set! dm { r with outputs := r.outputs ++ [(did, bytesOf recv)] }
        inputs := inputs ++ [did]
      idx := (j, rs.size) :: idx
      rs := rs.push { recv := bytesOf recv, inputs }
    else
      match splitTag t with
      | none => throw s!"unmodeled: action log entry {t}"
      | some (tag, r, fs) =>
        let m ← mi idx r
        let some cur := rs[m]? | throw "unmodeled: receipt index"
        let push (raw : Bytes) (fc : Option (Nat × Nat × Bytes × Bytes × Nat)) : Array MR :=
          rs.set! m { cur with acts := cur.acts ++ [(raw, fc)] }
        match tag, fs with
        | "RT", [acct] => rs := rs.set! m { cur with refundTo := some (bytesOf acct) }
        | "CA", [] => rs := push [0] none
        | "DC", [code] => rs := push ([1] ++ borshBytes (← unhexB code)) none
        | "FC", [mh, a, dep, g, w] =>
          let mb ← unhexB mh; let ab ← unhexB a
          rs := push [] (some (← natOf g, ← natOf w, mb, ab, ← natOf dep))
        | "TR", [amt] => rs := push ([3] ++ u128 (← natOf amt)) none
        | "ST", [amt, pk] => rs := push ([4] ++ u128 (← natOf amt) ++ (← unhexB pk)) none
        | "AF", [pk, nonce] => rs := push ([5] ++ (← unhexB pk) ++ u64 (← natOf nonce) ++ [1]) none
        | "AC", [pk, nonce, al, recv, names] =>
          let allowance ← if al == "-" then pure none else some <$> natOf al
          let ms ← (names.splitOn "/").filter (· ≠ "") |>.mapM unhexB
          let perm := (FcPerm.mk allowance (bytesOf recv) ms).encode
          rs := push ([5] ++ (← unhexB pk) ++ u64 (← natOf nonce) ++ [0] ++ perm) none
        | "DK", [pk] => rs := push ([6] ++ (← unhexB pk)) none
        | "DA", [b] => rs := push ([7] ++ borshBytes (bytesOf b)) none
        | _, _ => throw s!"unmodeled: action log entry {t}"
  pure (rs, idx, resumes)

/-- `distribute_unused_gas` (§5.5, `receipt_manager.rs:654-695`): returns the patched receipts and
the gas added to `used`. -/
def distribute (rs : Array MR) (prepaid used : Nat) : Except String (Array MR × Nat) := do
  let unused := prepaid - used
  let ws : List Nat := rs.toList.flatMap fun r => r.acts.filterMap fun (_, fc) =>
    match fc with | some (_, w, _, _, _) => if w > 0 then some w else none | none => none
  let W := ws.foldl (· + ·) 0
  if W == 0 || unused == 0 then return (rs, 0)
  let n := ws.length
  let mut out := rs
  let mut i := 0
  let mut given := 0
  for ri in [0:rs.size] do
    let some r := rs[ri]? | throw "unmodeled"
    let mut acts := []
    for (raw, fc) in r.acts do
      match fc with
      | some (g, w, mb, ab, dep) =>
        if w > 0 then
          let a := unused * w / W
          i := i + 1
          given := given + a
          let extra := if i == n then unused - given else 0
          let g' := g + a + extra
          if g' ≥ 2 ^ 64 then throw "invalid: IntegerOverflowError (gas distribution)"
          acts := acts ++ [(raw, some (g', w, mb, ab, dep))]
        else acts := acts ++ [(raw, fc)]
      | none => acts := acts ++ [(raw, fc)]
    out := out.set! ri { r with acts := acts }
  pure (out, unused)

/-- Final action bytes (FunctionCall: `2 ‖ method ‖ args ‖ gas ‖ deposit`), decoded as D2 actions. -/
def finishActs (r : MR) : Except String (List Act) :=
  r.acts.mapM fun (raw, fc) => do
    let raw := match fc with
      | some (g, _, mb, ab, dep) => [2] ++ borshBytes mb ++ borshBytes ab ++ u64 g ++ u128 dep
      | none => raw
    match pBaseAct raw with
    | .ok (b, []) => pure (.base b)
    | .ok _ => throw "unmodeled: action re-encoding"
    | .error e => if isShapeOOD e then throw e else throw s!"unmodeled: action decoding {e}"

/-! ## The hook -/

/-- Parse the harness-format line of a state-free outcome (`Exec.runCall` `.line`): `abort B U …` ⇒
an action failure with that gas. -/
def lineOutcome (l : String) : Except String (Nat × Nat) :=
  match l.splitOn " " with
  | "abort" :: b :: u :: _ => do pure (← natOf b, ← natOf u)
  | _ => if l.startsWith "out-of-domain" then .error (oodE l) else .error (oodE s!"unmodeled {l}")

def functionCall (cfg : NearCfg) (c : ActCtx) (st : ActSt) (ar : AR) (b : Base) :
    Except String (ActSt × AR) := do
  let .fcall method args gas deposit := b | throw "unmodeled: functionCall hook on a non-FunctionCall"
  let some acct := st.account | throw "invalid: EXPECT_ACCOUNT_EXISTS"
  let env := c.env
  let h := env.ctx.height
  if acct.amount + deposit ≥ 2 ^ 128 then
    throw "invalid: StorageInconsistentState (account balance overflow on deposit)"
  -- code (§2)
  let codeHash ← match acct.contract with
    | .none => pure none
    | .local hh => pure (some hh)
    | _ => throw "out of domain (w.shape): global contract identifier"
  match codeHash with
  | none =>
    -- CodeDoesNotExist: 0 VM gas, action failure
    pure (st, ar.fail)
  | some hh =>
  -- Code (§2.2, cold-cache rule). A blob in the merged witness store always serves. Otherwise:
  -- for the account's *pre-state* contract (nearcore's "contract access", `fc.rs:355-393`) the
  -- verdict depends on the compiled-contract cache and the preparation pipeline (an in-chunk
  -- deploy of the same code, even rolled back, precompiles it; pipelined receipts are prepared
  -- before such a deploy runs): out of domain if that code was deployed in this chunk, else
  -- nearcore's `MissingTrieValue`. A contract set by a deploy in this chunk comes from the deploy
  -- tracker (`contract.rs:42-69`).
  let preHash : Option Bytes := match st.o.trie.find (nibbles (kAccount c.r.recv)) with
    | some (some raw) => match decodeAcct raw with
      | some x => match x.contract with | .local h0 => some h0 | _ => none
      | none => none
    | _ => none
  let code ← match env.codeOf hh with
    | some code => pure code
    | none =>
      if preHash == some hh then
        if (st.deploys ++ c.deployed ++ c.attempted).any (fun x => sha256 x == hh) then
          throw (oodE "pre-state contract served only by the in-chunk compiled-contract cache")
        else throw "invalid: MissingTrieValue (contract code)"
      else match codeAvailable c st hh with
        | some code => pure code
        | none => throw "invalid: MissingTrieValue (contract code)"
  let codeB := toBA code
  if let some why := contractOOD cfg codeB then throw (oodE why)
  -- VMContext (§3)
  let ah := actionHash c.r.rid h c.idx
  let a := c.a
  let isLast := c.idx + 1 == c.nActs
  let ctx : CallCtx := {
    currentAccount := strOf c.r.recv, signer := strOf a.signer, signerPk := toBA a.signerPk.encode,
    predecessor := strOf c.r.pred, refundTo := strOf (a.refundTo.getD c.r.pred), input := toBA args,
    actionHash := some (toBA ah),
    promiseResults := (c.inputs.map fun x => match x with
      | some v => PRes.ok (toBA v) | none => PRes.failed).toArray,
    blockHeight := h, blockTimestamp := env.blockTimestamp, epochHeight := env.epochHeight,
    accountBalance := acct.amount, accountLocked := acct.locked, storageUsage := acct.usage,
    attachedDeposit := deposit, prepaidGas := gas,
    randomSeed := toBA (sha256 (ah ++ env.randomValue)),
    receivers := if isLast then (a.outputs.map fun (_, r) => strOf r).toArray else #[],
    chainId := strOf env.chainId,
    validators := (env.validators.map fun (v, s) => (strOf v, s)).toArray,
    accountContract := some (toBA hh) }
  -- trie-backed External over the merged witness values (§4.2, d3-trie-accounting.md)
  let pfx := TTN.contractDataPrefix ctx.currentAccount
  let ovl : Std.HashMap ByteArray (Option ByteArray) :=
    (st.o.committed ++ st.o.prosp).foldl (fun m (k, v) =>
      m.insert (toBA k) (v.map toBA)) {}
  let real : TTN.RealStore := { store := fun hb => (env.codeOf (ofBA hb)).map toBA,
                                root := toBA env.preRoot, overlay := ovl, pfx }
  let fuel := (gas / pv86.regularOpCost + 2) * 64 + 1000000
  match runCall cfg codeB (strOf method) ctx fuel true false (some real) with
  | .line l =>
    let (burnt, used) ← lineOutcome l
    let gb := ar.gasBurnt + burnt
    pure (st, { ar.fail with gasBurnt := gb, gasFC := ar.gasFC + burnt, gasUsed := ar.gasUsed + used })
  | .done s err =>
    -- storage writes (also of a failed call: rolled back with the receipt, removals counted)
    let o := match s.real with
      | some r => r.writes.foldl (fun (o : Ovl) (k, v) => match v with
          | some v => o.set (ofBA k) (ofBA v)
          | none => o.remove (ofBA k)) st.o
      | none => st.o
    let st := { st with o }
    let burnt := s.gas.burnt
    let logs := s.logs.toList.map ofBA
    -- receipts + gas distribution (only for VM-produced outcomes, §5.5)
    let (rs, idx, resumes) ← manager s.actions ah h
    let (rs, extra) ← distribute rs gas s.gas.used
    let used := s.gas.used + extra
    let ar1 := { ar with gasBurnt := ar.gasBurnt + burnt, gasFC := ar.gasFC + burnt,
                         gasUsed := ar.gasUsed + used, compute := ar.compute + s.gas.computeUsage,
                         logs := ar.logs ++ logs }
    match err with
    | some e =>
      if e.startsWith "unmodeled" then throw (oodE e)
      if e.startsWith "invalid" || e.startsWith "StorageInconsistentState" then throw s!"invalid: {e}"
      pure (st, ar1.fail)
    | none =>
      -- `PromiseYieldIndices` is read on every successful call; each yield receipt enqueues a
      -- timeout `{account, data_id, expires_at = h + 200}` (§4.2.1–4, `fc.rs:154-222`)
      let (yf, yn) ← st.o.getIndices kYieldIdx "PromiseYieldIndices"
      let mut o := st.o
      let mut next := yn
      for m in rs do
        if m.yield then
          let some did := m.inputs.head? | throw "unmodeled: yield receipt without data id"
          if next ≥ 2 ^ 64 - 1 then throw "invalid: panicked (promise yield indices overflow)"
          o := o.set (kYieldTimeout next) (borshBytes c.r.recv ++ did ++ u64 (h + 200))
          next := next + 1
      if next != yn then o := o.set kYieldIdx (encIndices yf next)
      let st := { st with o }
      let rcpts ← rs.toList.mapM fun m => do
        let acts ← finishActs m
        pure (⟨c.r.recv, m.recv, zero32, .action m.yield ⟨true, a.signer, m.refundTo, a.signerPk,
          a.gasPrice, m.outputs, m.inputs, acts⟩⟩ : Rcpt)
      let rcpts := rcpts ++ resumes.map fun (d, p) =>
        (⟨c.r.recv, c.r.recv, zero32, .data true d (some p)⟩ : Rcpt)
      let ret : Ret ← match s.ret with
        | none => pure .none
        | some (.inl v) => pure (.value (ofBA v))
        | some (.inr r) => match idx.find? (·.1 == r) with
          | some (_, m) => pure (.receiptIdx m)
          | none => throw (oodE "promise_return of a non-receipt log index")
      let acct' := { acct with amount := s.balance, usage := s.storageUsage }
      pure ({ st with account := some acct' },
            { ar1 with newReceipts := ar1.newReceipts ++ rcpts, ret := ret,
                       subsidized := ar1.subsidized + s.subsidized })

def d3Hooks (cfg : NearCfg) : ActionHooks where
  functionCall := functionCall cfg

end NearSpecV3.D3

namespace NearSpecV3.D3

/-- **`G_α`**, the D3α per-chunk cap on function-call gas (`gas_burnt_for_function_call`, summed
over the chunk's action receipts; it includes host-function gas). Derivation from single-proof
capacity:
* one np-udr-stark proof has tables of at most 2^22 rows, and the D3 EXEC table takes one row per
  WASM operator (`near-wasm-strategy.md` §2);
* the cheapest operator costs `regular_op_cost` = 822,756 gas;
* so 2^22 operators burn at most `2^22 · 822,756` gas. Host gas only lowers the operator count
  for the same gas, which makes this conservative.

At that table size the single-segment proof is ≈ 2.3 MiB, under the 8 MiB cap
(`docs/research/recursion-r1-cost.md`, lean preset S = 1). This is the checkpoint value; it is re-fixed
at checkpoint 5 from the measured EXEC/RAM rows per operator (`D3_WASM_REQUIREMENTS.md` §2.4). -/
def gAlpha : Nat := 2 ^ 22 * 822756

/-- `Rel_D3` checker: the D2 pipeline (`checkD2Core`) with code blobs allowed and WASM execution
behind the FunctionCall hook. `InD3α` = `InD2` minus `e.wasm`/`w.no_code`, plus the WASM-level
conditions reported by the hook (`out of domain (e.wasm-α) …`) and the per-chunk cap
`out of domain (e.g_alpha)`.

**Cache independence.** `Rel_D3` is the cold-cache statement: the code of every executed pre-state
contract must be in the witness (`spec/near-chunk-validation-d3.md` §2.2). A nearcore validator
with a warm compiled-contract cache may accept witnesses that `Rel_D3` rejects (for example one with
no code blobs at all). `Rel_D3` is the conservative statement that does not depend on any cache. -/
def checkD3 (claimBytes witnessBytes : NearSpec.Bytes) : Except String Unit :=
  checkD2Core (d3Hooks Wasm.pv86) true claimBytes witnessBytes (some gAlpha)

def RelD3 (claimBytes witnessBytes : NearSpec.Bytes) : Prop := checkD3 claimBytes witnessBytes = .ok ()

end NearSpecV3.D3
