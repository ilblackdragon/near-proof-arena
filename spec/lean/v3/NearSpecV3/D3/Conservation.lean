import NearSpecV3.D3.FunctionCall
import NearSpecV3.StateMeasure
import NearSpecV3.Supply

/-!
# Conservation of NEAR by a D3 chunk — the statement

**Statement only; nothing here is proved.** The chunk-level claim is `ChunkConservation` and
`MissingChunkConservation` below, as `Prop`s (no `sorry`, so this module can sit in the default
build). `docs/zk-formal/CONSERVATION-D3.md` explains the choices; this header records the three that
differ from `ConservationStatement.lean`.

1. **Receipts carry gas, not only deposits.** A transaction's signer pays
   `burntAmount + rgp · rem + deposit` (`Fees.lean:376-384`); `burntAmount` goes to `txBurnt`, the
   rest travels in the receipt, whose `gasPrice` is `rgp` and whose gas is `rem` — exactly the `tot`
   that `refunds` later measures against (`Receipts.lean:72-79`). So a receipt's value is
   `deposit + gasPrice · tot`. A refund receipt has `gasPrice = 0`, so its value is its deposit.
2. **Receipts at rest in the trie count.** Postponed (`[6]`), delayed (`[7]`), yield (`[12]`) and
   buffered (`[14]`) receipts hold NEAR while stored, and the runtime moves receipts between those
   keys and the in-flight lists.
3. **The measure is over the revealed part of the trie.** A chunk's trie is a partial trie: only the
   recorded storage is revealed. `PTrie.allKeys` (used by `StateMeasure.acctSumOf`) is `none` as soon
   as any subtree is a hash, so it cannot measure such a trie. `nearIn` sums the revealed leaves and
   ignores hash stubs and value refs; the runtime fails (`MissingTrieValue`) on anything unrevealed
   that it touches, so unrevealed parts are identical on both sides and drop out of the identity.
   Keys are classified by their **first byte** (`kAccount = [0] ++ a`, `kAK = [2] ++ …`), not by
   their first nibble.

**Not exact conservation:** the WASM host's `one_yocto_on_promise` (`Wasm/Host.lean:480,671`) credits
1 yoctoNEAR to a promise from a zero balance, and the chunk nets it out of `balance_burnt`
(`balance_burnt = tx_burnt + other_burnt − subsidized`, `D2/RuntimeD2.lean:225-227`). The identity
below is therefore stated with `balanceBurnt`, as the block header's `total_supply` check is.
-/

namespace NearSpecV3.Conservation

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Supply

/-! ## Value of a receipt -/

/-- The gas a receipt carries (`refunds`' `tot`, `Receipts.lean:72-79`): prepaid gas, prepaid send
fees of delegated actions, prepaid exec fees and the action-receipt base exec fee. `0` on overflow
(such a receipt is rejected wherever it is processed). -/
def carriedGas (recv : Bytes) (acts : List Act) : Nat :=
  match totalPrepaidGas acts, prepaidSend acts, prepaidExec recv acts with
  | some pg, some ps, some pe => pg + ps.gas + (pe.gas + Fees.nar.exec)
  | _, _, _ => 0

/-- **NEAR held by a receipt**: its attached deposits plus its gas at the receipt's gas price.
Data and distribution receipts hold none. -/
def rcptValue (r : Rcpt) : Nat :=
  match r.body with
  | .action _ a => (totalDeposit a.actions).getD 0 + a.gasPrice * carriedGas r.recv a.actions
  | _ => 0

def rcptsValue (rs : List Rcpt) : Nat := sumNat (rs.map rcptValue)

/-! ## NEAR in the revealed part of a trie -/

mutual
/-- The revealed `(key nibbles, value)` pairs of a partial trie; hash stubs and value refs are
skipped. -/
def revealedT : PTrie → List Nat → List (List Nat × Bytes)
  | .hash _, _ => []
  | .leaf k v _, acc => match v with
    | .val b => [(acc ++ k, b)]
    | .ref _ _ => []
  | .ext k c _, acc => revealedT c (acc ++ k)
  | .branch v cs _, acc =>
    (match v with | some (.val b) => [(acc, b)] | _ => []) ++ revealedK cs 0 acc
def revealedK : Kids → Nat → List Nat → List (List Nat × Bytes)
  | .nil, _, _ => []
  | .none r, i, acc => revealedK r (i + 1) acc
  | .some c r, i, acc => revealedT c (acc ++ [i]) ++ revealedK r (i + 1) acc
end

/-- NEAR held under one trie entry, by the entry's first key byte, for shard `own` of layout `l`.

A delayed receipt counts only if it routes to `own`: after a reshard both children inherit the
parent's delayed queue, and each drops the copies that belong to its sibling (`delayPop`,
`D2/Queues.lean:459-480`, "resharding leftovers"). Counting those copies would count the same NEAR
twice across the two shards. -/
def entryNear (l : Layout) (own : Nat) (key v : Bytes) : Nat :=
  match key with
  | 0 :: _ => acctTotalOf v                                  -- account: amount + locked
  | 2 :: _ => akGasOf v                                      -- access key: gas-key balance
  | 6 :: _ :: _ | 12 :: _ :: _ =>                            -- postponed / yield receipt
    match decodeRcpt v with | .ok r => rcptValue r | .error _ => 0
  | 7 :: _ :: _ =>                                           -- delayed receipt of this shard
    match decodeStored v with
    | .ok s => if l.shardOf s.r.recv == own then rcptValue s.r else 0
    | .error _ => 0
  | 14 :: _ :: _ =>                                          -- buffered outgoing receipt
    match decodeStored v with | .ok s => rcptValue s.r | .error _ => 0
  | _ => 0

/-- **NEAR in the revealed part of a trie**: accounts, gas keys, and receipts at rest. -/
def nearIn (l : Layout) (own : Nat) (t : PTrie) : Nat :=
  sumNat ((revealedT t []).map fun (n, v) => entryNear l own (packNibbles n) v)

/-! ## The post-state of a chunk

`applyNewChunkD2` returns only the post-state *root*. `applyNewChunkD2Obs` is the same computation
returning the final overlay as well, so the post-state trie is the trie `Ovl.finalize` hashes.
`applyNewChunkD2_eq_obs` (an obligation) ties the two together. -/

/-- The trie `Ovl.finalize` hashes (`D2/State.lean:160-166`): `none` if a path is missing, `some
none` for the empty trie. -/
def finalTrie (o : Ovl) : Option (Option PTrie) :=
  let t0 : Option PTrie := match o.trie with
    | .hash h => if h == emptyRoot then none else some o.trie
    | t => some t
  applyChanges t0 (sortKV o.committed)

def nearInOpt (l : Layout) (own : Nat) : Option PTrie → Nat
  | some t => nearIn l own t
  | none => 0

/-- `applyNewChunkD2`, also returning the committed overlay that `finalize` hashes. The body is the
same as `D2/RuntimeD2.lean:173-230` with `(·, o)` on the result. -/
def applyNewChunkD2Obs (hooks : ActionHooks) (prims : Prims) (env : Env) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (lastProps : List (Bytes × Nat))
    (incoming : List Rcpt) (txs : List (TxD2 × Bool)) (ownCong : Congestion) :
    Except String (MainOutD2 × Ovl) := do
  let ctx := env.ctx
  let o := Ovl.ofTrie t
  let o ← match vu with
    | some f => validatorUpdate ctx.layout ctx.own o f lastProps
    | none => pure o
  let (df, dn) ← o.getIndices kDelayedIdx "DelayedReceiptIndices"
  let (o, so) ← schedOvl prims ctx o
  let bufIdx ← match o.trie.find (nibbles kBufIdx) with
    | none => throw (missing "BufferedReceiptIndices")
    | some none => pure []
    | some (some b) => ok? (decodeBufIdx b) (inconsistent "BufferedReceiptIndices")
  let metas ← bufIdx.foldlM (fun ms (s, _, _) => do
      match o.trie.find (nibbles (kGroupsData s)) with
      | none => throw (missing "BufferedReceiptGroupsQueueData")
      | some none => pure ms
      | some (some b) => match decodeMeta b with
        | some m => pure (ms ++ [(s, m)])
        | none => throw (inconsistent "BufferedReceiptGroupsQueueData")) []
  let limits : List Limit := ctx.statuses.map fun (s, ci, missed) =>
    ⟨s, (if s == ctx.own then GASMAX else prims.outGas ci missed ctx.own), so.grant ctx.own s⟩
  let rs : RS := { o, limits, outgoing := [], bufIdx, metas, cong := ownCong, dq := ⟨df, dn, 0, 0, 0, 0⟩,
                   outcomes := [], gas := 0, compute := 0, txBurnt := 0, otherBurnt := 0,
                   proposals := [], instant := [], locals := [] }
  let rs ← forwardFromBuffer env rs
  let (rs, _) ← txs.foldlM (processTxD2 env) (rs, [])
  let locals := rs.locals
  let rs ← processLocals hooks env { rs with locals := [] } locals
  let rs ← processDelayed hooks env (rs.dq.next - rs.dq.first + 1) rs
  let rs ← processIncoming hooks env rs incoming
  let (yf, yn) ← rs.o.getIndices kYieldIdx "PromiseYieldIndices"
  let (rs, yf') ← yieldLoop env yn (yn - yf + 1) (rs, yf, 0)
  let rs := if yf' != yf then { rs with o := rs.o.set kYieldIdx (encIndices yf' yn) } else rs
  let cong ← applyDelayedCongestion rs.dq rs.cong
  let allowed := ctx.layout.shardIds.getD ((ctx.height + (ctx.layout.index ctx.own).getD 0) % ctx.layout.numShards) ctx.own
  let cong := { cong with allowedShard := allowed }
  let bw ← bandwidthRequests env rs
  let o := rs.o.commit
  let root ← o.finalize
  let gasUsed ← ok? (sumNat64 (rs.outcomes.map (·.o.gasBurnt))) (panicked "total gas burnt overflow")
  let burnt ← ok? (add128 rs.txBurnt rs.otherBurnt) (panicked "burnt balance overflow")
  if rs.subsidized > burnt then throw "invalid: balance_burnt underflow (subsidized exceeds burnt)"
  let burnt := burnt - rs.subsidized
  pure ({ root, outcomes := rs.outcomes, outgoing := rs.outgoing, gasUsed, balanceBurnt := burnt,
          congestion := cong, bwRequests := bw, proposals := dedupProposals rs.proposals,
          cdRemovals := o.cdRemovals, wasmGas := rs.wasmGas }, o)

/-! ## The epoch reward credited on the shard -/

/-- What `validatorUpdate` (`D2/Validators.lean:36-67`) credits on the shard, read off the pre-state:
each shard stake-info entry whose account exists gets its reward (into `locked`, part of which is
then returned to `amount`), and the treasury, when it is on the shard and not a stake-info entry,
gets its reward. -/
def creditedRewards (l : Layout) (own : Nat) (t : PTrie) (f : ValidatorUpdateFacts) : Nat :=
  let onShard := fun (a : Bytes) => l.shardOf a == own
  let rewards := f.validatorRewards.filter (onShard ·.1)
  let exists_ := fun (a : Bytes) => match t.find (nibbles (kAccount a)) with
    | some (some _) => true
    | _ => false
  let stakeInfo := f.stakeInfo.filter (onShard ·.1)
  sumNat (stakeInfo.map fun (a, _) => if exists_ a then (lookupAmt rewards a).getD 0 else 0) +
  match f.treasury with
  | some tr => if onShard tr && !(stakeInfo.any (·.1 == tr)) then (lookupAmt rewards tr).getD 0 else 0
  | none => 0

def creditedOpt (l : Layout) (own : Nat) (t : PTrie) : Option ValidatorUpdateFacts → Nat
  | some f => creditedRewards l own t f
  | none => 0

/-! ## The statements -/

/-- **A D3 chunk changes the NEAR it holds only by the epoch reward and the burnt amount.**

NEAR in the pre-state plus the value of the incoming receipts plus the reward credited equals NEAR
in the post-state plus the value of the outgoing receipts plus the chunk's `balance_burnt`.
Summed over the shards of a block, every outgoing receipt is some shard's incoming receipt, so the
total changes by `Σ rewards − Σ balance_burnt` — the block header's `total_supply` identity
(`Supply.verifyTotalSupply_accept`). Transactions are internal: the signer's charge reappears as
`txBurnt` plus the value of the receipt it creates.

The two hypotheses say the chunk's inputs belong to the shard. `checkD2CoreObs` establishes the
first (it filters the incoming receipts by `L.shardOf r.recv == H.shardId`,
`ChunkValidationD2.lean:213`); the second is the chunk producer's invariant and is not checked by
`checkD2`. Without them a foreign receipt can enter this shard's delayed queue, where `nearIn` does
not count it (it is a sibling's resharding leftover by the same test that `delayPop` applies). -/
def ChunkConservation : Prop :=
  ∀ (prims : Prims) (env : Env) (t : PTrie) (vu : Option ValidatorUpdateFacts)
    (lastProps : List (Bytes × Nat)) (incoming : List Rcpt) (txs : List (TxD2 × Bool))
    (ownCong : Congestion) (out : MainOutD2) (o : Ovl),
    (∀ r ∈ incoming, env.ctx.layout.shardOf r.recv = env.ctx.own) →
    (∀ tf ∈ txs, env.ctx.layout.shardOf tf.1.signer = env.ctx.own) →
    applyNewChunkD2Obs (D3.d3Hooks Wasm.pv86) prims env t vu lastProps incoming txs ownCong
      = .ok (out, o) →
    ∃ t', finalTrie o = some t' ∧
      nearInOpt env.ctx.layout env.ctx.own t' + rcptsValue out.outgoing + out.balanceBurnt
        = nearIn env.ctx.layout env.ctx.own t + rcptsValue incoming
          + creditedOpt env.ctx.layout env.ctx.own t vu

/-- **A missing chunk changes the NEAR it holds only by the epoch reward.** -/
def MissingChunkConservation : Prop :=
  ∀ (prims : Prims) (env : Env) (t : PTrie) (vu : Option ValidatorUpdateFacts)
    (lastProps : List (Bytes × Nat)) (root : Bytes),
    applyMissingChunkD2 prims env t vu lastProps = .ok root →
    ∃ o : Ovl, ∃ t', finalTrie o = some t' ∧ o.finalize = .ok root ∧
      nearInOpt env.ctx.layout env.ctx.own t'
        = nearIn env.ctx.layout env.ctx.own t + creditedOpt env.ctx.layout env.ctx.own t vu

/-- `applyNewChunkD2Obs` is `applyNewChunkD2` with the overlay kept. -/
def ObsAgrees : Prop :=
  ∀ hooks prims env t vu lastProps incoming txs ownCong,
    applyNewChunkD2 hooks prims env t vu lastProps incoming txs ownCong
      = (applyNewChunkD2Obs hooks prims env t vu lastProps incoming txs ownCong).map (·.1)

end NearSpecV3.Conservation
