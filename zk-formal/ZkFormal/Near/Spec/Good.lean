import ZkFormal.Near.Spec.Trie

/-!
# ZkFormal.Near.Spec.Good — the relational intermediate spec of `NearRelation`

`Good c e` is what the AIR establishes about an extracted `Ext` (NEAR-AIR.md
§4): the revealed trie as records (`Spec.Trie`), the receipts, the slot each
receipt's walk reaches, and the batch run in *flat* form — amounts per slot
as sums of earlier deposits (`amtAt`), per-receipt arithmetic facts, and the
public outputs as functions of these.  It mirrors `runBatch`/`applyReceipt`
with the trie walk replaced by the slot (the arena view of reexec-npai), so
that

* `good_sound : Good c e → NearRelation c (witnessOf e)` is pure NEAR-level
  reasoning (tree hashing, `get`/`set` along walks, the run), and
* the AIR side only has to produce the flat facts.
-/

namespace ZkFormal.Near

open NearSpec NearSpec.TransferV1

/-- Data extracted from an accepted trace (or built from a witness). -/
structure Ext where
  /-- revealed trie nodes, root = node `0` -/
  ns : List NodeRec
  /-- pre-state value bytes of touched slots (indexed by node id) -/
  vals0 : Nat → Bytes
  /-- the receipts, in batch order -/
  rs : List Receipt
  /-- the touched slot (node id) receipt `r`'s walk reaches -/
  slot : Nat → Nat

namespace Ext
variable (e : Ext)

/-- Pre-state account of slot `k`. -/
def acc0 (k : Nat) : Account := (Account.decode (e.vals0 k)).getD ⟨0, 0, [], 0⟩

/-- Receipt `r` (default when out of range). -/
def rc (r : Nat) : Receipt := e.rs.getD r ⟨[], [], [], [], ⟨0, []⟩, 0, 0⟩

/-- Amount of slot `k` before receipt `r` is applied. -/
def amtAt (k : Nat) : Nat → Nat
  | 0 => (e.acc0 k).amount
  | r + 1 => amtAt k r + (if e.slot r = k then (e.rc r).deposit else 0)

/-- Value bytes of slot `k` before receipt `r`. -/
def valsAt (r k : Nat) : Bytes := Account.encode { e.acc0 k with amount := e.amtAt k r }

end Ext

/-- `gas_burn_price` and the burnt / refunded amounts of a receipt. -/
def burnPrice (bgp : Nat) (rc : Receipt) : Nat := min rc.gasPrice bgp
def burntOf (bgp : Nat) (rc : Receipt) : Nat := Params.G * burnPrice bgp rc
def surplusOf (bgp : Nat) (rc : Receipt) : Nat := Params.G * (rc.gasPrice - burnPrice bgp rc)

namespace Ext
variable (e : Ext) (c : Claim)

/-- `tokens_burnt` before receipt `r`. -/
def tokAt : Nat → Nat
  | 0 => 0
  | r + 1 => tokAt r + burntOf c.blockGasPrice (e.rc r)

/-- The gas-refund receipt receipt `r` generates (none if no surplus). -/
def refundOf (r : Nat) : List Receipt :=
  let s := surplusOf c.blockGasPrice (e.rc r)
  if s = 0 then [] else [gasRefundReceipt (e.rc r) c.blockHeight s]

def outcomeOf (r : Nat) : Outcome :=
  { id := (e.rc r).receiptId, receiptIds := (e.refundOf c r).map Receipt.receiptId,
    gasBurnt := Params.G, tokensBurnt := burntOf c.blockGasPrice (e.rc r),
    executorId := (e.rc r).receiverId }

def outcomes : List Outcome := (List.range e.rs.length).map (e.outcomeOf c)
def refunds : List Receipt := (List.range e.rs.length).flatMap (e.refundOf c)

end Ext

/-- Per-receipt checks of `applyReceipt` in flat form (receipt `r`, slot `k`). -/
structure RcptOk (c : Claim) (e : Ext) (r : Nat) : Prop where
  amt_lt : e.amtAt (e.slot r) r + (e.rc r).deposit < Params.u128Max
  tot_lt : e.amtAt (e.slot r) r + (e.rc r).deposit + (e.acc0 (e.slot r)).locked < Params.two128
  stake : Params.storageAmountPerByte * (e.acc0 (e.slot r)).storageUsage ≤
            e.amtAt (e.slot r) r + (e.rc r).deposit + (e.acc0 (e.slot r)).locked ∨
          (e.acc0 (e.slot r)).storageUsage ≤ Params.zeroBalanceStorageLimit
  burnt_lt : burntOf c.blockGasPrice (e.rc r) < Params.two128
  surplus_lt : surplusOf c.blockGasPrice (e.rc r) < Params.two128
  tok_lt : e.tokAt c r + burntOf c.blockGasPrice (e.rc r) < Params.two128

/-- **The relational spec.** -/
structure Good (c : Claim) (e : Ext) : Prop where
  -- claim-level facts (DomainStatic, the parts readable from the claim)
  pv : c.protocolVersion = Params.protocolVersion
  chain : c.chainId = Params.chainId
  n_pos : 1 ≤ c.receiptCount
  n_le : c.receiptCount ≤ Params.maxBatch
  gas_limit : (c.receiptCount - 1) * Params.G < c.gasLimit
  gas_total : c.gasBurntTotal = c.receiptCount * Params.G
  -- receipts
  len : e.rs.length = c.receiptCount
  inSlice : e.rs.all Receipt.inSlice = true
  nodup : (e.rs.map Receipt.receiptId).Nodup
  rcCommit : receiptsCommitment c.shardId e.rs = c.receiptsCommitment
  -- the revealed trie
  shape : TreeShape e.ns
  nodes_wf : ∀ nr ∈ e.ns, nr.wf
  vals_len : ∀ k nr, e.ns[k]? = some nr → nr.touched = true → (e.vals0 k).length = 72
  vals_v1 : ∀ k nr, e.ns[k]? = some nr → nr.touched = true → (Account.decode (e.vals0 k)).isSome
  preRoot : (trieOf e.ns e.vals0).hashOf = c.preStateRoot
  size : revealedOf e.ns ≤ Params.maxWitnessBytes
  -- walks: each receipt's account key reaches its slot
  walks : ∀ r, r < e.rs.length → WalkTo e.ns (accountKeyPath (e.rc r).receiverId) (e.slot r)
  -- the run
  rcpt_ok : ∀ r, r < e.rs.length → RcptOk c e r
  -- outputs
  postRoot : (trieOf e.ns (e.valsAt e.rs.length)).hashOf = c.slicePostRoot
  outRoot : outcomeRoot (e.outcomes c) = c.outcomeRoot
  refundCount : (e.refunds c).length = c.refundCount
  rfCommit : refundsCommitment (e.refunds c) = c.refundsCommitment
  tokens : e.tokAt c e.rs.length = c.tokensBurntTotal

/-- The witness an `Ext` denotes. -/
def witnessOf (e : Ext) : Witness := ⟨e.rs, trieOf e.ns e.vals0⟩

end ZkFormal.Near
