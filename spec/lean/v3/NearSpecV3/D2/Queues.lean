import NearSpecV3.D2.State
import NearSpecV3.RuntimeD1
import NearSpecV3.BandwidthScheduler

/-!
# D2 queues: receipt sink (forward / buffer, receipt groups, bandwidth requests) and the
delayed-receipt queue (spec/near-chunk-validation-d2.md §9)

The chunk-level processing state `RS` lives here: the `TrieUpdate` overlay, the receipt sink
(`ReceiptSinkV2`, `congestion_control.rs:57-500`), the delayed-queue wrapper
(`congestion_control.rs:796-944`), outcomes, totals and proposals. Every function transcribes
the cited nearcore function; `panicked` marks nearcore panics (`expect`/`unwrap`/`assert`,
`RuntimeError::UnexpectedIntegerOverflow`), which fail validation.
-/

namespace NearSpecV3.D2

open NearSpec NearSpecV3

def panicked (what : String) : String := s!"invalid: nearcore panics ({what})"

def ok? {α : Type} (o : Option α) (err : String) : Except String α :=
  match o with
  | some a => .ok a
  | none => .error err

/-- Receipt-group queue data (`ReceiptGroupsQueueDataV0`, `om.rs:213-224`). -/
structure Meta where
  first : Nat
  next : Nat
  totalSize : Nat
  totalGas : Nat
  totalNum : Nat
  deriving Repr

def Meta.encode (m : Meta) : Bytes :=
  [0] ++ u64 m.first ++ u64 m.next ++ u64 m.totalSize ++ u128 m.totalGas ++ u64 m.totalNum

def decodeMeta (b : Bytes) : Option Meta :=
  if b.length == 1 + 8 + 8 + 8 + 16 + 8 && b.head? == some 0 then
    let b := b.drop 1
    some ⟨leNat (b.take 8), leNat ((b.drop 8).take 8), leNat ((b.drop 16).take 8),
          leNat ((b.drop 24).take 16), leNat (b.drop 40)⟩
  else none

/-- `ReceiptGroup::V0 { size: u64, gas: u128 }`. -/
def encodeGroup (size gas : Nat) : Bytes := [0] ++ u64 size ++ u128 gas

def decodeGroup (b : Bytes) : Option (Nat × Nat) :=
  if b.length == 25 && b.head? == some 0 then some (leNat ((b.drop 1).take 8), leNat (b.drop 9))
  else none

/-- Delayed-queue wrapper state. -/
structure DQ where
  first : Nat
  next : Nat
  newGas : Nat
  newBytes : Nat
  remGas : Nat
  remBytes : Nat
  deriving Repr

/-- `ValidatorStake::V1(account, public_key, stake)`. -/
structure Proposal where
  acct : Bytes
  pk : PublicKey
  stake : Nat
  deriving DecidableEq, Repr

def Proposal.encode (p : Proposal) : Bytes := [0] ++ borshBytes p.acct ++ p.pk.encode ++ u128 p.stake

/-- Chunk-level apply context. The fields after `sched` (E1, E2) are read only by D3's
`FunctionCall` hook; their defaults are never observed by D2. -/
structure Env where
  ctx : ApplyCtx
  chainId : Bytes
  minStake : Nat
  sched : Scheduler.Params
  /-- E1: `B2.header.raw_timestamp()` = `inner_lite.timestamp` (`VMContext.block_timestamp`,
  `fc.rs:270`). -/
  blockTimestamp : Nat := 0
  /-- E1: `B2.header.random_value()` = `inner_rest.random_value` (random seed input,
  `fc.rs:258-259`). -/
  randomValue : Bytes := []
  /-- E1: `epoch_height` of the applied block's epoch (claim `epochs[epoch_id].epoch_height`,
  `fc.rs:271`, `rt/mod.rs:275`). -/
  epochHeight : Nat := 0
  /-- E1: the validators `(account, stake)` of the applied block's epoch (claim
  `epochs[epoch_id].validators`; `validator_stake` / `validator_total_stake`,
  `ext.rs:326-330`). -/
  validators : List (Bytes × Nat) := []
  /-- E2: the merged recorded storage `w.main.values ++ codes` keyed by SHA-256 — **every**
  `base_state` value (trie nodes and trie values) plus the appended contract-code blobs
  (`pwt.rs:693-696`, `TrieMemoryPartialStorage`, `trie_storage.rs:325-337`). The main trie
  (`Ovl.trie`) is revealed from the same list. Empty for implicit transitions. -/
  store : HStore := .tip
  /-- The main transition's pre-state root (`prev_state_root`, the root `Ovl.trie` reveals);
  `[]` for implicit transitions. -/
  preRoot : Bytes := []

/-- E2: raw lookup by hash over the merged recorded storage `w.main.values ++ codes`
(value-hash → bytes; `ContractStorage::get` → `storage.retrieve_raw_bytes`, `contract.rs:119`).
Covers every `base_state` value — trie nodes and trie values included — not only code blobs,
so it also serves trie-node walks by node hash. -/
def Env.codeOf (env : Env) (h : Bytes) : Option Bytes := hGet env.store h

structure RS where
  o : Ovl
  limits : List Limit
  outgoing : List Rcpt
  bufIdx : List (Nat × Nat × Nat)        -- BTreeMap shard → (first, next), ascending shard
  metas : List (Nat × Meta)
  cong : Congestion
  dq : DQ
  outcomes : List OutD1
  gas : Nat
  compute : Nat
  txBurnt : Nat
  otherBurnt : Nat
  proposals : List Proposal
  instant : List Rcpt
  locals : List Rcpt
  /-- E4: codes committed by `DeployContract` in earlier receipts of this chunk
  (`ContractsTracker` committed deploys, `contract.rs:42-69`); never removed. -/
  deployed : List Bytes := []
  /-- D3: every code deployed in the chunk so far, committed or rolled back (see `ActCtx.attempted`). -/
  attempted : List Bytes := []
  /-- E9: `stats.balance.subsidized` (`lib.rs:1025-1026`); `0` in D2. -/
  subsidized : Nat := 0

/-! ## `BufferedReceiptIndices` -/

def encodeBufIdx (l : List (Nat × Nat × Nat)) : Bytes :=
  u32 l.length ++ concatAll (l.map fun (s, f, n) => u64 s ++ u64 f ++ u64 n)

def bufGet (l : List (Nat × Nat × Nat)) (s : Nat) : Nat × Nat :=
  match l.find? (·.1 == s) with
  | some (_, f, n) => (f, n)
  | none => (0, 0)

def bufPut (l : List (Nat × Nat × Nat)) (s f n : Nat) : List (Nat × Nat × Nat) :=
  if l.any (·.1 == s) then l.map fun e => if e.1 == s then (s, f, n) else e
  else
    let rec ins : List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
      | [] => [(s, f, n)]
      | e :: es => if s < e.1 then (s, f, n) :: e :: es else e :: ins es
    ins l

def metaGet (ms : List (Nat × Meta)) (s : Nat) : Option Meta := (ms.find? (·.1 == s)).map (·.2)

def metaPut (ms : List (Nat × Meta)) (s : Nat) (m : Meta) : List (Nat × Meta) :=
  if ms.any (·.1 == s) then ms.map fun e => if e.1 == s then (s, m) else e else ms ++ [(s, m)]

/-! ## Receipt groups (`om.rs:275-340`) -/

def RS.setMeta (rs : RS) (s : Nat) (m : Meta) : RS :=
  { rs with metas := metaPut rs.metas s m, o := rs.o.set (kGroupsData s) m.encode }

/-- `TrieQueue::pop_back` on the groups queue. -/
def groupsPopBack (rs : RS) (s : Nat) (m : Meta) : Except String (RS × Meta × Option (Nat × Nat)) := do
  if m.first ≥ m.next then return (rs, m, none)
  let i := m.next - 1
  let raw ← rs.o.get (kGroupsItem s i) "receipt group"
  let g ← match raw with
    | none => throw (inconsistent "receipt group should be in the state")
    | some b => ok? (decodeGroup b) (inconsistent "receipt group")
  let m := { m with next := i }
  let rs := { rs with o := rs.o.remove (kGroupsItem s i) }
  pure (rs.setMeta s m, m, some g)

def groupsPushBack (rs : RS) (s : Nat) (m : Meta) (size gas : Nat) : Except String (RS × Meta) := do
  let rs := { rs with o := rs.o.set (kGroupsItem s m.next) (encodeGroup size gas) }
  let n := m.next + 1
  if n ≥ two64 then throw (panicked "Integer overflow on push")
  let m := { m with next := n }
  pure (rs.setMeta s m, m)

/-- `ReceiptGroupsQueue::update_on_receipt_pushed` (`om.rs:275-314`); groups bounded by
100 000 bytes (`ByteSize::kb(100)`, bytesize 1.1.0 `KB = 1000`) and `u64::MAX` gas. -/
def metaPushed (rs : RS) (s size gas : Nat) : Except String RS := do
  let m := (metaGet rs.metas s).getD ⟨0, 0, 0, 0, 0⟩
  if m.totalSize + size ≥ two64 then throw (panicked "add_size_checked")
  if m.totalGas + gas ≥ two128 then throw (panicked "add_gas_checked")
  if m.totalNum + 1 ≥ two64 then throw (panicked "receipt count overflow")
  let m := { m with totalSize := m.totalSize + size, totalGas := m.totalGas + gas,
                    totalNum := m.totalNum + 1 }
  let rs := { rs with metas := metaPut rs.metas s m }
  let (rs, m, last) ← groupsPopBack rs s m
  match last with
  | none => let (rs, _) ← groupsPushBack rs s m size gas; pure rs
  | some (ls, lg) =>
    if ls + size ≥ two64 then throw (panicked "add_size_checked")
    if lg + gas ≥ two128 then throw (panicked "add_gas_checked")
    if ls + size > 100000 || lg + gas > GASMAX then
      let (rs, m) ← groupsPushBack rs s m ls lg
      let (rs, _) ← groupsPushBack rs s m size gas
      pure rs
    else
      let (rs, _) ← groupsPushBack rs s m (ls + size) (lg + gas)
      pure rs

/-- `ReceiptGroupsQueue::update_on_receipt_popped` (`om.rs:316-340`) with `modify_first`
(`rch.rs:156-189`). -/
def metaPopped (rs : RS) (s size gas : Nat) : Except String RS := do
  let m ← ok? (metaGet rs.metas s) (panicked "Metadata for this shard should've been created")
  if m.totalSize < size then throw (panicked "subtract_size_checked")
  if m.totalGas < gas then throw (panicked "subtract_gas_checked")
  if m.totalNum < 1 then throw (panicked "More receipts were popped than pushed")
  let m := { m with totalSize := m.totalSize - size, totalGas := m.totalGas - gas,
                    totalNum := m.totalNum - 1 }
  if m.first ≥ m.next then throw (panicked "No receipt groups to pop from")
  let rs := { rs with metas := metaPut rs.metas s m }
  let raw ← rs.o.get (kGroupsItem s m.first) "receipt group"
  let (gs, gg) ← match raw with
    | none => throw (inconsistent "receipt group should be in the state")
    | some b => ok? (decodeGroup b) (inconsistent "receipt group")
  if gs < size then throw (panicked "subtract_size_checked")
  if gg < gas then throw (panicked "subtract_gas_checked")
  let gs := gs - size
  let gg := gg - gas
  if gs == 0 then
    if gg != 0 then throw (panicked "Gas should be zero for an empty group")
    -- pop_front: reads the item again, removes it
    let _ ← rs.o.get (kGroupsItem s m.first) "receipt group"
    let rs := { rs with o := rs.o.remove (kGroupsItem s m.first) }
    pure (rs.setMeta s { m with first := m.first + 1 })
  else
    let rs := { rs with o := rs.o.set (kGroupsItem s m.first) (encodeGroup gs gg) }
    pure (rs.setMeta s m)

/-! ## Forwarding and buffering (`congestion_control.rs:338-500`) -/

def allowedShardOutgoingGas' : Nat := 1000000000000000

/-- `try_forward`; `none` = not forwarded. -/
def tryFwd (ls : List Limit) (gas size shard : Nat) : Option (List Limit) :=
  let size := min size Lim.maxReceiptSize
  let l := Limit.get ls shard
  if l.gas ≥ min gas allowedShardOutgoingGas' && l.size ≥ size then
    some (Limit.put ls ⟨shard, l.gas - gas, l.size - size⟩)
  else none

/-- `ReceiptSinkV2::buffer_receipt` (`congestion_control.rs:466-500`). -/
def bufferReceipt (rs : RS) (r : Rcpt) (size gas shard : Nat) : Except String RS := do
  if shard > 65535 then throw (panicked "Shard ID too big")
  let c := rs.cong
  if c.receiptBytes + size ≥ two64 then throw (panicked "add_receipt_bytes")
  if c.bufferedGas + gas ≥ two128 then throw (panicked "add_buffered_receipt_gas")
  let rs := { rs with cong := { c with receiptBytes := c.receiptBytes + size,
                                       bufferedGas := c.bufferedGas + gas } }
  let rs ← metaPushed rs shard size gas
  let (f, n) := bufGet rs.bufIdx shard
  let rs := { rs with o := rs.o.set (kBuf shard n) (encodeStoredV1 r gas size) }
  if n + 1 ≥ two64 then throw (panicked "buffer index overflow")
  let bi := bufPut rs.bufIdx shard f (n + 1)
  pure { rs with bufIdx := bi, o := rs.o.set kBufIdx (encodeBufIdx bi) }

/-- `ReceiptSink::forward_or_buffer_receipt` (`congestion_control.rs:292-325`). -/
def forwardOrBuffer (env : Env) (rs : RS) (r : Rcpt) : Except String RS := do
  let shard := env.ctx.layout.shardOf r.recv
  let size := receiptSize r
  let gas ← ok? (congestionGas r) (panicked "receipt congestion gas overflow")
  match tryFwd rs.limits gas size shard with
  | some ls => pure { rs with limits := ls, outgoing := rs.outgoing ++ [r] }
  | none => bufferReceipt rs r size gas shard

/-- Gas and size of a stored receipt: from the metadata, or recomputed for a plain receipt. -/
def storedGasSize (s : Stored) : Except String (Nat × Nat) :=
  match s.md with
  | some (g, z, _) => .ok (g, z)
  | none => do
    let g ← ok? (congestionGas s.r) (panicked "receipt congestion gas overflow")
    pure (g, receiptSize s.r)

/-- Read buffered items from the *pre-state trie* (`iter(&state_update.trie, true)`). -/
def readBufferedFromTrie (o : Ovl) (s i : Nat) : Except String Stored := do
  let raw ← match o.trie.find (nibbles (kBuf s i)) with
    | some v => pure v
    | none => throw (missing "buffered receipt")
  match raw with
  | none => throw (inconsistent "TrieQueue::Item referenced by index should be in the state")
  | some b => match decodeStored b with
    | .ok st => pure st
    | .error e => if isShapeOOD e then throw e else throw (inconsistent "buffered receipt")

/-- Forward up to the first receipt that does not fit (`forward_from_buffer_to_shard`,
`congestion_control.rs:338-399`). Returns the forwarded count and metadata pops. -/
def fwdLoop (env : Env) (s : Nat) : Nat → Nat → RS × Nat × List (Nat × Nat) →
    Except String (RS × Nat × List (Nat × Nat))
  | 0, _, acc => .ok acc
  | fuel + 1, i, (rs, k, pops) => do
    let (_, n) := bufGet rs.bufIdx s
    if i ≥ n then return (rs, k, pops)
    let st ← readBufferedFromTrie rs.o s i
    let (gas, size) ← storedGasSize st
    let target := env.ctx.layout.shardOf st.r.recv
    match tryFwd rs.limits gas size target with
    | none => return (rs, k, pops)
    | some ls =>
      let c := rs.cong
      if c.receiptBytes < size then throw (panicked "remove_receipt_bytes")
      if c.bufferedGas < gas then throw (panicked "remove_buffered_receipt_gas")
      let rs := { rs with limits := ls, outgoing := rs.outgoing ++ [st.r],
                          cong := { c with receiptBytes := c.receiptBytes - size,
                                           bufferedGas := c.bufferedGas - gas } }
      let upd := match st.md with | some (_, _, 1) => true | _ => false
      fwdLoop env s fuel (i + 1) (rs, k + 1, if upd then pops ++ [(size, gas)] else pops)

def forwardFromBufferToShard (env : Env) (rs : RS) (s : Nat) : Except String RS := do
  let (f, n) := bufGet rs.bufIdx s
  let (rs, k, pops) ← fwdLoop env s (n - f) f (rs, 0, [])
  -- pop_n(k): blind removes, indices written iff k > 0
  let rs := (List.range k).foldl (fun rs j => { rs with o := rs.o.remove (kBuf s (f + j)) }) rs
  let rs := if k > 0 then
      let bi := bufPut rs.bufIdx s (f + k) n
      { rs with bufIdx := bi, o := rs.o.set kBufIdx (encodeBufIdx bi) }
    else rs
  pops.foldlM (fun rs (size, gas) => metaPopped rs s size gas) rs

/-- `forward_from_buffer` (`congestion_control.rs:236-286`): split-parent buffers first (D2
requires them empty: `c.same_layout`), then the layout's shards in order. -/
def forwardFromBuffer (env : Env) (rs : RS) : Except String RS := do
  let ids := env.ctx.layout.shardIds
  if rs.bufIdx.any (fun (s, f, n) => !ids.contains s && f < n) then
    throw "out of domain (c.same_layout): outgoing buffer to a shard outside the layout"
  ids.foldlM (forwardFromBufferToShard env) rs

/-! ## Bandwidth requests (`congestion_control.rs:503-610`, `bandwidth_scheduler.rs:81-127`) -/

def setBit (bm : List UInt8) (i : Nat) : List UInt8 :=
  bm.set (i / 8) (UInt8.ofNat ((bm.getD (i / 8) 0).toNat ||| (1 <<< (i % 8))))

/-- `BandwidthRequest::make_from_receipt_sizes`. -/
def makeRequest (p : Scheduler.Params) (sizes : List Nat) : List UInt8 :=
  let vals := Scheduler.requestValues p
  let rec go : List Nat → Nat → Nat → List UInt8 → List UInt8
    | [], _, _, bm => bm
    | s :: rest, total, idx, bm =>
      let total := total + s
      if total ≤ p.base then go rest total idx bm
      else
        let idx' := idx + ((vals.drop idx).takeWhile (· < total)).length
        if idx' ≥ vals.length then bm
        else go rest total idx' (setBit bm idx')
  go (sizes.map fun s => min s p.maxReceiptSize) 0 0 [0, 0, 0, 0, 0]

def groupSizes (o : Ovl) (s : Nat) : Nat → Nat → Except String (List Nat)
  | 0, _ => .ok []
  | fuel + 1, i => do
    let raw ← o.get (kGroupsItem s i) "receipt group"
    let (sz, _) ← match raw with
      | none => throw (inconsistent "TrieQueue::Item referenced by index should be in the state")
      | some b => ok? (decodeGroup b) (inconsistent "receipt group")
    pure (sz :: (← groupSizes o s fuel (i + 1)))

def bandwidthRequests (env : Env) (rs : RS) : Except String (List BwRequest) := do
  let reqs ← env.ctx.layout.shardIds.mapM fun s => do
    let (f, n) := bufGet rs.bufIdx s
    if n ≤ f then return none
    let len := n - f
    let sizes ← match metaGet rs.metas s with
      | some m => if m.totalNum == len then groupSizes rs.o s (m.next - m.first) m.first
                  else pure [env.sched.maxReceiptSize]
      | none => pure [env.sched.maxReceiptSize]
    let bm := makeRequest env.sched sizes
    if bm.all (· == 0) then return none
    pure (some (⟨s, bm⟩ : BwRequest))
  pure reqs.reduceOption

/-! ## Delayed receipts (`congestion_control.rs:838-944`, `rch.rs:83-123`) -/

def RS.writeDelayedIdx (rs : RS) : RS :=
  { rs with o := rs.o.set kDelayedIdx (encIndices rs.dq.first rs.dq.next) }

/-- `DelayedReceiptQueueWrapper::push`. -/
def delayPush (rs : RS) (r : Rcpt) : Except String RS := do
  let gas ← ok? (congestionGas r) (panicked "receipt congestion gas overflow")
  let size := receiptSize r
  let dq := rs.dq
  if dq.newGas + gas ≥ two64 then throw (panicked "delayed gas overflow")
  if dq.newBytes + size ≥ two64 then throw (panicked "delayed bytes overflow")
  if dq.next + 1 ≥ two64 then throw (panicked "delayed index overflow")
  let rs := { rs with o := rs.o.set (kDelayed dq.next) (encodeStoredV1 r gas size),
                      dq := { dq with next := dq.next + 1, newGas := dq.newGas + gas,
                                      newBytes := dq.newBytes + size } }
  pure rs.writeDelayedIdx

/-- `DelayedReceiptQueueWrapper::pop`: pops until a receipt of this shard (others — resharding
leftovers — are dropped but still accounted). -/
def delayPop (env : Env) : Nat → RS → Except String (RS × Option Rcpt)
  | 0, rs => .ok (rs, none)
  | fuel + 1, rs => do
    let dq := rs.dq
    if dq.first ≥ dq.next then return (rs, none)
    let raw ← rs.o.get (kDelayed dq.first) "delayed receipt"
    let st ← match raw with
      | none => throw (inconsistent "TrieQueue::Item should be in the state")
      | some b => match decodeStored b with
        | .ok st => pure st
        | .error e => if isShapeOOD e then throw e else throw (inconsistent "delayed receipt")
    let (gas, size) ← storedGasSize st
    if dq.remGas + gas ≥ two64 then throw (panicked "removed delayed gas overflow")
    if dq.remBytes + size ≥ two64 then throw (panicked "removed delayed bytes overflow")
    let rs := { rs with o := rs.o.remove (kDelayed dq.first),
                        dq := { dq with first := dq.first + 1, remGas := dq.remGas + gas,
                                        remBytes := dq.remBytes + size } }
    let rs := rs.writeDelayedIdx
    if env.ctx.layout.shardOf st.r.recv == env.ctx.own then pure (rs, some st.r)
    else delayPop env fuel rs

/-- `apply_congestion_changes` (adds before subtracts; underflow / overflow panics). -/
def applyDelayedCongestion (dq : DQ) (c : Congestion) : Except String Congestion := do
  let g := c.delayedGas + dq.newGas
  if g ≥ two128 then throw (panicked "add_delayed_receipt_gas")
  if g < dq.remGas then throw (panicked "remove_delayed_receipt_gas")
  let b := c.receiptBytes + dq.newBytes
  if b ≥ two64 then throw (panicked "add_receipt_bytes")
  if b < dq.remBytes then throw (panicked "remove_receipt_bytes")
  pure { c with delayedGas := g - dq.remGas, receiptBytes := b - dq.remBytes }

end NearSpecV3.D2
