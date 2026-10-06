import NearSpecV3.Logged.D2State

/-!
# Mirror of `D2/Queues.lean` in `LM`

Line for line the functions of `D2/Queues.lean`; recorded-storage reads go through `Ovl.getL` /
`trieFindL`. Functions that never read storage are reused as they are (`liftE`).
-/

namespace NearSpecV3.D2

open NearSpec NearSpecV3 NearSpecV3.Logged

/-- An `Except` computation inside `LM` (no store access). -/
def liftE {α : Type} : Except String α → LM α
  | .ok a => pure a
  | .error e => throw e

@[reducible] def RS.wt (rs : RS) (t : PTrie) : RS := { rs with o := rs.o.wt t }

def groupsPopBackL (rs : RS) (s : Nat) (m : Meta) : LM (RS × Meta × Option (Nat × Nat)) := do
  if m.first ≥ m.next then return (rs, m, none)
  let i := m.next - 1
  let raw ← rs.o.getL (kGroupsItem s i) "receipt group"
  let g ← match raw with
    | none => throw (inconsistent "receipt group should be in the state")
    | some b => LM.okL (decodeGroup b) (inconsistent "receipt group")
  let m := { m with next := i }
  let rs := { rs with o := rs.o.remove (kGroupsItem s i) }
  pure (rs.setMeta s m, m, some g)

def groupsPushBackL (rs : RS) (s : Nat) (m : Meta) (size gas : Nat) : LM (RS × Meta) := do
  let rs := { rs with o := rs.o.set (kGroupsItem s m.next) (encodeGroup size gas) }
  let n := m.next + 1
  if n ≥ two64 then throw (panicked "Integer overflow on push")
  let m := { m with next := n }
  pure (rs.setMeta s m, m)

def metaPushedL (rs : RS) (s size gas : Nat) : LM RS := do
  let m := (metaGet rs.metas s).getD ⟨0, 0, 0, 0, 0⟩
  if m.totalSize + size ≥ two64 then throw (panicked "add_size_checked")
  if m.totalGas + gas ≥ two128 then throw (panicked "add_gas_checked")
  if m.totalNum + 1 ≥ two64 then throw (panicked "receipt count overflow")
  let m := { m with totalSize := m.totalSize + size, totalGas := m.totalGas + gas,
                    totalNum := m.totalNum + 1 }
  let rs := { rs with metas := metaPut rs.metas s m }
  let (rs, m, last) ← groupsPopBackL rs s m
  match last with
  | none => let (rs, _) ← groupsPushBackL rs s m size gas; pure rs
  | some (ls, lg) =>
    if ls + size ≥ two64 then throw (panicked "add_size_checked")
    if lg + gas ≥ two128 then throw (panicked "add_gas_checked")
    if ls + size > 100000 || lg + gas > GASMAX then
      let (rs, m) ← groupsPushBackL rs s m ls lg
      let (rs, _) ← groupsPushBackL rs s m size gas
      pure rs
    else
      let (rs, _) ← groupsPushBackL rs s m (ls + size) (lg + gas)
      pure rs

def metaPoppedL (rs : RS) (s size gas : Nat) : LM RS := do
  let m ← LM.okL (metaGet rs.metas s) (panicked "Metadata for this shard should've been created")
  if m.totalSize < size then throw (panicked "subtract_size_checked")
  if m.totalGas < gas then throw (panicked "subtract_gas_checked")
  if m.totalNum < 1 then throw (panicked "More receipts were popped than pushed")
  let m := { m with totalSize := m.totalSize - size, totalGas := m.totalGas - gas,
                    totalNum := m.totalNum - 1 }
  if m.first ≥ m.next then throw (panicked "No receipt groups to pop from")
  let rs := { rs with metas := metaPut rs.metas s m }
  let raw ← rs.o.getL (kGroupsItem s m.first) "receipt group"
  let (gs, gg) ← match raw with
    | none => throw (inconsistent "receipt group should be in the state")
    | some b => LM.okL (decodeGroup b) (inconsistent "receipt group")
  if gs < size then throw (panicked "subtract_size_checked")
  if gg < gas then throw (panicked "subtract_gas_checked")
  let gs := gs - size
  let gg := gg - gas
  if gs == 0 then
    if gg != 0 then throw (panicked "Gas should be zero for an empty group")
    let _ ← rs.o.getL (kGroupsItem s m.first) "receipt group"
    let rs := { rs with o := rs.o.remove (kGroupsItem s m.first) }
    pure (rs.setMeta s { m with first := m.first + 1 })
  else
    let rs := { rs with o := rs.o.set (kGroupsItem s m.first) (encodeGroup gs gg) }
    pure (rs.setMeta s m)

def bufferReceiptL (rs : RS) (r : Rcpt) (size gas shard : Nat) : LM RS := do
  if shard > 65535 then throw (panicked "Shard ID too big")
  let c := rs.cong
  if c.receiptBytes + size ≥ two64 then throw (panicked "add_receipt_bytes")
  if c.bufferedGas + gas ≥ two128 then throw (panicked "add_buffered_receipt_gas")
  let rs := { rs with cong := { c with receiptBytes := c.receiptBytes + size,
                                       bufferedGas := c.bufferedGas + gas } }
  let rs ← metaPushedL rs shard size gas
  let (f, n) := bufGet rs.bufIdx shard
  let rs := { rs with o := rs.o.set (kBuf shard n) (encodeStoredV1 r gas size) }
  if n + 1 ≥ two64 then throw (panicked "buffer index overflow")
  let bi := bufPut rs.bufIdx shard f (n + 1)
  pure { rs with bufIdx := bi, o := rs.o.set kBufIdx (encodeBufIdx bi) }

def forwardOrBufferL (env : Env) (rs : RS) (r : Rcpt) : LM RS := do
  let shard := env.ctx.layout.shardOf r.recv
  let size := receiptSize r
  let gas ← LM.okL (congestionGas r) (panicked "receipt congestion gas overflow")
  match tryFwd rs.limits gas size shard with
  | some ls => pure { rs with limits := ls, outgoing := rs.outgoing ++ [r] }
  | none => bufferReceiptL rs r size gas shard

def readBufferedFromTrieL (s i : Nat) : LM Stored := do
  let raw ← match ← trieFindL (kBuf s i) with
    | some v => pure v
    | none => throw (missing "buffered receipt")
  match raw with
  | none => throw (inconsistent "TrieQueue::Item referenced by index should be in the state")
  | some b => match decodeStored b with
    | .ok st => pure st
    | .error e => if isShapeOOD e then throw e else throw (inconsistent "buffered receipt")

def fwdLoopL (env : Env) (s : Nat) : Nat → Nat → RS × Nat × List (Nat × Nat) →
    LM (RS × Nat × List (Nat × Nat))
  | 0, _, acc => pure acc
  | fuel + 1, i, (rs, k, pops) => do
    let (_, n) := bufGet rs.bufIdx s
    if i ≥ n then return (rs, k, pops)
    let st ← readBufferedFromTrieL s i
    let (gas, size) ← liftE (storedGasSize st)
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
      fwdLoopL env s fuel (i + 1) (rs, k + 1, if upd then pops ++ [(size, gas)] else pops)

def forwardFromBufferToShardL (env : Env) (rs : RS) (s : Nat) : LM RS := do
  let (f, n) := bufGet rs.bufIdx s
  let (rs, k, pops) ← fwdLoopL env s (n - f) f (rs, 0, [])
  let rs := (List.range k).foldl (fun rs j => { rs with o := rs.o.remove (kBuf s (f + j)) }) rs
  let rs := if k > 0 then
      let bi := bufPut rs.bufIdx s (f + k) n
      { rs with bufIdx := bi, o := rs.o.set kBufIdx (encodeBufIdx bi) }
    else rs
  pops.foldlM (fun rs (size, gas) => metaPoppedL rs s size gas) rs

def forwardFromBufferL (env : Env) (rs : RS) : LM RS := do
  let ids := env.ctx.layout.shardIds
  if rs.bufIdx.any (fun (s, f, n) => !ids.contains s && f < n) then
    throw "out of domain (c.same_layout): outgoing buffer to a shard outside the layout"
  ids.foldlM (forwardFromBufferToShardL env) rs

def groupSizesL (o : Ovl) (s : Nat) : Nat → Nat → LM (List Nat)
  | 0, _ => pure []
  | fuel + 1, i => do
    let raw ← o.getL (kGroupsItem s i) "receipt group"
    let (sz, _) ← match raw with
      | none => throw (inconsistent "TrieQueue::Item referenced by index should be in the state")
      | some b => LM.okL (decodeGroup b) (inconsistent "receipt group")
    pure (sz :: (← groupSizesL o s fuel (i + 1)))

def bandwidthRequestsL (env : Env) (rs : RS) : LM (List BwRequest) := do
  let reqs ← env.ctx.layout.shardIds.mapM fun s => do
    let (f, n) := bufGet rs.bufIdx s
    if n ≤ f then return none
    let len := n - f
    let sizes ← match metaGet rs.metas s with
      | some m => if m.totalNum == len then groupSizesL rs.o s (m.next - m.first) m.first
                  else pure [env.sched.maxReceiptSize]
      | none => pure [env.sched.maxReceiptSize]
    let bm := makeRequest env.sched sizes
    if bm.all (· == 0) then return none
    pure (some (⟨s, bm⟩ : BwRequest))
  pure reqs.reduceOption

def delayPushL (rs : RS) (r : Rcpt) : LM RS := do
  let gas ← LM.okL (congestionGas r) (panicked "receipt congestion gas overflow")
  let size := receiptSize r
  let dq := rs.dq
  if dq.newGas + gas ≥ two64 then throw (panicked "delayed gas overflow")
  if dq.newBytes + size ≥ two64 then throw (panicked "delayed bytes overflow")
  if dq.next + 1 ≥ two64 then throw (panicked "delayed index overflow")
  let rs := { rs with o := rs.o.set (kDelayed dq.next) (encodeStoredV1 r gas size),
                      dq := { dq with next := dq.next + 1, newGas := dq.newGas + gas,
                                      newBytes := dq.newBytes + size } }
  pure rs.writeDelayedIdx

def delayPopL (env : Env) : Nat → RS → LM (RS × Option Rcpt)
  | 0, rs => pure (rs, none)
  | fuel + 1, rs => do
    let dq := rs.dq
    if dq.first ≥ dq.next then return (rs, none)
    let raw ← rs.o.getL (kDelayed dq.first) "delayed receipt"
    let st ← match raw with
      | none => throw (inconsistent "TrieQueue::Item should be in the state")
      | some b => match decodeStored b with
        | .ok st => pure st
        | .error e => if isShapeOOD e then throw e else throw (inconsistent "delayed receipt")
    let (gas, size) ← liftE (storedGasSize st)
    if dq.remGas + gas ≥ two64 then throw (panicked "removed delayed gas overflow")
    if dq.remBytes + size ≥ two64 then throw (panicked "removed delayed bytes overflow")
    let rs := { rs with o := rs.o.remove (kDelayed dq.first),
                        dq := { dq with first := dq.first + 1, remGas := dq.remGas + gas,
                                        remBytes := dq.remBytes + size } }
    let rs := rs.writeDelayedIdx
    if env.ctx.layout.shardOf st.r.recv == env.ctx.own then pure (rs, some st.r)
    else delayPopL env fuel rs

end NearSpecV3.D2
