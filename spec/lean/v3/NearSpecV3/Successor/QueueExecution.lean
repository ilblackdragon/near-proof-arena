import NearSpecV3.Logged.D2Queues

/-! Queue execution parameterized only by stored-receipt decoding and routing.
The metadata, limits, gas/size and authenticated read operations reuse the logged D2 runtime.
-/
namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged

structure QueuePolicy where
  decodeStored : Bytes → Except String D2.Stored
  target : Layout → Rcpt → Except String Nat

def forwardOrBufferLWith (policy : QueuePolicy) (env : Env) (rs : RS) (r : Rcpt) : LM RS := do
  let shard ← liftE (policy.target env.ctx.layout r)
  let size := receiptSize r
  let gas ← LM.okL (congestionGas r) (panicked "receipt congestion gas overflow")
  match tryFwd rs.limits gas size shard with
  | some ls => pure { rs with limits := ls, outgoing := rs.outgoing ++ [r] }
  | none => bufferReceiptL rs r size gas shard

def readBufferedFromTrieLWith (policy : QueuePolicy) (s i : Nat) : LM Stored := do
  let raw ← match ← trieFindL (kBuf s i) with
    | some v => pure v
    | none => throw (missing "buffered receipt")
  match raw with
  | none => throw (inconsistent "TrieQueue::Item referenced by index should be in the state")
  | some b => match policy.decodeStored b with
    | .ok st => pure st
    | .error e => if isShapeOOD e then throw e else throw (inconsistent "buffered receipt")

def fwdLoopLWith (policy : QueuePolicy) (env : Env) (s : Nat) : Nat → Nat → RS × Nat × List (Nat × Nat) →
    LM (RS × Nat × List (Nat × Nat))
  | 0, _, acc => pure acc
  | fuel + 1, i, (rs, k, pops) => do
    let (_, n) := bufGet rs.bufIdx s
    if i ≥ n then return (rs, k, pops)
    let st ← readBufferedFromTrieLWith policy s i
    let (gas, size) ← liftE (storedGasSize st)
    let target ← liftE (policy.target env.ctx.layout st.r)
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
      fwdLoopLWith policy env s fuel (i + 1) (rs, k + 1, if upd then pops ++ [(size, gas)] else pops)

def forwardFromBufferToShardLWith (policy : QueuePolicy) (env : Env) (rs : RS) (s : Nat) : LM RS := do
  let (f, n) := bufGet rs.bufIdx s
  let (rs, k, pops) ← fwdLoopLWith policy env s (n - f) f (rs, 0, [])
  let rs := (List.range k).foldl (fun rs j => { rs with o := rs.o.remove (kBuf s (f + j)) }) rs
  let rs := if k > 0 then
      let bi := bufPut rs.bufIdx s (f + k) n
      { rs with bufIdx := bi, o := rs.o.set kBufIdx (encodeBufIdx bi) }
    else rs
  pops.foldlM (fun rs (size, gas) => metaPoppedL rs s size gas) rs

def forwardFromBufferLWith (policy : QueuePolicy) (env : Env) (rs : RS) : LM RS := do
  let ids := env.ctx.layout.shardIds
  if rs.bufIdx.any (fun (s, f, n) => !ids.contains s && f < n) then
    throw "out of domain (c.same_layout): outgoing buffer to a shard outside the layout"
  ids.foldlM (forwardFromBufferToShardLWith policy env) rs

def delayPopLWith (policy : QueuePolicy) (env : Env) : Nat → RS → LM (RS × Option Rcpt)
  | 0, rs => pure (rs, none)
  | fuel + 1, rs => do
    let dq := rs.dq
    if dq.first ≥ dq.next then return (rs, none)
    let raw ← rs.o.getL (kDelayed dq.first) "delayed receipt"
    let st ← match raw with
      | none => throw (inconsistent "TrieQueue::Item should be in the state")
      | some b => match policy.decodeStored b with
        | .ok st => pure st
        | .error e => if isShapeOOD e then throw e else throw (inconsistent "delayed receipt")
    let (gas, size) ← liftE (storedGasSize st)
    if dq.remGas + gas ≥ two64 then throw (panicked "removed delayed gas overflow")
    if dq.remBytes + size ≥ two64 then throw (panicked "removed delayed bytes overflow")
    let rs := { rs with o := rs.o.remove (kDelayed dq.first),
                        dq := { dq with first := dq.first + 1, remGas := dq.remGas + gas,
                                        remBytes := dq.remBytes + size } }
    let rs := rs.writeDelayedIdx
    let target ← liftE (policy.target env.ctx.layout st.r)
    if target == env.ctx.own then pure (rs, some st.r)
    else delayPopLWith policy env fuel rs

end NearSpecV3.Successor
