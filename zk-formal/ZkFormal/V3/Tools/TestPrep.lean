import ZkFormal.V3.Fast.Prep

/-!
`nearspec-v3-test-prep CASE_DIR...` — executable test of `NearSpecV3.prepD0` / `hintOf`
(V3-D0-DESIGN §1, §2.1, §6.1, §11) against the amended relation `checkD0a` (= `RelD0a`) on
real cases. Compiled with the candidate-side fast paths (`ZkFormal.V3.Fast.*`).

Per case: `r := checkD0a cb wb`, `h := hintOf cb wb`, `p := prepD0 cb h`.

* `r = ok` (RelD0a): `p` must be `ok`, and every prepared value must equal the value the
  relation's own execution computes, re-run here independently of `prepD0`: applied receipts
  rebuilt from `p.lists` against the witness entries and hashed to `applied_receipts_hash`;
  from-shard and Merkle path of each list; `n`, gas, roots, outcome root, burnt; the body;
  **scheduler split**: for every applied block τ, `Scheduler.runCore p.sched[τ] v_τ` (with
  `v_τ` the `0x0f` value the run reads) writes exactly the `0x0f` value found in the post
  trie of `applyNewChunk` / `applyMissingChunk`; **forwarding split**: every `(s, total)` of
  `p.fwd` is `≤ grant(own, s)` of the τ = 0 run; routing intervals vs `Layout.shardOf`.
* `r = error m` from a claim/hint (C/H) check: `p` must fail with the same category; for
  `e.forwarded`, `p` may instead succeed with a `p.fwd` total above the AIR-side grant
  (size part of the split), which is then checked here.
* `r = error m` from a witness/AIR (W) check: no requirement; counted.
-/

open NearSpec NearSpec.TransferV1 NearSpecV3

def wPrefixes : List String :=
  ["out of domain (w.", "out of domain (r.", "out of domain (e.distinct_ids)",
   "out of domain (e.queues_empty)", "out of domain (e.sched_canonical)",
   "invalid: witness chunk header", "invalid: epoch id", "invalid: missing source receipt proof",
   "invalid: receipt proof", "invalid: source_receipt_proofs", "invalid: applied receipts hash",
   "invalid: MissingTrieValue", "invalid: main base_state", "invalid: main transition post",
   "invalid: implicit transition", "invalid: InvalidStateRoot", "invalid: InvalidOutcomesProof",
   "invalid: InvalidBalanceBurnt", "invalid: account path not revealed",
   "invalid: bandwidth scheduler aborted", "invalid: StorageInconsistentState",
   "decode: truncated shard_buffers", "decode: truncated shard", "decode: truncated first",
   "decode: truncated next"]

def category (m : String) : String := if m.startsWith "out of domain" then "ood" else "invalid"

def witnessHeadOk (cb wb : Bytes) : Bool :=
  match decodeClaimE cb, decodeWitnessFile wb with
  | .ok c, .ok (sw, codes) =>
    codes.isEmpty && lenT sw ≤ 8388608 &&
    (match decodeStateWitness sw with
     | .ok w => w.innerBytes == c.chunkInner && w.epochId == c.epochId
     | .error _ => false)
  | _, _ => false

def findD (t : PTrie) (k : List Nat) : Option Bytes := (t.find k).getD none

structure Tr where
  w : StateWitness
  k : WalkD0
  receipts : List Receipt
  tMain : PTrie
  out : MainOut
  ctxB2 : ApplyCtx
  impl : List (PTrie × PTrie)     -- (pre, post) per implicit transition

def trace (cb wb : Bytes) : Except String Tr := do
  let k ← walkD0 cb
  let w ← decodeW wb
  let B2 ← match k.blks[k.b2i]? with | some b => pure b | none => throw "walk"
  let prevB2 ← match k.blks[k.b2i + 1]? with | some b => pure b | none => throw "walk"
  let receipts := appliedReceipts k w
  let ctxB2 := blockCtx k.L k.H.shardId k.slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let t0 := partialTrie w.main.values k.slotB2.prevStateRoot [keyBufferedIdx]
  let bshards ← match t0.find keyBufferedIdx with
    | some v => bufferedShards v | none => throw "missing"
  let tMain := partialTrie w.main.values k.slotB2.prevStateRoot (mainKeys receipts bshards)
  let out ← applyNewChunk prims ctxB2 tMain receipts
  let mut root := out.trie.hashOf
  let mut impl : List (PTrie × PTrie) := []
  for (M, T) in k.implicitBlks.zip w.implicit do
    let ctxM := blockCtx k.L k.H.shardId k.slotB2.gasLimit M M.hdr.nextGasPrice
    let tM := partialTrie T.values root [keyDelayedIdx, keyBwState]
    let tM' ← applyMissingChunk prims ctxM tM
    impl := impl ++ [(tM, tM')]
    root := tM'.hashOf
  pure ⟨w, k, receipts, tMain, out, ctxB2, impl⟩

def grantOf (o : Scheduler.Output) (a b : Nat) : Nat :=
  ((o.granted.find? (·.1 == (a, b))).map (·.2)).getD 0

def compare (p : Prep) (t : Tr) : List String := Id.run do
  let mut bad : List String := []
  let own := t.k.H.shardId
  let entries := p.lists.map fun s => lookupLast s.key t.w.entries
  if entries.any Option.isNone then bad := bad ++ ["lists: key without witness entry"]
  let es := entries.filterMap id
  let rebuilt := (es.map fun e => e.receipts.filter fun r => t.k.L.shardOf r.receiverId == own).flatten
  if sha256 (encodeReceipts rebuilt) != t.w.appliedReceiptsHash then bad := bad ++ ["lists: applied receipts hash"]
  if rebuilt != t.receipts then bad := bad ++ ["lists: applied order"]
  if !((p.lists.zip es).all fun (s, e) => e.proof.fromShard == s.fromShard && verifyReceiptProof s.root e) then
    bad := bad ++ ["lists: from_shard / path"]
  if p.lists.length != (distinctKeys t.w.entries).length then bad := bad ++ ["lists: count"]
  if p.hdr.n != t.receipts.length then bad := bad ++ ["n"]
  if p.hdr.n * Params.G != t.out.gasUsed then bad := bad ++ ["gas used"]
  if p.hdr.prevStateRoot != t.tMain.hashOf then bad := bad ++ ["prev_state_root"]
  let finalRoot := (t.impl.getLast?.map (·.2.hashOf)).getD t.out.trie.hashOf
  if p.hdr.postStateRoot != finalRoot then bad := bad ++ ["post_state_root"]
  if p.hdr.outcomeRoot != outcomeRoot t.out.outcomes then bad := bad ++ ["outcome root"]
  if p.hdr.balanceBurnt != t.out.tokensBurnt then bad := bad ++ ["balance burnt"]
  if p.hdr.K != t.impl.length then bad := bad ++ ["K"]
  if p.hdr.height != t.ctxB2.height || p.hdr.gasPrice != t.ctxB2.gasPrice || p.hdr.gasLimit != t.ctxB2.gasLimit then
    bad := bad ++ ["ctx"]
  if p.body != u32 0 ++ encodeReceipts t.out.outgoing then bad := bad ++ ["body"]
  -- scheduler split: runCore(pub_τ, value read) writes the value in the post trie
  let pres := t.tMain :: t.impl.map (·.1)
  let posts := t.out.trie :: t.impl.map (·.2)
  if p.sched.length != pres.length then bad := bad ++ ["sched: count"]
  let ok := ((p.sched.zip (pres.zip posts)).all fun (pub, pre, post) =>
    match Scheduler.runCore pub (findD pre keyBwState) with
    | some o => post.find keyBwState == some (some o.state)
    | none => false)
  if !ok then bad := bad ++ ["sched: runCore state"]
  -- forwarding split
  match p.sched.head? with
  | some pub =>
    match Scheduler.runCore pub (findD t.tMain keyBwState) with
    | some o =>
      if !(p.fwd.all fun (s, tot) => tot ≤ grantOf o own s) then bad := bad ++ ["fwd: total above grant"]
    | none => bad := bad ++ ["fwd: no run"]
  | none => bad := bad ++ ["fwd: no sched"]
  -- routing intervals
  let accts := (t.w.entries.flatMap fun e => e.receipts.map (·.receiverId)) ++ t.out.outgoing.map (·.receiverId)
  if !(accts.all fun a => inIntervals p.bnds a == (t.k.L.shardOf a == own)) then bad := bad ++ ["bnds"]
  return bad

/-- For an `e.forwarded` failure that `prepD0` lets through: is a `fwd` total above the
τ = 0 grant (the AIR-side size check)? -/
def fwdAboveGrant (cb wb : Bytes) (p : Prep) : Bool :=
  match walkD0 cb, decodeW wb, p.sched.head? with
  | .ok k, .ok w, some pub =>
    let tMain := partialTrie w.main.values k.slotB2.prevStateRoot [keyBwState]
    match Scheduler.runCore pub (findD tMain keyBwState) with
    | some o => p.fwd.any fun (s, tot) => tot > grantOf o k.H.shardId s
    | none => false
  | _, _, _ => false

def main (args : List String) : IO UInt32 := do
  let mut acc := 0; let mut accOk := 0
  let mut chFail := 0; let mut chOk := 0; let mut chExact := 0; let mut chAir := 0
  let mut wFail := 0; let mut wPrepOk := 0
  let mut failures : List String := []
  for dir in args do
    let cb := (← IO.FS.readBinFile (dir ++ "/claim.bin")).toList
    let wb := (← IO.FS.readBinFile (dir ++ "/witness.bin")).toList
    let r := checkD0a cb wb
    let h := hintOf cb wb
    let p := prepD0 cb h
    match r with
    | .ok () =>
      acc := acc + 1
      match p, trace cb wb with
      | .ok p, .ok t =>
        let bad := compare p t
        if bad.isEmpty then accOk := accOk + 1
        else failures := failures ++ [s!"{dir}: accepted, mismatch {bad}"]
      | .error e, _ => failures := failures ++ [s!"{dir}: accepted but prepD0 failed: {e}"]
      | _, .error e => failures := failures ++ [s!"{dir}: trace failed: {e}"]
    | .error m =>
      let isW := !witnessHeadOk cb wb || wPrefixes.any (m.startsWith ·)
      if isW then
        wFail := wFail + 1
        if p matches .ok _ then wPrepOk := wPrepOk + 1
      else
        chFail := chFail + 1
        match p with
        | .ok p =>
          if m.startsWith "out of domain (e.forwarded)" && fwdAboveGrant cb wb p then chAir := chAir + 1
          else failures := failures ++ [s!"{dir}: C/H failure '{m}' but prepD0 succeeded"]
        | .error e =>
          if category e == category m then chOk := chOk + 1
          else failures := failures ++ [s!"{dir}: C/H failure '{m}', prepD0 '{e}'"]
          if e == m then chExact := chExact + 1
  for f in failures.take 50 do IO.eprintln f
  IO.println s!"\{\"cases\": {args.length}, \"accepted_d0a\": {acc}, \"accepted_prep_ok_and_match\": {accOk}, \"ch_failures\": {chFail}, \"ch_prep_fails_same_category\": {chOk}, \"ch_prep_same_message\": {chExact}, \"ch_forwarded_size_left_to_air_and_above_grant\": {chAir}, \"w_failures\": {wFail}, \"w_failures_prep_ok\": {wPrepOk}, \"problems\": {failures.length}}"
  return (if failures.isEmpty then 0 else 1)
