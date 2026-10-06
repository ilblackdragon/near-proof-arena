import NearSpecV3
import NearSpecV3.PrepD0

/-!
`nearspec-v3-test-prep CASE_DIR...` — executable test of `prepD0` / `hintOf`
(V3-D0-DESIGN §1, §2.1, §6.1) against the relation `checkD0` on real cases.

Per case (`claim.bin`, `witness.bin`): `r := checkD0 cb wb`, `h := hintOf cb wb`,
`p := prepD0 cb h`.

* `r = ok` (RelD0): `p` must be `ok`, and every prepared value must equal the value the
  relation's own execution computes (re-run here independently of `prepD0`: the applied
  receipts rebuilt from `p.lists` against the witness entries and hashed to
  `applied_receipts_hash`; each list's `from_shard` and Merkle path; `n`; the `0x0f` states
  read back from the post tries of `applyNewChunk` / `applyMissingChunk`; the fixed-key walk
  values from the pre tries; post/outcome/burnt/gas values; routing intervals vs
  `Layout.shardOf` on every receipt of every entry and every refund).
* `r = error m` with `m` raised by a claim/hint (C/H) check: `p` must fail with the same
  category (`out of domain` / `invalid`); exact message equality is counted.
* `r = error m` with `m` a witness (W) check: no requirement (the witness part is the
  STARK's); counted.
-/

open NearSpec NearSpec.TransferV1 NearSpecV3

def wPrefixes : List String :=
  ["out of domain (w.", "out of domain (r.", "out of domain (e.distinct_ids)",
   "invalid: witness chunk header", "invalid: epoch id", "invalid: missing source receipt proof",
   "invalid: receipt proof", "invalid: source_receipt_proofs", "invalid: applied receipts hash",
   "invalid: MissingTrieValue", "invalid: main base_state", "invalid: main transition post",
   "invalid: implicit transition", "invalid: InvalidStateRoot", "invalid: InvalidOutcomesProof",
   "invalid: InvalidBalanceBurnt", "invalid: account path not revealed"]

def category (m : String) : String := if m.startsWith "out of domain" then "ood" else "invalid"

/-- Does the witness part that `checkD0` decodes before any claim structure pass? -/
def witnessHeadOk (cb wb : Bytes) : Bool :=
  match decodeClaimE cb, decodeWitnessFile wb with
  | .ok c, .ok (sw, codes) =>
    codes.isEmpty && lenT sw ≤ 8388608 &&
    (match decodeStateWitness sw with
     | .ok w => w.innerBytes == c.chunkInner && w.epochId == c.epochId
     | .error _ => false)
  | _, _ => false

structure Tr where
  w : StateWitness
  L : Layout
  own : Nat
  receipts : List Receipt
  tMain : PTrie
  out : MainOut
  ctxB2 : ApplyCtx
  impl : List (PTrie × PTrie)     -- (pre, post) per implicit transition
  H : ChunkInner

/-- The relation's execution on an accepted case (same functions, same order as `checkD0`). -/
def trace (cb wb : Bytes) : Except String Tr := do
  let c ← decodeClaimE cb
  let (swBytes, _) ← decodeWitnessFile wb
  let w ← decodeStateWitness swBytes
  let H ← decodeChunkInner c.chunkInner
  let L ← decodeLayout (c.epochs.headD ⟨[], 0, 0, [], []⟩).shardLayout
  let blks ← c.blocks.mapM decodeBlk
  let idx ← match L.index H.shardId with | some i => pure i | none => throw "layout"
  let isNew := fun (b : Blk) => match b.slots[idx]? with
    | some (s, _) => s.heightIncluded == b.hdr.height
    | none => false
  let b2i ← match blks.findIdx? isNew with | some i => pure i | none => throw "walk"
  let B2 ← match blks[b2i]? with | some b => pure b | none => throw "walk"
  let stop ← match (blks.drop (b2i + 1)).findIdx? isNew with
    | some j => pure (b2i + 1 + j) | none => throw "walk"
  let implicitBlks := (blks.take b2i).reverse
  let sourceBlks := (blks.drop b2i).take (stop - b2i)
  let prevB2 ← match blks[b2i + 1]? with | some b => pure b | none => throw "walk"
  let slotB2 ← match B2.slots[idx]? with | some p => pure p.2 | none => throw "slot"
  let mut receipts : List Receipt := []
  for S in sourceBlks do
    let mut proofs : List ProofEntry := []
    for (s, ci) in S.slots do
      if s.heightIncluded == S.hdr.height then
        match lookupLast (chunkHash s.inner ci.encodedMerkleRoot) w.entries with
        | some e => proofs := proofs ++ [e]
        | none => throw "proof"
    let shuffled ← match shuffleWithSeed proofs S.hdr.prevHash with
      | some p => pure p | none => throw "shuffle"
    receipts := receipts ++
      (shuffled.map fun e => e.receipts.filter fun r => L.shardOf r.receiverId == H.shardId).flatten
  let ctxB2 := blockCtx L H.shardId slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let t0 := partialTrie w.main.values slotB2.prevStateRoot [keyBufferedIdx]
  let bshards ← match t0.find keyBufferedIdx with
    | some v => bufferedShards v | none => throw "missing"
  let tMain := partialTrie w.main.values slotB2.prevStateRoot (mainKeys receipts bshards)
  let out ← applyNewChunk prims ctxB2 tMain receipts
  let mut root := out.trie.hashOf
  let mut impl : List (PTrie × PTrie) := []
  for (M, T) in implicitBlks.zip w.implicit do
    let ctxM := blockCtx L H.shardId slotB2.gasLimit M M.hdr.nextGasPrice
    let tM := partialTrie T.values root [keyDelayedIdx, keyBwState]
    let tM' ← applyMissingChunk prims ctxM tM
    impl := impl ++ [(tM, tM')]
    root := tM'.hashOf
  pure ⟨w, L, H.shardId, receipts, tMain, out, ctxB2, impl, H⟩

/-- Compare every prepared value with the traced execution; returns the list of mismatches. -/
def compare (p : Prep) (t : Tr) : List String := Id.run do
  let mut bad : List String := []
  let entries := p.lists.map fun s => lookupLast s.key t.w.entries
  if entries.any Option.isNone then bad := bad ++ ["lists: key without witness entry"]
  let es := entries.filterMap id
  let rebuilt := (es.map fun e => e.receipts.filter fun r => t.L.shardOf r.receiverId == t.own).flatten
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
  -- states: the 0x0f value in each post trie
  let posts := t.out.trie :: t.impl.map (·.2)
  if p.states.length != posts.length ||
     !((p.states.zip posts).all fun (s, tr) => tr.find keyBwState == some (some s)) then
    bad := bad ++ ["states"]
  -- walks: values in the pre tries
  let pres := t.tMain :: t.impl.map (·.1)
  if !(p.walks.all fun wk => match pres[wk.tau]? with
      | some tr => tr.find wk.key == some wk.value
      | none => false) then bad := bad ++ ["walks"]
  -- routing intervals
  let accts := (t.w.entries.flatMap fun e => e.receipts.map (·.receiverId)) ++ t.out.outgoing.map (·.receiverId)
  if !(accts.all fun a => inIntervals p.bnds a == (t.L.shardOf a == t.own)) then bad := bad ++ ["bnds"]
  return bad

def esc (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

def main (args : List String) : IO UInt32 := do
  let mut acc := 0; let mut accOk := 0
  let mut chFail := 0; let mut chOk := 0; let mut chExact := 0
  let mut wFail := 0; let mut wPrepOk := 0
  let mut bnChecked := 0
  let mut failures : List String := []
  for dir in args do
    let cb := (← IO.FS.readBinFile (dir ++ "/claim.bin")).toList
    let wb := (← IO.FS.readBinFile (dir ++ "/witness.bin")).toList
    let r := checkD0 cb wb
    let h := hintOf cb wb
    let p := prepD0 cb h
    match r with
    | .ok () =>
      acc := acc + 1
      match p, trace cb wb with
      | .ok p, .ok t =>
        let bad := compare p t
        bnChecked := bnChecked + 1
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
        | .ok _ => failures := failures ++ [s!"{dir}: C/H failure '{m}' but prepD0 succeeded"]
        | .error e =>
          if category e == category m then chOk := chOk + 1
          else failures := failures ++ [s!"{dir}: C/H failure '{m}', prepD0 '{e}'"]
          if e == m then chExact := chExact + 1
  for f in failures.take 50 do IO.eprintln f
  IO.println s!"\{\"cases\": {args.length}, \"accepted\": {acc}, \"accepted_prep_ok_and_match\": {accOk}, \"ch_failures\": {chFail}, \"ch_prep_fails_same_category\": {chOk}, \"ch_prep_same_message\": {chExact}, \"w_failures\": {wFail}, \"w_failures_prep_ok\": {wPrepOk}, \"problems\": {failures.length}}"
  return (if failures.isEmpty then 0 else 1)
