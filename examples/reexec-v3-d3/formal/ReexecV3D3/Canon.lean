import NearSpecV3.ChallengeChunkV3

/-!
# The normal form of a D3 witness file (`ReexecV3D3.canonW`)

`witness.bin` (`near-arena-witness-v3`) = `bytes "near-arena-witness-v3" ‖ bytes state_witness ‖
Vec<bytes> contract_code`. nearcore's validator (and so `RelD3`, `NearSpecV3.D3.checkD3`) leaves
these degrees of freedom in it; `canonW cb w` fixes every one of them:

| freedom | normal form |
|---|---|
| chunk header `height_included`, chunk signature, every `ChunkStateTransition.block_hash` (never read) | 0 / ED25519 + 64 zero bytes / 32 zero bytes |
| `source_receipt_proofs: HashMap` decoded leniently (any order; a duplicate key keeps the last value) | one entry per key (the last), increasing byte order of the key; each entry's bytes are the producer's |
| every `base_state` is a hash-indexed store (any order, duplicates, values never looked up) | main transition: the values **reachable** from the chunk's `prev_state_root` through the merged store `base_state ++ contract_code` (trie nodes by child hash, leaf values by value hash — exactly what `D2.revealAll` and the WASM storage reads can look up), deduplicated, in increasing order of their SHA-256; implicit transition *i*: the same from its pre-state root (the previous transition's `post_state_root`) through its own `base_state` |
| `contract_code`: appended to the main store (`pwt.rs:693-696`), so any order, duplicates, blobs never used, and blobs that also serve as trie values | every blob of the merged store that is not reachable from the root (above) and is **needed**: removing it from the code list makes `checkD3` fail (cold-cache rule: the code of an executed pre-state contract must be in the witness); deduplicated, in increasing order of SHA-256 |

Everything else is the producer's bytes (the header inner, the receipts and paths of each entry,
the applied-receipts hash, both transaction lists, the post-state roots).

**What is decided, and what is proved.** `canonW` is an ordinary computable function of
`(claim, witness)`; the verifier (`Model.lean`) accepts only witnesses `w` with `canonW cb w = w`
— unless canonicalisation would *not* be a valid witness again (`canonOk` below fails), in which
case `w` itself is its own normal form. That escape keeps completeness a theorem without a
lock-step proof through the whole D2/D3 runtime (`Obligations.lean`): soundness and completeness
are proved; that `canonOk` holds on every `RelD3` witness (so that exactly one proof per claim
and per honest witness is accepted) is **tested, not proved** (every positive of the public set
and of the oracle corpora; `docs/e2e-results/v3-d3-reference/`).

Nothing here is trusted: a wrong normaliser can only make the verifier reject an honest proof
(caught by conformance) or accept a second encoding (caught by `ADVERSARIAL_PROOFS`), never accept
a witness outside `RelD3`.
-/

namespace ReexecV3D3

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## The relation as a `Bool` -/

/-- `checkD3` as a `Bool` (`RelD3 cb w ↔ acceptsD3 cb w = true`, `acceptsD3_iff`). -/
def acceptsD3 (cb w : Bytes) : Bool :=
  match D3.checkD3 cb w with
  | .ok () => true
  | .error _ => false

theorem acceptsD3_iff (cb w : Bytes) : acceptsD3 cb w = true ↔ D3.RelD3 cb w := by
  unfold acceptsD3 D3.RelD3
  cases D3.checkD3 cb w with
  | ok u => cases u; simp
  | error e => simp

/-! ## Parsing the state witness into spans -/

/-- A decoded state witness, keeping the bytes `canonW` copies verbatim. -/
structure SW where
  eid : Bytes
  inner : Bytes
  main : Transition
  /-- `(key, raw entry bytes)` in witness order -/
  entries : List (Bytes × Bytes)
  arh : Bytes
  /-- the raw `Vec<SignedTransaction>` (count included) -/
  txs : Bytes
  implicit : List Transition
  /-- the raw `new_transactions` `Vec` (count included) -/
  newTxs : Bytes

def pEntries : Nat → P (List (Bytes × Bytes))
  | 0, bs => .ok ([], bs)
  | n + 1, bs => do
    let (e, r1) ← pEntryD2 bs
    let (es, r) ← pEntries n r1
    pure ((e.key, consumed bs r1) :: es, r)

/-- The same walk as `decodeStateWitnessD2` (the trusted decoder of `checkD2Core`), recording spans. -/
def parseSW (bs : Bytes) : Except String SW := do
  let (t, bs) ← pU8 "ChunkStateWitness tag" bs
  if t != 1 then throw "tag"
  let (eid, bs) ← pHash "epoch_id" bs
  let ((ib, _), bs) ← pChunkHeader bs
  let (main, bs) ← pTransition bs
  let (n, bs) ← pU32 "source_receipt_proofs" bs
  let (entries, bs) ← pEntries n bs
  let (arh, bs) ← pHash "applied_receipts_hash" bs
  let b0 := bs
  let (_, bs) ← pVec "transactions" pTxD2 bs
  let txs := consumed b0 bs
  let (m, bs) ← pU32 "implicit_transitions" bs
  let (impl, bs) ← pMany pTransition m bs
  let b1 := bs
  let (_, bs) ← pVec "new_transactions" pTxD2 bs
  let ntx := consumed b1 bs
  if !bs.isEmpty then throw "trailing bytes"
  pure ⟨eid, ib, main, entries, arh, txs, impl, ntx⟩

/-! ## Encoding -/

def encT (t : Transition) (vals : List Bytes) : Bytes :=
  zeros 32 ++ [0] ++ encList borshBytes vals ++ t.postStateRoot

/-- The canonical state witness: zeroed ignored fields, the given entries and values. -/
def encSW (s : SW) (mainVals : List Bytes) (entries : List Bytes) (implVals : List (List Bytes)) :
    Bytes :=
  [1] ++ s.eid ++ [2] ++ s.inner ++ zeros 8 ++ [0] ++ zeros 64 ++ encT s.main mainVals ++
    u32 entries.length ++ concatAll entries ++ s.arh ++ s.txs ++
    u32 s.implicit.length ++ concatAll ((s.implicit.zip implVals).map fun (t, v) => encT t v) ++
    s.newTxs

def wrapW (sw : Bytes) (codes : List Bytes) : Bytes :=
  borshBytes witnessTag ++ borshBytes sw ++ encList borshBytes codes

/-! ## Ordering and deduplication -/

def lt (a b : Bytes) : Bool := cmpBytes a b == 0

/-- Sort by SHA-256, one value per hash (the first of equal-hash values). -/
def sortByHash (vs : List Bytes) : List Bytes :=
  let ps := (vs.map fun v => (sha256 v, v)).mergeSort fun a b => !lt b.1 a.1
  (ps.foldr (fun (h, v) acc =>
    match acc with
    | (h', _) :: _ => if h == h' then (h, v) :: acc.tail else (h, v) :: acc
    | [] => [(h, v)]) []).map (·.2)

/-- `source_receipt_proofs` normal form: the last entry of each key, increasing key order. -/
def normEntries (es : List (Bytes × Bytes)) : List Bytes :=
  let lastFirst := es.reverse.foldl (fun (acc : HStore × List (Bytes × Bytes)) (k, e) =>
    match hGet acc.1 k with
    | some _ => acc
    | none => (acc.1.insert k [], (k, e) :: acc.2)) (.tip, [])
  (lastFirst.2.mergeSort fun a b => !lt b.1 a.1).map (·.2)

/-! ## Reachability through the recorded store (mirror of `D2.revealAll` and the trie walks) -/

/-- `(child node hashes, value hashes)` referenced by a trie node (`RawTrieNodeWithSize`). -/
def nodeRefs (node : Bytes) : List Bytes × List Bytes :=
  if node.length < 9 then ([], []) else
  let body := node.take (node.length - 8)
  match body with
  | 0 :: rest =>
    let klen := leNat (rest.take 4)
    ([], [((rest.drop (4 + klen)).drop 4).take 32])
  | 3 :: rest =>
    let klen := leNat (rest.take 4)
    ([(rest.drop (4 + klen)).take 32], [])
  | 1 :: rest =>
    ((kidHashes 16 (leNat (rest.take 2)) (rest.drop 2)).filterMap id, [])
  | 2 :: rest =>
    let r := rest.drop 36
    ((kidHashes 16 (leNat (r.take 2)) (r.drop 2)).filterMap id, [(rest.drop 4).take 32])
  | _ => ([], [])

/-- Worklist closure: every present value reachable from the work items (`(hash, isNode)`);
`seen` holds `hash ‖ [kind]`. Each present hash is expanded at most twice (as a node and as a
value) and a node pushes at most 17 references, so at most `1 + 2·17·|store|` items are ever popped:
`fuel = 40·(|store| + 1)` suffices. -/
def reachGo (s : HStore) : Nat → List (Bytes × Bool) → HStore → List Bytes → List Bytes
  | 0, _, _, acc => acc
  | _ + 1, [], _, acc => acc
  | fuel + 1, (h, isNode) :: rest, seen, acc =>
    let k := h ++ [if isNode then 1 else 0]
    match hGet seen k with
    | some _ => reachGo s fuel rest seen acc
    | none =>
      let seen := seen.insert k []
      match hGet s h with
      | none => reachGo s fuel rest seen acc
      | some v =>
        if isNode then
          let (ns, vs) := nodeRefs v
          reachGo s fuel (ns.map (·, true) ++ vs.map (·, false) ++ rest) seen (v :: acc)
        else reachGo s fuel rest seen (v :: acc)

def reach (values : List Bytes) (root : Bytes) : List Bytes :=
  reachGo (mkHStore values) (40 * (values.length + 1)) [(root, true)] .tip []

/-! ## The main transition's pre-state root (the claim walk of `checkD2Core`) -/

def mainPreRoot (cb : Bytes) : Option Bytes :=
  let r : Except String Bytes := do
    let c ← decodeClaimE cb
    let H ← decodeChunkInner c.chunkInner
    let blks ← c.blocks.mapM decodeBlk
    let ep ← match c.epochs.find? (·.epochId == c.epochId) with
      | some e => pure e
      | none => throw "epoch"
    let L ← decodeLayout ep.shardLayout
    let idx ← match L.index H.shardId with
      | some i => pure i
      | none => throw "shard"
    let isNew := fun (b : Blk) => match b.slots[idx]? with
      | some (s, _) => s.heightIncluded == b.hdr.height
      | none => false
    let b2i ← match blks.findIdx? isNew with
      | some i => pure i
      | none => throw "no new chunk"
    let B2 ← match blks[b2i]? with
      | some b => pure b
      | none => throw "walk"
    let slotB2 ← match B2.slots[idx]? with
      | some p => pure p.2
      | none => throw "slot"
    pure slotB2.prevStateRoot
  match r with
  | .ok x => some x
  | .error _ => none

/-! ## The normaliser -/

def memHash (hs : HStore) (v : Bytes) : Bool := (hGet hs (sha256 v)).isSome

def hashSet (vs : List Bytes) : HStore := vs.foldl (fun m v => m.insert (sha256 v) []) .tip

/-- The code blobs of `U` (sorted, distinct) without which `checkD3` fails, given the canonical
state witness `sw`: one `checkD3` run per blob. -/
def neededCodes (cb sw : Bytes) (U : List Bytes) : List Bytes :=
  U.filter fun b => !acceptsD3 cb (wrapW sw (U.filter (· != b)))

/-- The normal form of `w` as a witness for the claim bytes `cb` (module doc). A file that does not
parse is returned unchanged. -/
def canonW (cb w : Bytes) : Bytes :=
  match decodeWitnessFile w with
  | .error _ => w
  | .ok (swb, codes) =>
    match parseSW swb with
    | .error _ => w
    | .ok s =>
      let merged := s.main.values ++ codes
      let mainVals := match mainPreRoot cb with
        | some root => sortByHash (reach merged root)
        | none => sortByHash s.main.values
      let reached := hashSet mainVals
      let U := sortByHash (merged.filter fun v => !memHash reached v)
      let (_, implVals) := s.implicit.foldl (fun (acc : Bytes × List (List Bytes)) t =>
        (t.postStateRoot, acc.2 ++ [sortByHash (reach t.values acc.1)]))
        (s.main.postStateRoot, [])
      let sw := encSW s mainVals (normEntries s.entries) implVals
      wrapW sw (neededCodes cb sw U)

/-- The canonical form `w1 = canonW cb w` is usable: a valid witness again, a fixed point, and no
longer than `w`. -/
def canonOkOf (cb w w1 : Bytes) : Bool :=
  acceptsD3 cb w1 && canonW cb w1 == w1 && decide (w1.length ≤ w.length)

/-- **Normal form.** `w` is its own canonical form, or (escape, never observed) its canonical form
is not usable. `canonW cb w` is computed once. -/
def normalW (cb w : Bytes) : Bool :=
  let w1 := canonW cb w
  w1 == w || !canonOkOf cb w w1

/-- **The honest proof** (what `prove` emits, and the witness of `Obligations.relD3_normal`): the
canonical form when it is usable, else the witness itself (the escape of `normalW`). -/
def proveW (cb w : Bytes) : Bytes :=
  let w1 := canonW cb w
  if canonOkOf cb w w1 then w1 else w

end ReexecV3D3
