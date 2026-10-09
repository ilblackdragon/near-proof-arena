import NearSpecV3.ChallengeChunkV3
import ReexecV3D3.CanonDefs
import ReexecV3D3.NormDefs

/-!
# The normal form of a D3 witness file (executable; part of the verifier model)

`witness.bin` (`near-arena-witness-v3`) = `bytes "near-arena-witness-v3" ‖ bytes state_witness ‖
Vec<bytes> contract_code`. nearcore's validator (and so `RelD3`, `NearSpecV3.D3.checkD3`) leaves
these degrees of freedom in it; the normal form fixes every one of them:

| freedom | normal form |
|---|---|
| chunk header `height_included`, chunk signature, every `ChunkStateTransition.block_hash` (never read) | 0 / ED25519 + 64 zero bytes / 32 zero bytes |
| `source_receipt_proofs: HashMap` decoded leniently (any order; a duplicate key keeps the last value) | one entry per key (the last), increasing byte order of the key; entry bytes are the producer's |
| the main recorded store `base_state ++ contract_code` (`pwt.rs:693-696`, `checkD2Core`'s `merged`: any order, duplicates, values never read, values in either list) | the **necessary** values: the store's answers (one value per SHA-256, `mkHStore`'s last-wins) such that removing any one of them makes `checkD3` fail, in increasing byte order; those that `D2.revealAll` looks up from the chunk's pre-state root (`qAll`) form `base_state`, the others `contract_code` (both in byte order) |
| implicit transition *i*'s `base_state` (its own store) | the same: its necessary values, in byte order |

Everything else is the producer's bytes (the header inner, the receipts and paths of each entry,
the applied-receipts hash, both transaction lists, the post-state roots).

**The read set, as necessity.** The relation reads the recorded storage through the trie it reveals
up front (`D2.revealAll`: every reachable node) and through `Env.codeOf` (code blobs, the WASM
`External`'s trie walks); the D2/WASM runtime then reads the revealed trie, which is not a store
lookup. So "the values the relation reads" is characterised extensionally: a value is kept iff the
relation rejects the witness without it (an unread value can always be dropped; a read value that is
missing is `MissingTrieValue`). `pools` lists the candidate values, `pass` drops every value whose
removal keeps `checkD3` accepting (one run per value, in a fixed order), `iterP` repeats until
nothing is dropped. The verifier (`normalW`) accepts a witness only if it is byte-identical to the
encoding of its own pools (`encP`) **and** every one of its values is necessary (`allNeeded`: one
`checkD3` run per value, in parallel). No fallback: a witness for which that fails is rejected
(`Obligations.lean` proves that every `RelD3` witness has a normal form, `NormalForm.lean`).

Definitions only; the judge compiles this module.
-/

namespace ReexecV3D3

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## The relation as a `Bool` -/

/-- `checkD3` as a `Bool` (`RelD3 cb w ↔ acceptsD3 cb w = true`, `acceptsD3_iff`). -/
def acceptsD3 (cb w : Bytes) : Bool :=
  match D3.checkD3 cb w with
  | .ok () => true
  | .error _ => false

/-! ## Re-encoding a state witness with given values -/

/-- Borsh encoding of a `ChunkStateTransition` with `PartialState::TrieValues`. -/
def encTr (t : Transition) : Bytes :=
  t.blockHash ++ (u8 0 ++ (encList borshBytes t.values ++ t.postStateRoot))

/-- `n` items of `p`, each with the exact bytes it was parsed from. -/
def segs {α : Type} (p : P α) : Nat → Bytes → Except String (List (α × Bytes) × Bytes)
  | 0, bs => .ok ([], bs)
  | n + 1, bs => do
    let (a, r) ← p bs
    let (as, r') ← segs p n r
    pure ((a, consumed bs r) :: as, r')

/-- Receipt-proof entries (with their bytes) in normal form: one per key (the last),
increasing key order. -/
def normPairs (ps : List (EntryD2 × Bytes)) : List (EntryD2 × Bytes) :=
  isort (fun a b => bytesLe a.1.key b.1.key) (dedupLastBy (·.1.key) ps)

/-- A transition with zero block hash and the values `vs`. -/
def trV (vs : List Bytes) (t : Transition) : Transition :=
  { blockHash := zeroHash, values := vs, postStateRoot := t.postStateRoot }

/-- The implicit transitions with zero block hashes and the values `iv` (`[]` past its end). -/
def implV : List (List Bytes) → List Transition → List Transition
  | _, [] => []
  | iv, t :: ts => trV (iv.headD []) t :: implV iv.tail ts

/-- The state-witness bytes `sw` with the ignored fields zero, the receipt-proof entries in normal
form (as byte segments of `sw`), the main transition's values `mv` and the implicit transitions'
values `iv`; every other field is `sw`'s bytes. -/
def normSWV (mv : List Bytes) (iv : List (List Bytes)) (sw : Bytes) : Except String Bytes := do
  let (_, b1) ← pU8 "ChunkStateWitness tag" sw
  let (_, b2) ← pHash "epoch_id" b1
  let (_, b3) ← pU8 "ShardChunkHeader tag" b2
  let (_, b4) ← pChunkInner b3
  let (_, b5) ← pU64 "height_included" b4
  let (_, b6) ← pSignature "chunk signature" b5
  let (main, b7) ← pTransition b6
  let (n, b8) ← pU32 ("source_receipt_proofs" ++ " length") b7
  let (ps, b9) ← segs pEntryD2 n b8
  let (_, b10) ← pHash "applied_receipts_hash" b9
  let (_, b11) ← pVec "transactions" pTxD2 b10
  let (impl, b12) ← pVec "implicit_transitions" pTransition b11
  let es := normPairs ps
  pure (consumed sw b4 ++ (zeros8 ++ (sig0 ++ (encTr (trV mv main) ++
    (u32 es.length ++ (concatAll (es.map (·.2)) ++ (consumed b9 b11 ++
    (encList encTr (implV iv impl) ++ b12))))))))

/-- `witness.bin` of a state witness and contract code blobs. -/
def wrapWC (sw : Bytes) (codes : List Bytes) : Bytes :=
  borshBytes witnessTag ++ (borshBytes sw ++ encList borshBytes codes)

/-! ## Value pools -/

/-- Main pool and one pool per implicit transition. -/
abbrev Pools := List Bytes × List (List Bytes)

/-- The values a store built from `vals` answers (one per hash, `mkHStore`'s last wins), in byte
order. -/
def poolOf (vals : List Bytes) : List Bytes := normValsH vals (vals.map sha256)

/-- The pools of a decoded witness: the main store `base_state ++ contract_code` and each implicit
transition's `base_state`. -/
def initPools (s : StateWitnessD2) (codes : List Bytes) : Pools :=
  (poolOf (s.main.values ++ codes), s.implicit.map fun t => poolOf t.values)

/-- The main transition's pre-state root, from the claim alone (the walk of `checkD2Core`). -/
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

/-- Placement of the main pool: the values `revealAll` looks up from the root `R` go to
`base_state`, the others to `contract_code` (both keep the pool's byte order). -/
def layout (R : Bytes) (P : List Bytes) : List Bytes × List Bytes :=
  let q := qAll (mkHStore P) revealFuel R
  (P.filter fun v => q.contains (sha256 v), P.filter fun v => !q.contains (sha256 v))

/-- The witness file of the pools `X` over the state witness `sw`. If the placement would make the
state witness larger than the 8 MiB `w.size` bound, every main value goes to `contract_code`. -/
def encP (cb sw : Bytes) (X : Pools) : Bytes :=
  let bc := layout ((mainPreRoot cb).getD []) X.1
  match normSWV bc.1 X.2 sw with
  | .ok sw1 =>
    if lenT sw1 ≤ 8388608 then wrapWC sw1 bc.2 else
    match normSWV [] X.2 sw with
    | .ok sw2 => wrapWC sw2 X.1
    | .error _ => []
  | .error _ => []

/-! ## Dropping unnecessary values -/

/-- A removal candidate: `(none, v)` = main pool value `v`, `(some i, v)` = value `v` of implicit
transition `i`. -/
abbrev Item := Option Nat × Bytes

def modAt {α : Type} (f : α → α) : Nat → List α → List α
  | _, [] => []
  | 0, x :: xs => f x :: xs
  | i + 1, x :: xs => x :: modAt f i xs

def items (X : Pools) : List Item :=
  X.1.map (fun v => (none, v)) ++
    (List.range X.2.length).flatMap fun i => (X.2.getD i []).map fun v => (some i, v)

def removeItem (X : Pools) : Item → Pools
  | (none, v) => (X.1.erase v, X.2)
  | (some i, v) => (X.1, modAt (·.erase v) i X.2)

def poolSize (X : Pools) : Nat := X.1.length + (X.2.map List.length).sum

/-- One removal attempt: keep the removal iff `checkD3` still accepts. -/
def stepP (cb sw : Bytes) (X : Pools) (it : Item) : Pools :=
  let Y := removeItem X it
  if acceptsD3 cb (encP cb sw Y) then Y else X

/-- One pass over the candidates of `X`, in order. -/
def pass (cb sw : Bytes) (X : Pools) : Pools := (items X).foldl (stepP cb sw) X

/-- Every value of `X` is necessary (one `checkD3` run per value, in parallel tasks). -/
def allNeeded (cb sw : Bytes) (X : Pools) : Bool :=
  ((items X).map fun it => Task.spawn fun _ => acceptsD3 cb (encP cb sw (removeItem X it))).all
    fun t => !t.get

/-- `pass`, with the common case (nothing to drop) decided in parallel. -/
def passPar (cb sw : Bytes) (X : Pools) : Pools :=
  if allNeeded cb sw X then X else pass cb sw X

/-- Passes until nothing is dropped (`poolSize X + 1` passes suffice). -/
def iterP (cb sw : Bytes) : Nat → Pools → Pools
  | 0, X => X
  | f + 1, X =>
    let Y := passPar cb sw X
    if decide (Y = X) then X else iterP cb sw f Y

/-! ## The normaliser and the normal-form test -/

/-- **The normal form** of `w` for the claim bytes `cb` (what `prove` emits). A file that does not
decode is returned unchanged (it is not a `RelD3` witness). -/
def canonW (cb w : Bytes) : Bytes :=
  match decodeWitnessFile w with
  | .error _ => w
  | .ok (sw, codes) =>
    match decodeStateWitnessD2 sw with
    | .error _ => w
    | .ok s =>
      let X0 := initPools s codes
      encP cb sw (iterP cb sw (poolSize X0 + 1) X0)

/-- **`w` is in normal form**: it is the encoding of its own pools, and every value of them is
necessary. Equivalent to `canonW cb w = w` (`NormalForm.lean`), without iterating. -/
def normalW (cb w : Bytes) : Bool :=
  match decodeWitnessFile w with
  | .error _ => false
  | .ok (sw, codes) =>
    match decodeStateWitnessD2 sw with
    | .error _ => false
    | .ok s =>
      let X := initPools s codes
      encP cb sw X == w && allNeeded cb sw X

end ReexecV3D3
