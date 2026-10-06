import ReexecV3D0.NormalDefs

/-!
# The normaliser on bytes (executable; part of the verifier model)

`normSW K R sw` rewrites the state-witness bytes `sw` into the normal form of
`NormalDefs.normW K R`: the bytes before `height_included` are kept, `height_included`
and the chunk signature become zero, every transition is re-encoded (`encTr`: zero block
hash, normal `base_state` values), the receipt-proof entries are deduplicated (last
wins) and sorted by key **as byte segments of the input** (so the receipt encodings are
the input's own), and the remaining fields are kept. The verifier accepts a proof only
when its state witness is a fixed point of `normSW` (`normalW`), and the prover runs this
very function. Definitions only; the judge compiles this module.
-/

namespace ReexecV3D0

open NearSpec NearSpecV3

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
def normPairs (ps : List (ProofEntry × Bytes)) : List (ProofEntry × Bytes) :=
  isort (fun a b => bytesLe a.1.key b.1.key) (dedupLastBy (·.1.key) ps)

/-- The normal-form bytes of a state witness, for main-trie keys `K` at root `R`. -/
def normSW (K : List (List Nat)) (R : Bytes) (sw : Bytes) : Except String Bytes := do
  let (_, b1) ← pU8 "ChunkStateWitness tag" sw
  let (_, b2) ← pHash "epoch_id" b1
  let (_, b3) ← pU8 "ShardChunkHeader tag" b2
  let (_, b4) ← pChunkInner b3
  let (_, b5) ← pU64 "height_included" b4
  let (_, b6) ← pSignature "chunk signature" b5
  let (main, b7) ← pTransition b6
  let (n, b8) ← pU32 ("source_receipt_proofs" ++ " length") b7
  let (ps, b9) ← segs pEntry n b8
  let (_, b10) ← pHash "applied_receipts_hash" b9
  let (_, b11) ← pU32 "transactions" b10
  let (impl, b12) ← pVec "implicit_transitions" pTransition b11
  let es := normPairs ps
  pure (consumed sw b4 ++ (zeros8 ++ (sig0 ++ (encTr (normMain K R main) ++
    (u32 es.length ++ (concatAll (es.map (·.2)) ++ (consumed b9 b11 ++
    (encList encTr (normImpl main.postStateRoot impl) ++ b12))))))))

/-- Normal witness file: `near-arena-witness-v3`, no contract code, and the state
witness is a fixed point of `normSW` for the keys and root `keysD0` computes. -/
def normalW (cb w : Bytes) : Bool :=
  match decodeWitnessFile w with
  | .ok (sw, []) =>
    match keysD0 cb w with
    | .ok (K, R) =>
      match normSW K R sw with
      | .ok c => c == sw
      | .error _ => false
    | .error _ => false
  | _ => false

end ReexecV3D0
