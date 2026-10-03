import NearSpec.TransferV1
import Std.Data.HashMap

/-!
# Decoders and the executable reference checker (NOT part of the trusted relation)

Strict decoders for `request.bin`, `witness.bin`, `claim.bin` (`spec/claim-v1.md`),
the partial-trie builder (from nearcore's `PartialState` node list), and
`deriveClaim`, used by the `nearspec-check` executable for differential testing
against nearcore. Soundness of the challenge never depends on this file: the
relation (`TransferV1.NearRelation`) is stated with encoders only, and the
checker re-validates every result with `decide (NearRelation c w)`.
-/

namespace NearSpec.Codec

open NearSpec NearSpec.TransferV1

/-- `"near-arena-request-v1"` -/
def requestFormat : Bytes :=
  [110, 101, 97, 114, 45, 97, 114, 101, 110, 97, 45, 114, 101, 113, 117, 101, 115, 116, 45, 118, 49]
/-- `"near-arena-witness-v1"` -/
def witnessFormat : Bytes :=
  [110, 101, 97, 114, 45, 97, 114, 101, 110, 97, 45, 119, 105, 116, 110, 101, 115, 115, 45, 118, 49]

structure Request where
  protocolVersion : Nat
  chainId : Bytes
  shardId : Nat
  blockHeight : Nat
  blockGasPrice : Nat
  gasLimit : Nat
  preStateRoot : Bytes
  receipts : List Receipt

/-- Parser combinators in `Except String` for error reporting. -/
abbrev P (α : Type) := Bytes → Except String (α × Bytes)

def lift {α} (what : String) (p : Parser α) : P α := fun bs =>
  match p bs with
  | some r => .ok r
  | none => .error s!"truncated/invalid {what}"

def chainIdOk (b : Bytes) : Bool :=
  1 ≤ b.length && b.length ≤ 64 && b.all (fun x => 33 ≤ x.toNat && x.toNat ≤ 126)

def pTag (want : Bytes) (what : String) : P Unit := fun bs => do
  let (got, rest) ← lift what readBorshBytes bs
  if got == want then pure ((), rest) else throw s!"unknown {what}"

/-- Strict decoder of one nearcore-borsh `Receipt` of the slice shape. Any other
shape (other ReceiptEnum variant, data dependencies, >1 action, non-Transfer
action, ML-DSA key) is rejected as out of the slice. -/
def pReceipt : P Receipt := fun bs => do
  let (pred, bs) ← lift "predecessor_id" readBorshBytes bs
  let (recv, bs) ← lift "receiver_id" readBorshBytes bs
  let (rid, bs) ← lift "receipt_id" readHash bs
  let (tag, bs) ← lift "ReceiptEnum tag" readU8 bs
  if tag != 0 then throw "out of slice: ReceiptEnum is not Action(0)"
  let (signer, bs) ← lift "signer_id" readBorshBytes bs
  let (kt, bs) ← lift "key type" readU8 bs
  let klen ← match kt with
    | 0 => pure 32
    | 1 => pure 64
    | _ => throw "out of slice: signer key type not ED25519/SECP256K1"
  let (kdata, bs) ← lift "public key" (takeN klen) bs
  let (gp, bs) ← lift "gas_price" readU128 bs
  let (nout, bs) ← lift "output_data_receivers" readU32 bs
  if nout != 0 then throw "out of slice: output_data_receivers not empty"
  let (nin, bs) ← lift "input_data_ids" readU32 bs
  if nin != 0 then throw "out of slice: input_data_ids not empty"
  let (nact, bs) ← lift "actions" readU32 bs
  if nact != 1 then throw s!"out of slice: {nact} actions"
  let (atag, bs) ← lift "action tag" readU8 bs
  if atag != 3 then throw "out of slice: action is not Transfer(3)"
  let (dep, bs) ← lift "deposit" readU128 bs
  pure ({ predecessorId := pred, receiverId := recv, receiptId := rid, signerId := signer,
          signerPk := ⟨kt, kdata⟩, gasPrice := gp, deposit := dep }, bs)

def pMany {α} (p : P α) : Nat → P (List α)
  | 0, bs => pure ([], bs)
  | n + 1, bs => do
    let (a, bs) ← p bs
    let (as, bs) ← pMany p n bs
    pure (a :: as, bs)

def decodeRequest (bs : Bytes) : Except String Request := do
  let ((), bs) ← pTag requestFormat "request format" bs
  let ((), bs) ← pTag statementId "statement id" bs
  let (pv, bs) ← lift "protocol_version" readU32 bs
  let (chain, bs) ← lift "chain_id" readBorshBytes bs
  if !chainIdOk chain then throw "bad chain_id"
  let (shard, bs) ← lift "shard_id" readU64 bs
  let (h, bs) ← lift "block_height" readU64 bs
  let (gp, bs) ← lift "block_gas_price" readU128 bs
  let (gl, bs) ← lift "gas_limit" readU64 bs
  let (root, bs) ← lift "pre_state_root" readHash bs
  let (n, bs) ← lift "receipt count" readU32 bs
  let (rs, bs) ← pMany pReceipt n bs
  if !bs.isEmpty then throw "trailing bytes"
  pure ⟨pv, chain, shard, h, gp, gl, root, rs⟩

def decodeClaim (bs : Bytes) : Except String Claim := do
  let ((), bs) ← pTag claimFormat "claim format" bs
  let ((), bs) ← pTag statementId "statement id" bs
  let (pv, bs) ← lift "protocol_version" readU32 bs
  let (chain, bs) ← lift "chain_id" readBorshBytes bs
  if !chainIdOk chain then throw "bad chain_id"
  let (shard, bs) ← lift "shard_id" readU64 bs
  let (h, bs) ← lift "block_height" readU64 bs
  let (gp, bs) ← lift "block_gas_price" readU128 bs
  let (gl, bs) ← lift "gas_limit" readU64 bs
  let (pre, bs) ← lift "pre_state_root" readHash bs
  let (n, bs) ← lift "receipt_count" readU32 bs
  let (rc, bs) ← lift "receipts_commitment" readHash bs
  let (post, bs) ← lift "slice_post_root" readHash bs
  let (orr, bs) ← lift "outcome_root" readHash bs
  let (nr, bs) ← lift "refund_count" readU32 bs
  let (rfc, bs) ← lift "refunds_commitment" readHash bs
  let (gas, bs) ← lift "gas_burnt_total" readU64 bs
  let (tok, bs) ← lift "tokens_burnt_total" readU128 bs
  if !bs.isEmpty then throw "trailing bytes"
  pure ⟨pv, chain, shard, h, gp, gl, pre, n, rc, post, orr, nr, rfc, gas, tok⟩

/-- Strict lexicographic `<` on byte strings (nearcore sorts `PartialState` values). -/
def lexLt : Bytes → Bytes → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLt as bs)

def sortedStrict : List Bytes → Bool
  | a :: b :: rest => lexLt a b && sortedStrict (b :: rest)
  | _ => true

/-- witness.bin → (pre_state_root, PartialState values). -/
def decodeWitness (bs : Bytes) : Except String (Bytes × List Bytes) := do
  let ((), bs) ← pTag witnessFormat "witness format" bs
  let (root, bs) ← lift "pre_state_root" readHash bs
  let (tag, bs) ← lift "PartialState tag" readU8 bs
  if tag != 0 then throw "PartialState tag != TrieValues(0)"
  let (n, bs) ← lift "value count" readU32 bs
  let (vs, bs) ← pMany (lift "value" readBorshBytes) n bs
  if !bs.isEmpty then throw "trailing bytes"
  if !sortedStrict vs then throw "witness values not strictly ascending"
  pure (root, vs)

/-! ## Partial-trie builder (completeness helper; any mistake here can only make
the checker reject, since the relation re-hashes the built trie). -/

def hpDecode : Bytes → List Nat
  | [] => []
  | f :: rest =>
    let odd := (f.toNat / 16) % 2 == 1
    (if odd then [f.toNat % 16] else []) ++ nibbles rest

def kidHashes : Nat → Nat → Bytes → List (Option Bytes)
  | 0, _, _ => []
  | k + 1, bm, bs =>
    if bm % 2 == 1 then some (bs.take 32) :: kidHashes k (bm / 2) (bs.drop 32)
    else none :: kidHashes k (bm / 2) bs

abbrev Store := Std.HashMap (List UInt8) Bytes

instance : Inhabited PTrie := ⟨.hash []⟩
instance : Inhabited Kids := ⟨.nil⟩

partial def build (store : Store) (h : Bytes) (keys : List (List Nat)) : PTrie :=
  if keys.isEmpty then .hash h else
  match store.get? h with
  | none => .hash h
  | some node =>
    let val (len : Nat) (vh : Bytes) (want : Bool) : Slot :=
      match (if want then store.get? vh else none) with
      | some v => if v.length == len then .val v else .ref len vh
      | none => .ref len vh
    let mem := leNat ((node.drop (node.length - 8)))
    let body := node.take (node.length - 8)
    match body with
    | 0 :: rest =>
      let klen := leNat (rest.take 4)
      let k := hpDecode ((rest.drop 4).take klen)
      let r2 := rest.drop (4 + klen)
      .leaf k (val (leNat (r2.take 4)) ((r2.drop 4).take 32) (keys.any (· == k))) mem
    | 3 :: rest =>
      let klen := leNat (rest.take 4)
      let k := hpDecode ((rest.drop 4).take klen)
      let child := (rest.drop (4 + klen)).take 32
      let keys' := (keys.filter (isPrefix k)).map (·.drop k.length)
      .ext k (build store child keys') mem
    | t :: rest =>
      let (vslot, rest) : Option Slot × Bytes :=
        if t == 2 then (some (val (leNat (rest.take 4)) ((rest.drop 4).take 32) (keys.any (· == []))), rest.drop 36)
        else (none, rest)
      let bm := leNat (rest.take 2)
      let hs := kidHashes 16 bm (rest.drop 2)
      let rec mk : Nat → List (Option Bytes) → Kids
        | _, [] => .nil
        | i, none :: more => .none (mk (i + 1) more)
        | i, some ch :: more =>
          let ks := (keys.filter (fun k => k.head? == some i)).map (·.drop 1)
          .some (build store ch ks) (mk (i + 1) more)
      .branch vslot (mk 0 hs) mem
    | [] => .hash h

def buildWitness (req : Request) (values : List Bytes) : Witness :=
  let store : Store := values.foldl (fun m v => m.insert (sha256 v) v) {}
  let keys := req.receipts.map (fun r => accountKeyPath r.receiverId)
  ⟨req.receipts, build store req.preStateRoot keys⟩

/-! ## Reference claim derivation -/

def firstFailing (ctx : Ctx) : Nat → Acc → List Receipt → Option Nat
  | _, _, [] => none
  | i, st, r :: rs =>
    match applyReceipt ctx st r with
    | none => some i
    | some st' => firstFailing ctx (i + 1) st' rs

/-- Derive the expected claim from a request and witness, or explain why the
request is out of the slice domain / the witness is insufficient. -/
def deriveClaim (req : Request) (w : Witness) : Except String Claim := do
  let ctx : Ctx := ⟨req.blockHeight, req.blockGasPrice⟩
  let hdr : Claim :=
    { protocolVersion := req.protocolVersion, chainId := req.chainId, shardId := req.shardId,
      blockHeight := req.blockHeight, blockGasPrice := req.blockGasPrice, gasLimit := req.gasLimit,
      preStateRoot := req.preStateRoot, receiptCount := req.receipts.length,
      receiptsCommitment := receiptsCommitment req.shardId req.receipts,
      slicePostRoot := zeroHash, outcomeRoot := zeroHash, refundCount := 0,
      refundsCommitment := zeroHash, gasBurntTotal := 0, tokensBurntTotal := 0 }
  if hdr.protocolVersion != Params.protocolVersion then throw "out of domain: protocol_version"
  if hdr.chainId != Params.chainId then throw "out of domain: chain_id"
  let n := req.receipts.length
  if n < 1 || n > Params.maxBatch then throw "out of domain: batch size"
  if !((n - 1) * Params.G < req.gasLimit) then throw "out of domain: gas limit"
  if !(req.receipts.all Receipt.inSlice) then throw "out of domain: receipt fields (ids/key/named receiver/system)"
  if !(decide (req.receipts.map Receipt.receiptId).Nodup) then throw "out of domain: duplicate receipt id"
  if w.trie.hashOf != req.preStateRoot then throw "witness does not hash to pre_state_root"
  if !w.trie.wf then throw "witness trie not well-formed"
  if w.trie.revealedBytes > Params.maxWitnessBytes then throw "out of domain: witness too large"
  match runBatch ctx w.trie w.receipts with
  | none =>
    let i := (firstFailing ctx 0 ⟨w.trie, [], [], 0, 0⟩ w.receipts).getD 0
    throw s!"out of domain: receipt {i} (missing/unrevealed receiver, not AccountV1, overflow, or storage stake)"
  | some acc =>
    let o := Outputs.ofAcc acc
    pure { hdr with slicePostRoot := o.slicePostRoot, outcomeRoot := o.outcomeRoot,
                    refundCount := o.refundCount, refundsCommitment := o.refundsCommitment,
                    gasBurntTotal := o.gasBurntTotal, tokensBurntTotal := o.tokensBurntTotal }

def hex (b : Bytes) : String :=
  let d := "0123456789abcdef".toList
  String.ofList (b.flatMap fun x => [d.getD (x.toNat / 16) '0', d.getD (x.toNat % 16) '0'])

end NearSpec.Codec
