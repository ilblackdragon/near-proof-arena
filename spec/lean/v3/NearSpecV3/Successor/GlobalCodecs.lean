import NearSpecV3.D2.TxD2
import Std.Data.HashMap

/-! Opt-in PV86 global codecs. Original D2 pBase/pRcpt remain rejecting. -/
namespace NearSpecV3.Successor.GlobalCodecs
open NearSpec NearSpecV3 NearSpecV3.D2

/-- Pinned borsh 1.5.7 has no de_strict_order feature: BTreeMap decoding sorts
keys and keeps the last occurrence, rather than rejecting noncanonical input order. -/
def pDsiGlobal : P D3.L4.Dsi := fun bs => do
  let (version, bs) ← pU8 "DeterministicAccountStateInit tag" bs
  if version != 0 then throw "decode: DeterministicAccountStateInit tag"
  let (code, bs) ← D3.L4.pGci bs
  let (entries, bs) ← pVec "state_init data" (fun bs => do
    let (k, bs) ← pBytes "state_init key" bs
    let (v, bs) ← pBytes "state_init value" bs
    pure ((k,v), bs)) bs
  let map := entries.foldl (fun (m : Std.HashMap Bytes Bytes) (k,v) => m.insert k v) {}
  let data := map.toList.mergeSort (fun a b => !bytesLt b.1 a.1)
  let (deposit, bs) ← pU128 "deposit" bs
  pure (⟨⟨code,data⟩,deposit⟩,bs)

/-- Re-serialization is canonical, including normalized state-init maps. -/
def baseRaw (raw : Bytes) (b : Base) : Bytes :=
  match b with
  | .stateInit d => [11] ++ d.encode
  | _ => raw

def nonceBytes (v2 : Bool) (n : Nat) (ni : Option Nat) : Bytes :=
  if v2 then match ni with | some i => [1] ++ u64 n ++ u16 i | none => [0] ++ u64 n
  else u64 n

def pBaseGlobal (tag : Nat) : P Base := fun bs => do
  match tag with
  | 9 => let (d, bs) ← D3.L4.pDeployGlobal bs; pure (.deployGlobal d, bs)
  | 10 => let (u, bs) ← D3.L4.pUseGlobal bs; pure (.useGlobal u, bs)
  | 11 => let (d, bs) ← pDsiGlobal bs; pure (.stateInit d, bs)
  | _ => pBase tag bs

def pBaseActGlobal : P BaseAct := fun bs => do
  let start := bs
  let (t, bs) ← pU8 "action tag" bs
  if t == 8 || t == 14 then throw "decode: DelegateAction mustn't contain a nested one"
  let (b, bs) ← pBaseGlobal t bs
  pure (⟨baseRaw (consumed start bs) b, b⟩, bs)


def pDelegateBodyGlobal (v2 : Bool) : P (Bytes × Bytes × List BaseAct × (Nat × Option Nat) × Nat × PublicKey) :=
  fun bs => do
    let (s, bs) ← pAccountId "sender_id" bs
    let (r, bs) ← pAccountId "receiver_id" bs
    let (acts, bs) ← pVec "delegate actions" pBaseActGlobal bs
    let (n, bs) ← if v2 then pTxNonce bs else (do let (n, bs) ← pU64 "nonce" bs; pure ((n, none), bs))
    let (mh, bs) ← pU64 "max_block_height" bs
    let (pk, bs) ← pPk "delegate public key" bs
    pure ((s, r, acts, n, mh, pk), bs)


def pActGlobal : P Act := fun bs => do
  let start := bs
  let (t, bs) ← pU8 "action tag" bs
  if t == 8 || t == 14 then
    let bs ← if t == 14 then (do
        let (pt, bs) ← pU8 "VersionedDelegateActionPayload tag" bs
        if pt != 0 then throw "decode: VersionedDelegateActionPayload tag"
        pure bs) else pure bs
    let ((s, r, acts, (n, ni), mh, pk), bs) ← pDelegateBodyGlobal (t == 14) bs
    let payload := (if t == 14 then [0] else []) ++ borshBytes s ++ borshBytes r ++
      u32 acts.length ++ concatAll (acts.map (·.raw)) ++ nonceBytes (t == 14) n ni ++ u64 mh ++ pk.encode
    let ((st, sig), bs) ← pSig "delegate" bs
    pure (.delegate ([UInt8.ofNat t] ++ payload ++ [UInt8.ofNat st] ++ sig)
      ⟨t == 14, s, r, acts, n, ni, mh, pk, payload, st, sig⟩, bs)
  else
    let (b, bs) ← pBaseGlobal t bs
    pure (.base ⟨baseRaw (consumed start bs) b, b⟩, bs)


def pActionRGlobal (v2 : Bool) : P ActionR := fun bs => do
  let (s, bs) ← pAccountId "signer_id" bs
  let (rt, bs) ← if v2 then pOption "refund_to" (pAccountId "refund_to") bs else pure (none, bs)
  let (pk, bs) ← pPk "signer_public_key" bs
  let (gp, bs) ← pU128 "gas_price" bs
  let (outs, bs) ← pVec "output_data_receivers" (fun bs => do
      let (d, bs) ← pHash "data_id" bs
      let (r, bs) ← pAccountId "data receiver" bs
      pure ((d, r), bs)) bs
  let (ins, bs) ← pVec "input_data_ids" (pHash "input data id") bs
  let (acts, bs) ← pVec "actions" pActGlobal bs
  pure (⟨v2, s, rt, pk, gp, outs, ins, acts⟩, bs)


def pDistribution : P Distribution := fun bs => do
  let (v, bs) ← pU8 "GlobalContractDistribution version" bs
  if v > 1 then throw "decode: GlobalContractDistribution version"
  let (id, bs) ← D3.L4.pGci bs
  let (target, bs) ← pU64 "target_shard" bs
  let (delivered, bs) ← pVec "delivered shards" (pU64 "shard") bs
  let (code, bs) ← pBytes "global code" bs
  let (nonce, bs) ← if v == 1 then pU64 "global nonce" bs else pure (0, bs)
  pure (⟨v == 1, id, target, delivered, code, nonce⟩, bs)

def pRcptGlobal : P Rcpt := fun bs => do
  let (pred, bs) ← pAccountId "predecessor_id" bs
  let (recv, bs) ← pAccountId "receiver_id" bs
  let (rid, bs) ← pHash "receipt_id" bs
  let (tag, bs) ← pU8 "ReceiptEnum tag" bs
  match tag with
  | 0 => do let (a, bs) ← pActionRGlobal false bs; pure (⟨pred, recv, rid, .action false a⟩, bs)
  | 2 => do let (a, bs) ← pActionRGlobal false bs; pure (⟨pred, recv, rid, .action true a⟩, bs)
  | 5 => do let (a, bs) ← pActionRGlobal true bs; pure (⟨pred, recv, rid, .action false a⟩, bs)
  | 6 => do let (a, bs) ← pActionRGlobal true bs; pure (⟨pred, recv, rid, .action true a⟩, bs)
  | 1 | 3 => do
    let (d, bs) ← pHash "data_id" bs
    let (x, bs) ← pOption "data" (pBytes "data") bs
    pure (⟨pred, recv, rid, .data (tag == 3) d x⟩, bs)
  | 4 => do let (d, bs) ← pDistribution bs; pure (⟨pred, recv, rid, .distribution d⟩, bs)
  | _ => throw "decode: ReceiptEnum tag"


def decodeRcptGlobal (b : Bytes) : Except String Rcpt := do
  let (r, rest) ← pRcptGlobal b
  if !rest.isEmpty then throw "decode: trailing bytes in receipt"
  pure r


def decodeStoredGlobal (b : Bytes) : Except String Stored := do
  match b with
  | 255 :: 255 :: v :: rest =>
    if v != 0 && v != 1 then throw "decode: StateStoredReceipt version"
    let (r, rest) ← pRcptGlobal rest
    let (g, rest) ← pU64 "congestion_gas" rest
    let (s, rest) ← pU64 "congestion_size" rest
    if !rest.isEmpty then throw "decode: trailing bytes in StateStoredReceipt"
    pure ⟨r, some (g, s, v.toNat)⟩
  | _ => do
    let r ← decodeRcptGlobal b
    pure ⟨r, none⟩


def pTxD2Global : P TxD2 := fun bs => do
  let start := bs
  let (u1, r1) ← pU8 "transaction version" bs
  let (u2, _) ← pU8 "transaction version" r1
  let (v1, bs) ←
    if u2 == 0 then pure (false, bs)
    else if u1 == 1 then pure (true, r1)
    else throw "decode: invalid transaction version tag"
  let (signer, bs) ← pAccountId "signer_id" bs
  let (pk, bs) ← pPublicKey "tx public_key" bs
  if pk.tag != 0 then throw "out of domain (w.shape): non-ED25519 transaction key"
  let ((nonce, ni), bs) ← if v1 then pTxNonce bs else (do let (n, bs) ← pU64 "nonce" bs; pure ((n, none), bs))
  let (recv, bs) ← pAccountId "receiver_id" bs
  let (bh, bs) ← pHash "block_hash" bs
  let rawPrefix := consumed start bs
  let (acts, bs) ← pVec "actions" pActGlobal bs
  let (strict, bs) ← if v1 then (do
      let (m, bs) ← pU8 "NonceMode" bs
      if m == 0 then pure (false, bs) else if m == 1 then pure (true, bs)
      else throw "decode: NonceMode tag")
    else pure (false, bs)
  let body := rawPrefix ++ u32 acts.length ++ concatAll (acts.map Act.raw) ++
    (if v1 then [if strict then 1 else 0] else [])
  let (st, bs) ← pU8 "signature type" bs
  if st != 0 then
    if st == 1 || st == 2 then throw "out of domain (w.shape): non-ED25519 transaction signature"
    else throw "decode: unknown signature tag"
  let (sig, bs) ← pTake 64 "ed25519 signature" bs
  if (sig.getD 63 0).toNat / 32 != 0 then throw "decode: ed25519 signature high bits"
  pure (⟨body ++ [0] ++ sig, body, signer, pk, nonce, ni, recv, bh, acts, strict, sig⟩, bs)

def decodeStoredRcptGlobal (b : Bytes) (what : String) : Except String Rcpt :=
  match decodeRcptGlobal b with
  | .ok r => .ok r
  | .error e => if isShapeOOD e then .error e else .error (inconsistent what)

end NearSpecV3.Successor.GlobalCodecs
