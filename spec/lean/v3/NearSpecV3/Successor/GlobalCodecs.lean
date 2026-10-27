import NearSpecV3.D2.TxD2
import Std.Data.TreeMap

/-! Opt-in PV86 global codecs. Original D2 pBase/pRcpt remain rejecting. -/
namespace NearSpecV3.Successor.GlobalCodecs
open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## Key widening for action positions

`D2.pPk` excludes ML-DSA-65 (tag 2) as `w.shape` so the signed statement stays as it was. The
successor admits tag 2 wherever a key only needs to be *stored*: `Stake`/`AddKey`/`DeleteKey` and the
two gas-key actions carry a key but never verify a signature with it. The stored form is the 33-byte
tag-3 handle `NearSpec.PublicKey.handle` computes, so a 1952-byte key never lands in state.

Signing positions admit ML-DSA-65 too (W06): the transaction key and signature (`pTxD2Global`), the
delegate key and signature (`pDelegateBodyGlobal`, `pSigGlobal`) and the receipt signer key
(`pActionRGlobal`). Verification is `MlDsa65.verify` (FIPS 204, pure, empty context) in
`TxD2.sigOk` / `D2.actDelegate`, and the `ml_dsa_65_verification_cost` burnt-gas term is
`D2.txSigVerifyCost`. -/

/-- `PublicKey` with ML-DSA-65 admitted. Identical to `D2.pPk` on tags 0/1. -/
def pPkGlobal (w : String) : P PublicKey := fun bs => do
  let (pk, bs) ← pPublicKey w bs
  if pk.tag > 2 then throw s!"decode: unknown PublicKey tag ({w})"
  pure (pk, bs)

/-- `Signature` borsh with ML-DSA-65 admitted (`signature.rs:1168-1196`): tag 2 reads exactly 3,309
bytes, with no further check at decode time (`read_exact`). Identical to `D2.pSig` on tags 0/1. -/
def pSigGlobal (w : String) : P (Nat × Bytes) := fun bs => do
  let (t, rest) ← pU8 (w ++ " signature type") bs
  if t == 2 then do let (d, rest) ← pTake 3309 w rest; pure ((2, d), rest)
  else pSig w bs

/-- `NonDelegateAction` with the key positions widened. Identical to `D2.pBase` except that tags 4–6,
12 and 13 accept an ML-DSA-65 key; the body layouts are the pinned ones. -/
def pBaseGlobalKeyed (tag : Nat) : P Base := fun bs =>
  match tag with
  | 4 => do
    let (s, bs) ← pU128 "stake" bs
    let (pk, bs) ← pPkGlobal "stake key" bs
    pure (.stake s pk, bs)
  | 5 => do
    let (pk, bs) ← pPkGlobal "add key" bs
    let (ak, bs) ← pAK bs
    pure (.addKey pk ak, bs)
  | 6 => do let (pk, bs) ← pPkGlobal "delete key" bs; pure (.deleteKey pk, bs)
  | 12 => do
    let (pk, bs) ← pPkGlobal "gas key" bs
    let (d, bs) ← pU128 "deposit" bs
    pure (.toGasKey pk d, bs)
  | 13 => do
    let (pk, bs) ← pPkGlobal "gas key" bs
    let (a, bs) ← pU128 "amount" bs
    pure (.fromGasKey pk a, bs)
  | _ => pBase tag bs

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
  let map := entries.foldl (fun (m : Std.TreeMap Bytes Bytes compare) (k,v) => m.insert k v) {}
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
  -- Key positions admit ML-DSA-65 (tag 2); these actions store the key but never sign with it.
  | 4 | 5 | 6 | 12 | 13 => pBaseGlobalKeyed tag bs
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
    let (pk, bs) ← pPkGlobal "delegate public key" bs
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
    let ((st, sig), bs) ← pSigGlobal "delegate" bs
    pure (.delegate ([UInt8.ofNat t] ++ payload ++ [UInt8.ofNat st] ++ sig)
      ⟨t == 14, s, r, acts, n, ni, mh, pk, payload, st, sig⟩, bs)
  else
    let (b, bs) ← pBaseGlobal t bs
    pure (.base ⟨baseRaw (consumed start bs) b, b⟩, bs)


def pActionRGlobal (v2 : Bool) : P ActionR := fun bs => do
  let (s, bs) ← pAccountId "signer_id" bs
  let (rt, bs) ← if v2 then pOption "refund_to" (pAccountId "refund_to") bs else pure (none, bs)
  -- An ML-DSA-65 signer key is carried in full (1,953 bytes) by the receipts of an ML-DSA-signed
  -- transaction; refunds and allowance updates address its access key by `PublicKey.handle`.
  let (pk, bs) ← pPkGlobal "signer_public_key" bs
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
  -- The signed layer (`D2.pTxD2`) excludes non-ED25519 keys; the successor admits all three
  -- families. ML-DSA-65 is verified by `MlDsa65.verify` and charged `ml_dsa_65_verification_cost`
  -- (`85.yaml:15`, `runtime/src/config.rs:426-441, 512-526`) through `D2.txCostD2`.
  let (pk, bs) ← pPkGlobal "tx public_key" bs
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
  -- `Signature` borsh decodes independently of the key (`signature.rs:1168-1196`): ED25519 64 B with
  -- the high-bit check, SECP256K1 65 B `r ‖ s ‖ rec_id`, ML-DSA-65 3,309 B. A key/signature type
  -- mismatch decodes, and `Signature::verify`'s catch-all arm returns `false`
  -- (`signature.rs:1129`), so the transaction is dropped as `InvalidSignature` by `TxD2.sigOk`.
  let (st, bs) ← pU8 "signature type" bs
  let (sig, bs) ← match st with
    | 0 => pTake 64 "ed25519 signature" bs
    | 1 => pTake 65 "secp256k1 signature" bs
    | 2 => pTake 3309 "ml-dsa-65 signature" bs
    | _ => throw "decode: unknown signature tag"
  if st == 0 && (sig.getD 63 0).toNat / 32 != 0 then throw "decode: ed25519 signature high bits"
  pure (⟨body ++ [UInt8.ofNat st] ++ sig, body, signer, pk, nonce, ni, recv, bh, acts, strict, st, sig⟩, bs)

def decodeStoredRcptGlobal (b : Bytes) (what : String) : Except String Rcpt :=
  match decodeRcptGlobal b with
  | .ok r => .ok r
  | .error e => if isShapeOOD e then .error e else .error (inconsistent what)

end NearSpecV3.Successor.GlobalCodecs
