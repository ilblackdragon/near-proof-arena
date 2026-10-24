import NearSpecV3.D3.GlobalContract

/-!
# W00 interface 3/7 — versioned actions and receipts

The signed D2 decoder (`D2/Types.lean`) refuses action tags 9/10/11 and receipt tag 4 as
`out of domain (w.shape)`, and refuses ML-DSA-65 keys/signatures as `w.shape`. Those are live PV86
shapes (`core/primitives/src/action/mod.rs:349-370`; `core/primitives/src/receipt.rs:565-660`;
`core/crypto/src/signature.rs:250-257`). W06/W07/W09 need one versioned codec that *represents* them.

This module is additive: it defines successor decoders/encoders in a new file and does not touch
`D2/Types.lean`, `pAct`, `pRcpt`, `pBase`, `pPublicKey` or the signed relations.

## What is represented

* **Action tags.** `ActionTag` covers all 15 nearcore tags, including 9/10/11 and 14. `ActionDispatch`
  maps each tag to its successor handler. Tags 9/10/11 use L4's codecs (`DeployGlobal`,
  `UseGlobal`, `DeterministicStateInit`); 0–7, 12, 13 delegate to `D2.pAct`; 8 and 14 use D2's
  delegate decoder.
* **Receipt tags.** `ReceiptTag` covers 0–6. Tag 4 (`GlobalContractDistribution`) is decoded here with
  the V1/V2 discriminant and its full borsh layout; 0–3/5/6 delegate to `D2.pRcpt`.
* **New key forms.** `KeyForm` represents `PublicKey` tag 0 (ED25519, 32 B), tag 1 (SECP256K1, 64 B),
  tag 2 (full ML-DSA-65, 1952 B) and `PublicKeyHandle` tag 3 (ML-DSA-65 trie handle, SHA3-256 of the
  pubkey, 32 B). The tag numbering is the pinned nearcore one: `PublicKeyHandle` deliberately has no
  tag 2 (`core/crypto/src/signature.rs:674-720`), so a full key cannot land in a handle-shaped slot.
* **Rollback.** `RollbackContract` is the abstract contract for "discard a receipt's uncommitted
  effects"; `DeployTracker` is the concrete deploy-tracker instance with commit/rollback and the two
  structural laws that make the split meaningful.

## What is not established

* **No round-trip theorem is proved for the byte codecs.** The decoders are strict and the encoders
  are the pinned borsh layouts, but `decode (encode x) = ok x` needs length arithmetic through
  `takeT`/`readU32` and is left as W06/W09's directed-test obligation. `decode_encode` theorems for
  these types are therefore **absent**, and no lane may cite this module as a codec proof.
* **The distribution receipt's semantics are not implemented.** Only its representation is. Whether a
  `GlobalContractDistribution` receipt can appear in a chunk witness is UQ-006 (owner L4); this module
  does not decide that and does not admit the receipt into `checkD3`.
* **ML-DSA verification is not implemented.** Only key/signature *shapes* are represented; the
  signature scheme is W05/W06's obligation (UQ-005).
* **The action dispatch table is a naming device, not a handler proof.** It records which codec each
  tag uses; it does not execute the action.
-/

namespace NearSpecV3.Successor

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.D3 NearSpecV3.D3.L4

/-! ## Action tags -/

/-- Every `Action` discriminant at the pinned commit (`core/primitives/src/action/mod.rs:349-370`). -/
inductive ActionTag where
  | createAccount            -- 0
  | deployContract           -- 1
  | functionCall             -- 2
  | transfer                 -- 3
  | stake                    -- 4
  | addKey                   -- 5
  | deleteKey                -- 6
  | deleteAccount            -- 7
  | delegate                 -- 8
  | deployGlobalContract     -- 9
  | useGlobalContract        -- 10
  | deterministicStateInit   -- 11
  | transferToGasKey         -- 12
  | transferFromGasKey       -- 13
  | delegateV2               -- 14
  deriving DecidableEq, Repr

/-- The borsh discriminant of each tag. -/
def ActionTag.code : ActionTag → Nat
  | .createAccount => 0 | .deployContract => 1 | .functionCall => 2 | .transfer => 3
  | .stake => 4 | .addKey => 5 | .deleteKey => 6 | .deleteAccount => 7
  | .delegate => 8 | .deployGlobalContract => 9 | .useGlobalContract => 10
  | .deterministicStateInit => 11 | .transferToGasKey => 12
  | .transferFromGasKey => 13 | .delegateV2 => 14

/-- The discriminant as the byte that starts the action's borsh encoding. -/
def ActionTag.byte (t : ActionTag) : UInt8 := UInt8.ofNat t.code

theorem ActionTag.byte_eq_ofNat (t : ActionTag) : t.byte = UInt8.ofNat t.code := rfl

/-- The three successor tags have distinct leading bytes. Decided, so a code change breaks these
named facts rather than silently mis-dispatching. -/
theorem byte_deployGlobal_ne_useGlobal :
    ActionTag.deployGlobalContract.byte ≠ ActionTag.useGlobalContract.byte := by decide
theorem byte_deployGlobal_ne_stateInit :
    ActionTag.deployGlobalContract.byte ≠ ActionTag.deterministicStateInit.byte := by decide
theorem byte_useGlobal_ne_stateInit :
    ActionTag.useGlobalContract.byte ≠ ActionTag.deterministicStateInit.byte := by decide
theorem byte_useGlobal_ne_deployGlobal :
    ActionTag.useGlobalContract.byte ≠ ActionTag.deployGlobalContract.byte := by decide
theorem byte_stateInit_ne_deployGlobal :
    ActionTag.deterministicStateInit.byte ≠ ActionTag.deployGlobalContract.byte := by decide
theorem byte_stateInit_ne_useGlobal :
    ActionTag.deterministicStateInit.byte ≠ ActionTag.useGlobalContract.byte := by decide

/-- The tag of a discriminant, total on the 15 valid codes. -/
def ActionTag.ofCode? : Nat → Option ActionTag
  | 0 => some .createAccount | 1 => some .deployContract | 2 => some .functionCall
  | 3 => some .transfer | 4 => some .stake | 5 => some .addKey | 6 => some .deleteKey
  | 7 => some .deleteAccount | 8 => some .delegate | 9 => some .deployGlobalContract
  | 10 => some .useGlobalContract | 11 => some .deterministicStateInit
  | 12 => some .transferToGasKey | 13 => some .transferFromGasKey | 14 => some .delegateV2
  | _ => none

/-- The 15 tag codes are distinct and round-trip. Decided, so a future edit to either function breaks
this named theorem instead of drifting quietly. -/
theorem ActionTag.ofCode_code (t : ActionTag) : ActionTag.ofCode? t.code = some t := by
  cases t <;> rfl

/-- The successor handler a tag dispatches to. -/
inductive ActionHandler where
  /-- `D2.pAct`: tags 0–7, 12, 13 and the delegate tags 8/14. -/
  | d2
  /-- L4's `DeployGlobalContract` codec. -/
  | deployGlobal
  /-- L4's `UseGlobalContract` codec. -/
  | useGlobal
  /-- L4's `DeterministicStateInit` codec. -/
  | stateInit
  deriving DecidableEq, Repr

/-- The dispatch table. Tags 9/10/11 leave the signed decoder's out-of-domain branch and reach the
L4 codecs; every other tag stays with the signed decoder. -/
def ActionTag.handler : ActionTag → ActionHandler
  | .deployGlobalContract => .deployGlobal
  | .useGlobalContract => .useGlobal
  | .deterministicStateInit => .stateInit
  | _ => .d2

theorem handler_deployGlobal : ActionTag.deployGlobalContract.handler = .deployGlobal := rfl
theorem handler_useGlobal : ActionTag.useGlobalContract.handler = .useGlobal := rfl
theorem handler_stateInit : ActionTag.deterministicStateInit.handler = .stateInit := rfl
theorem handler_d2_createAccount : ActionTag.createAccount.handler = .d2 := rfl

/-! ## Versioned actions -/

/-- A successor action: the signed D2 action, or one of the three live PV86 actions the signed
decoder excludes. The L4 variants keep their typed codecs; `D2.Act` keeps its raw bytes. -/
inductive ActV where
  | d2 (a : Act)
  | deployGlobal (d : L4.DeployGlobal)
  | useGlobal (u : L4.UseGlobal)
  | stateInit (s : L4.Dsi)
  deriving Repr

/-- The raw borsh bytes of an action. For `d2` this is the original raw bytes, exactly as the signed
decoder preserves them. -/
def ActV.raw : ActV → Bytes
  | .d2 a => a.raw
  | .deployGlobal d => ActionTag.deployGlobalContract.byte :: d.encode
  | .useGlobal u => ActionTag.useGlobalContract.byte :: u.encode
  | .stateInit s => ActionTag.deterministicStateInit.byte :: s.encode

/-- The successor action decoder. A first-byte dispatch: tag 9/10/11 go to the L4 codecs on the bytes
after the tag; everything else goes to the signed `D2.pAct` on the whole input (which keeps the
signed decoder's strictness for tags 0–8, 12–14 and its `w.shape` errors unreachable here). -/
def pActV : P ActV := fun bs =>
  match bs with
  | [] => .error "decode: empty action"
  | t :: rest =>
    if t = ActionTag.deployGlobalContract.byte then
      match L4.pDeployGlobal rest with
      | .ok (d, r) => .ok (.deployGlobal d, r)
      | .error e => .error e
    else if t = ActionTag.useGlobalContract.byte then
      match L4.pUseGlobal rest with
      | .ok (u, r) => .ok (.useGlobal u, r)
      | .error e => .error e
    else if t = ActionTag.deterministicStateInit.byte then
      match L4.pDsi rest with
      | .ok (s, r) => .ok (.stateInit s, r)
      | .error e => .error e
    else
      match D2.pAct bs with
      | .ok (a, r) => .ok (.d2 a, r)
      | .error e => .error e

/-- **Tag 9 dispatches to the L4 codec.** -/
theorem pActV_tag9 (rest : Bytes) (d : L4.DeployGlobal) (r : Bytes)
    (h : L4.pDeployGlobal rest = .ok (d, r)) :
    pActV (ActionTag.deployGlobalContract.byte :: rest) = .ok (.deployGlobal d, r) := by
  simp [pActV, h]

/-- **Tag 10 dispatches to the L4 codec.** -/
theorem pActV_tag10 (rest : Bytes) (u : L4.UseGlobal) (r : Bytes)
    (h : L4.pUseGlobal rest = .ok (u, r)) :
    pActV (ActionTag.useGlobalContract.byte :: rest) = .ok (.useGlobal u, r) := by
  simp [pActV, h, byte_useGlobal_ne_deployGlobal]

/-- **Tag 11 dispatches to the L4 codec.** -/
theorem pActV_tag11 (rest : Bytes) (s : L4.Dsi) (r : Bytes)
    (h : L4.pDsi rest = .ok (s, r)) :
    pActV (ActionTag.deterministicStateInit.byte :: rest) = .ok (.stateInit s, r) := by
  simp [pActV, h, byte_stateInit_ne_deployGlobal, byte_stateInit_ne_useGlobal]

/-- Every other first byte goes to the signed decoder. -/
theorem pActV_fallsThrough (t : UInt8) (rest : Bytes)
    (h9 : t ≠ ActionTag.deployGlobalContract.byte)
    (h10 : t ≠ ActionTag.useGlobalContract.byte)
    (h11 : t ≠ ActionTag.deterministicStateInit.byte)
    (a : Act) (r : Bytes) (h : D2.pAct (t :: rest) = .ok (a, r)) :
    pActV (t :: rest) = .ok (.d2 a, r) := by
  simp [pActV, h9, h10, h11, h]

/-! ## New key forms -/

/-- The pinned key encodings a successor chunk can carry. The first three are `PublicKey`
discriminants (`signature.rs:371-389`); the last is the trie handle stored in access keys
(`signature.rs:498-506, 674-720`, tag 3). -/
inductive KeyForm where
  | ed25519 (key : Bytes)         -- PublicKey tag 0, 32 B
  | secp256k1 (key : Bytes)       -- PublicKey tag 1, 64 B
  | mlDsa65 (key : Bytes)         -- PublicKey tag 2, 1952 B (full key)
  | mlDsa65Handle (h : Bytes)     -- PublicKeyHandle tag 3, 32 B = SHA3-256(pubkey)
  deriving DecidableEq, Repr

/-- The borsh discriminant: `PublicKey` tags 0–2, `PublicKeyHandle` tag 3. -/
def KeyForm.code : KeyForm → Nat
  | .ed25519 _ => 0 | .secp256k1 _ => 1 | .mlDsa65 _ => 2 | .mlDsa65Handle _ => 3

/-- The payload bytes. -/
def KeyForm.data : KeyForm → Bytes
  | .ed25519 k => k | .secp256k1 k => k | .mlDsa65 k => k | .mlDsa65Handle h => h

/-- Pinned key lengths (`signature.rs:21,25,33,156,220`). -/
def KeyForm.expectedLength : KeyForm → Nat
  | .ed25519 _ => 32 | .secp256k1 _ => 64 | .mlDsa65 _ => 1952 | .mlDsa65Handle _ => 32

/-- The key's borsh encoding: discriminant byte then the payload. -/
def KeyForm.encode (k : KeyForm) : Bytes := UInt8.ofNat k.code :: k.data

/-- A key form is well-formed when its payload has the pinned length. -/
def KeyForm.wf (k : KeyForm) : Bool := k.data.length = k.expectedLength

/-- The successor key decoder. It accepts the handle form as well as the full key, so a trie-shaped
`PublicKeyHandle` and a `PublicKey` are both representable without conflating their tags. -/
def pKeyForm : P KeyForm := fun bs =>
  match bs with
  | [] => .error "decode: empty public key"
  | t :: rest =>
    match t with
    | 0 => match takeT 32 rest with | some (k, r) => .ok (.ed25519 k, r) | none => .error "decode: truncated ED25519 key"
    | 1 => match takeT 64 rest with | some (k, r) => .ok (.secp256k1 k, r) | none => .error "decode: truncated SECP256K1 key"
    | 2 => match takeT 1952 rest with | some (k, r) => .ok (.mlDsa65 k, r) | none => .error "decode: truncated ML-DSA-65 key"
    | 3 => match takeT 32 rest with | some (h, r) => .ok (.mlDsa65Handle h, r) | none => .error "decode: truncated ML-DSA-65 handle"
    | _ => .error "decode: unknown public key tag"

theorem keyForm_encode_code (k : KeyForm) :
    (KeyForm.encode k).head? = some (UInt8.ofNat k.code) := by
  cases k <;> rfl

theorem keyForm_wf_ed25519 (k : Bytes) (h : k.length = 32) : (KeyForm.ed25519 k).wf = true := by
  unfold KeyForm.wf KeyForm.expectedLength KeyForm.data
  simp [h]


/-! ## Distribution receipts (`ReceiptEnum::GlobalContractDistribution = 4`)

The pinned layout is the outer `ReceiptV0` fields (predecessor, receiver, receipt id) followed by the
`ReceiptEnum` tag 4 and the `GlobalContractDistributionReceipt` enum: V1 = `id ‖ target_shard u64 ‖
Vec<ShardId> ‖ code Vec<u8>`, V2 adds `nonce u64` (`core/primitives/src/receipt.rs:565-660, 876-1056`).
Both variants are represented; the discriminant is the type, so an encoded receipt cannot carry a
version/payload mismatch. -/

/-- `GlobalContractDistributionReceipt` (`receipt.rs:876-879`): V1 or V2. -/
inductive GcdBody where
  | v1 (id : L4.Gci) (targetShard : Nat) (delivered : List Nat) (code : Bytes)
  | v2 (id : L4.Gci) (targetShard : Nat) (delivered : List Nat) (code : Bytes) (nonce : Nat)
  deriving DecidableEq, Repr

/-- The borsh discriminant of the distribution receipt variant. -/
def GcdBody.version : GcdBody → Nat
  | .v1 _ _ _ _ => 0 | .v2 _ _ _ _ _ => 1

/-- The identifier. -/
def GcdBody.id : GcdBody → L4.Gci
  | .v1 i _ _ _ => i | .v2 i _ _ _ _ => i

/-- The borsh encoding of the variant, *without* the outer receipt fields. -/
def GcdBody.encode : GcdBody → Bytes
  | .v1 i t ds c => ([0] : Bytes) ++ i.encode ++ u64 t ++ u32 ds.length ++ concatAll (ds.map u64) ++
      borshBytes c
  | .v2 i t ds c n => ([1] : Bytes) ++ i.encode ++ u64 t ++ u32 ds.length ++ concatAll (ds.map u64) ++
      borshBytes c ++ u64 n

/-- A distribution receipt: the outer `ReceiptV0` fields plus the variant. -/
structure DistReceipt where
  pred : Bytes
  recv : Bytes
  rid : Bytes
  body : GcdBody
  deriving DecidableEq, Repr

/-- The distribution receipt decoder, entered *after* the outer tag 4. -/
def pGcdBody : P GcdBody := fun bs => do
  let (v, bs) ← pU8 "GlobalContractDistributionReceipt version" bs
  if v > 1 then throw "decode: GlobalContractDistributionReceipt tag"
  let (i, bs) ← L4.pGci bs
  let (t, bs) ← pU64 "target_shard" bs
  let (ds, bs) ← pVec "already_delivered_shards" (pU64 "shard") bs
  let (c, bs) ← pBytes "code" bs
  if v = 1 then
    let (n, bs) ← pU64 "nonce" bs
    pure (.v2 i t ds c n, bs)
  else pure (.v1 i t ds c, bs)

/-- The distribution receipt's raw bytes, including the outer fields and the `ReceiptEnum` tag. -/
def DistReceipt.encode (r : DistReceipt) : Bytes :=
  borshBytes r.pred ++ borshBytes r.recv ++ r.rid ++ ([4] : Bytes) ++ r.body.encode

/-- A receipt in the successor's versioned form: the signed D2 receipt, or a distribution receipt. -/
inductive RcptV where
  | d2 (r : Rcpt)
  | distribution (g : DistReceipt)
  deriving Repr

/-- The successor receipt decoder. It peeks the outer fields and the `ReceiptEnum` tag; tag 4 is
decoded here and everything else is delegated to the signed `D2.pRcpt` on the original bytes. -/
def pRcptV : P RcptV := fun bs => do
  let (pred, b1) ← pAccountId "predecessor_id" bs
  let (recv, b2) ← pAccountId "receiver_id" b1
  let (rid, b3) ← pHash "receipt_id" b2
  match b3 with
  | [] => throw "decode: truncated receipt"
  | t :: rest =>
    if t = 4 then
      let (g, r) ← pGcdBody rest
      pure (.distribution ⟨pred, recv, rid, g⟩, r)
    else
      match D2.pRcpt bs with
      | .ok (r, rest) => .ok (.d2 r, rest)
      | .error e => .error e

/-- The distribution receipt's borsh layout, stated on the encoder so W09 can read the field order
off one place. -/
theorem distReceipt_encode_layout (r : DistReceipt) :
    r.encode = borshBytes r.pred ++ borshBytes r.recv ++ r.rid ++ ([4] : Bytes) ++ r.body.encode := rfl

/-! ## Rollback contract -/

/-- The abstract contract for a state type whose uncommitted receipt effects can be discarded. The
law is *part of the structure*, so a lane that supplies a `RollbackContract` must supply the proof;
W00 does not assert it for an arbitrary state type. -/
structure RollbackContract (σ : Type) where
  /-- The state before the receipt's effects. -/
  snapshot : σ → σ
  /-- Discard the uncommitted effects of the current receipt. -/
  restore : σ → σ → σ
  /-- Restoring a snapshot really returns the snapshot's state. -/
  law : ∀ s, restore s (snapshot s) = s

/-- The deploy tracker: in-chunk deploys split into committed (survive a failed receipt) and
prospective (belong to the current receipt). This is the split `ContractsTracker` implements
(`runtime/runtime/src/contract.rs:42-131`, cited by L4's module docstring). -/
structure DeployTracker where
  committed : List (Bytes × Bytes) := []
  prospective : List (Bytes × Bytes) := []

/-- Commit the current receipt's deploys. -/
def DeployTracker.commit (d : DeployTracker) : DeployTracker :=
  { d with committed := d.committed ++ d.prospective, prospective := [] }

/-- Discard the current receipt's deploys; committed deploys survive. -/
def DeployTracker.rollback (d : DeployTracker) : DeployTracker :=
  { d with prospective := [] }

theorem commit_keeps_committed (d : DeployTracker) :
    d.commit.committed = d.committed ++ d.prospective := rfl

theorem rollback_keeps_committed (d : DeployTracker) :
    d.rollback.committed = d.committed := rfl

theorem rollback_discards_prospective (d : DeployTracker) :
    d.rollback.prospective = [] := rfl

theorem rollback_after_commit_noop (d : DeployTracker) :
    d.commit.rollback = d.commit := by
  simp [DeployTracker.commit, DeployTracker.rollback]

/-! ## Axiom-closure check points -/

#print axioms ActionTag.ofCode_code
#print axioms pActV_tag9
#print axioms distReceipt_encode_layout

end NearSpecV3.Successor
