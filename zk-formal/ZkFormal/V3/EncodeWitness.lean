import NearSpecV3.WitnessV3
import NearSpecV3.ClaimV3Props
import ReexecV3D0.NormalForm

/-!
# Witness encoder for the D0 witness shape, and its kernel-checked round trip

`encodeSW : StateWitness → Bytes` writes nearcore's borsh `ChunkStateWitness::V2`
(V3-D0-DESIGN.md §6.2):

  `1 ‖ epoch_id ‖ ShardChunkHeader::V3 (2 ‖ inner ‖ u64 height_included ‖ signature)
   ‖ main_state_transition ‖ Vec<(ChunkHash, ReceiptProof)> ‖ applied_receipts_hash
   ‖ u32 0 (transactions) ‖ Vec implicit_transitions ‖ u32 0 (new_transactions)`

`StateWitness` keeps neither `height_included` nor the chunk signature (the decoder
checks and drops them), so the encoder writes the normal form's fixed values: `height_included = 0`
(`zeros8`) and the ED25519 all-zero 64-byte signature (`sig0`).

`encodeWitnessFile sw = bytes "near-arena-witness-v3" ‖ bytes (encodeSW sw) ‖ u32 0`.

`D0Shape sw` (= `D0Shape.wf sw = true`, executable) lists exactly the conditions under
which the strict decoders invert the encoders: widths of hashes / integers / lengths,
the D0 receipt shape, path directions ≤ 1, a V4/V5 inner whose raw proposals and
proposed split re-parse, `innerBytes = encodeChunkInner inner`, no transactions, and
the 64 MiB size bound.

Main results: `encodeWitness_roundtrip : EncodeWitnessStmt` and, against the reference
candidate's witness normal form (`ReexecV3D0.normW` / `normSW` / `normalW`),
`encodeWitness_normal : EncodeWitnessNormalStmt` and `normalW_encodeWitnessFile`. The fixed
header fields and the transition encoding are the reference's own `zeros8`, `sig0`, `encTr`.
-/

namespace ZkFormal.V3

open NearSpec NearSpecV3 ReexecV3D0

/-! ## Encoders -/

/-- `ChunkStateTransition` with `PartialState::TrieValues`: the reference's `encTr`. -/
def encodeTransition (t : Transition) : Bytes := encTr t

def encodePathItem (p : Bytes × Nat) : Bytes := p.1 ++ u8 p.2

def encodeEntry (e : ProofEntry) : Bytes :=
  e.key ++ encList Receipt.encode e.receipts ++ u64 e.proof.fromShard ++ u64 e.proof.toShard ++
  encList encodePathItem e.proof.path

def encodeCongestion (c : Congestion) : Bytes :=
  u8 0 ++ u128 c.delayedGas ++ u128 c.bufferedGas ++ u64 c.receiptBytes ++ u16 c.allowedShard

def encodeBwRequest (q : BwRequest) : Bytes := u16 q.toShard ++ q.bitmap

def encodeBwRequests (l : List BwRequest) : Bytes := u8 0 ++ encList encodeBwRequest l

/-- Tagged `ShardChunkHeaderInner` (V4 = 3 / V5 = 4); proposals and the proposed split
are stored raw and written verbatim. -/
def encodeChunkInner (ci : ChunkInner) : Bytes :=
  u8 ci.tag ++ ci.prevBlockHash ++ ci.prevStateRoot ++ ci.prevOutcomeRoot ++
  ci.encodedMerkleRoot ++ u64 ci.encodedLength ++ u64 ci.heightCreated ++ u64 ci.shardId ++
  u64 ci.prevGasUsed ++ u64 ci.gasLimit ++ u128 ci.prevBalanceBurnt ++
  ci.prevOutgoingReceiptsRoot ++ ci.txRoot ++ encList (fun b => b) ci.proposals ++
  encodeCongestion ci.congestion ++ encodeBwRequests ci.bwRequests ++
  (if ci.tag == 4 then encOpt (fun b => b) ci.proposedSplit else [])

/-- `ChunkStateWitness::V2` bytes. -/
def encodeSW (sw : StateWitness) : Bytes :=
  u8 1 ++ sw.epochId ++ u8 2 ++ sw.innerBytes ++ zeros8 ++ sig0 ++
  encodeTransition sw.main ++ encList encodeEntry sw.entries ++ sw.appliedReceiptsHash ++
  u32 0 ++ encList encodeTransition sw.implicit ++ u32 0

/-- `witness.bin` with no contract code. -/
def encodeWitnessFile (sw : StateWitness) : Bytes :=
  borshBytes witnessTag ++ borshBytes (encodeSW sw) ++ u32 0

/-! ## The D0 shape -/

def h32 (b : Bytes) : Bool := b.length == 32

/-- `PublicKey` accepted by `pPublicKey` (tags 0/1/2 with their data lengths). -/
def pkWf3 (k : PublicKey) : Bool :=
  (k.tag == 0 && k.data.length == 32) || (k.tag == 1 && k.data.length == 64) ||
  (k.tag == 2 && k.data.length == 1952)

def encVS (a : Bytes) (k : PublicKey) (s : Nat) : Bytes := u8 0 ++ borshBytes a ++ k.encode ++ u128 s

/-- Candidate decomposition of a raw `ValidatorStake` (only used to state `vsWf`;
soundness does not depend on it, `vsWf` re-checks the encoding). -/
def vsCand (p : Bytes) : Option (Bytes × PublicKey × Nat) :=
  match (do
      let (_, b) ← pU8 "" p
      let (a, b) ← pBytes "" b
      let (k, b) ← pPublicKey "" b
      let (s, _) ← pU128 "" b
      pure (a, k, s) : Except String (Bytes × PublicKey × Nat)) with
  | .ok x => some x
  | .error _ => none

/-- A raw `ValidatorStake::V1` encoding that `pValidatorStake` re-parses exactly. -/
def vsWf (p : Bytes) : Bool :=
  match vsCand p with
  | some (a, k, s) => p == encVS a k s && AccountId.valid a && pkWf3 k && decide (s < Params.two128)
  | none => false

def encTS (a : Bytes) (l r : Nat) : Bytes := borshBytes a ++ u64 l ++ u64 r

def tsCand (p : Bytes) : Option (Bytes × Nat × Nat) :=
  match (do
      let (a, b) ← pBytes "" p
      let (l, b) ← pU64 "" b
      let (r, _) ← pU64 "" b
      pure (a, l, r) : Except String (Bytes × Nat × Nat)) with
  | .ok x => some x
  | .error _ => none

/-- A raw `TrieSplit` encoding that `pTrieSplit` re-parses exactly. -/
def tsWf (p : Bytes) : Bool :=
  match tsCand p with
  | some (a, l, r) => p == encTS a l r && AccountId.valid a &&
      decide (l < 18446744073709551616) && decide (r < 18446744073709551616)
  | none => false

def transitionWf (t : Transition) : Bool :=
  h32 t.blockHash && decide (t.values.length < 4294967296) &&
  t.values.all (fun v => decide (v.length < 4294967296)) && h32 t.postStateRoot

/-- D0 receipt shape: what `pReceipt` accepts. -/
def receiptWfD0 (r : Receipt) : Bool := r.wf && AccountId.isNamed r.receiverId

def pathWf (p : Bytes × Nat) : Bool := h32 p.1 && decide (p.2 ≤ 1)

def entryWf (e : ProofEntry) : Bool :=
  h32 e.key && decide (e.receipts.length < 4294967296) && e.receipts.all receiptWfD0 &&
  decide (e.proof.fromShard < 18446744073709551616) &&
  decide (e.proof.toShard < 18446744073709551616) &&
  decide (e.proof.path.length < 4294967296) && e.proof.path.all pathWf

def congestionWf (c : Congestion) : Bool :=
  decide (c.delayedGas < Params.two128) && decide (c.bufferedGas < Params.two128) &&
  decide (c.receiptBytes < 18446744073709551616) && decide (c.allowedShard < 65536)

def bwRequestWf (q : BwRequest) : Bool := decide (q.toShard < 65536) && q.bitmap.length == 5

def innerWf (ci : ChunkInner) : Bool :=
  (ci.tag == 3 || ci.tag == 4) && (ci.tag == 4 || ci.proposedSplit.isNone) &&
  h32 ci.prevBlockHash && h32 ci.prevStateRoot && h32 ci.prevOutcomeRoot &&
  h32 ci.encodedMerkleRoot &&
  decide (ci.encodedLength < 18446744073709551616) &&
  decide (ci.heightCreated < 18446744073709551616) &&
  decide (ci.shardId < 18446744073709551616) &&
  decide (ci.prevGasUsed < 18446744073709551616) &&
  decide (ci.gasLimit < 18446744073709551616) &&
  decide (ci.prevBalanceBurnt < Params.two128) &&
  h32 ci.prevOutgoingReceiptsRoot && h32 ci.txRoot &&
  decide (ci.proposals.length < 4294967296) && ci.proposals.all vsWf &&
  congestionWf ci.congestion &&
  decide (ci.bwRequests.length < 4294967296) && ci.bwRequests.all bwRequestWf &&
  (match ci.proposedSplit with | some s => tsWf s | none => true)

/-- Executable D0 shape of a decoded state witness. -/
def D0Shape.wf (sw : StateWitness) : Bool :=
  h32 sw.epochId && sw.innerBytes == encodeChunkInner sw.inner && innerWf sw.inner &&
  transitionWf sw.main && decide (sw.entries.length < 4294967296) && sw.entries.all entryWf &&
  h32 sw.appliedReceiptsHash && sw.nTransactions == 0 &&
  decide (sw.implicit.length < 4294967296) && sw.implicit.all transitionWf &&
  sw.nNewTransactions == 0 && decide (lenT (encodeSW sw) ≤ MAX_WITNESS)

def D0Shape (sw : StateWitness) : Prop := D0Shape.wf sw = true

/-! ## Helper lemmas -/

theorem pTake_ok (n : Nat) (w : String) (b rest : Bytes) (hl : b.length = n) :
    pTake n w (b ++ rest) = .ok (b, rest) := by
  subst hl; exact lift_ok (takeT_append b rest)

theorem h32_len {b : Bytes} (h : h32 b = true) : b.length = 32 := by
  simpa [h32] using h

theorem pAccountId_ok (w : String) (a rest : Bytes) (h : AccountId.valid a = true) :
    pAccountId w (borshBytes a ++ rest) = .ok (a, rest) := by
  have hl : a.length < 4294967296 := by
    simp only [AccountId.valid, Bool.and_eq_true, decide_eq_true_eq] at h; omega
  simp only [pAccountId, pBytes_ok _ _ _ hl, bind, Except.bind, h, ↓reduceIte, pure, Except.pure]

theorem pPublicKey_ok (w : String) (k : PublicKey) (rest : Bytes) (h : pkWf3 k = true) :
    pPublicKey w (k.encode ++ rest) = .ok (k, rest) := by
  obtain ⟨t, d⟩ := k
  simp only [pkWf3, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  simp only [PublicKey.encode, List.append_assoc]
  rcases h with (⟨rfl, hd⟩ | ⟨rfl, hd⟩) | ⟨rfl, hd⟩ <;>
  simp only [pPublicKey, pU8_ok _ _ _ (by decide : (0:Nat) < 256),
    pU8_ok _ _ _ (by decide : (1:Nat) < 256), pU8_ok _ _ _ (by decide : (2:Nat) < 256),
    bind, Except.bind, pure, Except.pure, pTake_ok _ _ _ _ hd]

theorem pkWf3_of_wf (k : PublicKey) (h : k.wf = true) : pkWf3 k = true := by
  simp only [PublicKey.wf, Bool.or_eq_true] at h
  simp only [pkWf3, Bool.or_eq_true, h, true_or]

/-! ## Raw validator stakes and trie splits -/

theorem vsWf_spec {p : Bytes} (h : vsWf p = true) :
    ∃ a k s, p = encVS a k s ∧ AccountId.valid a = true ∧ pkWf3 k = true ∧ s < Params.two128 := by
  unfold vsWf at h
  split at h
  · rename_i a k s _
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨a, k, s, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · exact absurd h (by simp)

theorem pValidatorStake_ok (p rest : Bytes) (h : vsWf p = true) :
    pValidatorStake (p ++ rest) = .ok (p, rest) := by
  obtain ⟨a, k, s, rfl, ha, hk, hs⟩ := vsWf_spec h
  have e : encVS a k s ++ rest = u8 0 ++ (borshBytes a ++ (k.encode ++ (u128 s ++ rest))) := by
    simp only [encVS, List.append_assoc]
  rw [e]
  simp only [pValidatorStake, pU8_ok _ _ _ (by decide : (0:Nat) < 256), bind, Except.bind,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pAccountId_ok _ _ _ ha, pPublicKey_ok _ _ _ hk,
    pU128_ok _ _ _ hs, pure, Except.pure]
  rw [← e, consumed_app]

theorem tsWf_spec {p : Bytes} (h : tsWf p = true) :
    ∃ a l r, p = encTS a l r ∧ AccountId.valid a = true ∧ l < 18446744073709551616 ∧
      r < 18446744073709551616 := by
  unfold tsWf at h
  split at h
  · rename_i a l r _
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨a, l, r, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · exact absurd h (by simp)

theorem pTrieSplit_ok (p rest : Bytes) (h : tsWf p = true) :
    pTrieSplit (p ++ rest) = .ok (p, rest) := by
  obtain ⟨a, l, r, rfl, ha, hl, hr⟩ := tsWf_spec h
  have e : encTS a l r ++ rest = borshBytes a ++ (u64 l ++ (u64 r ++ rest)) := by
    simp only [encTS, List.append_assoc]
  rw [e]
  simp only [pTrieSplit, pAccountId_ok _ _ _ ha, bind, Except.bind, pU64_ok _ _ _ hl,
    pU64_ok _ _ _ hr, pure, Except.pure]
  rw [← e, consumed_app]

/-! ## Component round trips -/

theorem pReceipt_encode (r : Receipt) (h : receiptWfD0 r = true) (rest : Bytes) :
    pReceipt (r.encode ++ rest) = .ok (r, rest) := by
  obtain ⟨pred, recv, rid, signer, pk, gp, dep⟩ := r
  simp only [receiptWfD0, Receipt.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have hk : pk.tag ≠ 2 := by
    simp only [PublicKey.wf, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h4; omega
  have e0 : ([0] : Bytes) = u8 0 := rfl
  have e3 : ([3] : Bytes) = u8 3 := rfl
  simp only [Receipt.encode, e0, e3, List.append_assoc]
  simp only [pReceipt, pAccountId_ok _ _ _ h1, bind, Except.bind, pAccountId_ok _ _ _ h2,
    pHash_ok _ _ _ h5, pU8_ok _ _ _ (by decide : (0:Nat) < 256), bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, pAccountId_ok _ _ _ h3, pPublicKey_ok _ _ _ (pkWf3_of_wf _ h4),
    pU128_ok _ _ _ h6, pU32_ok _ _ _ (by decide : (0:Nat) < 4294967296),
    pU32_ok _ _ _ (by decide : (1:Nat) < 4294967296),
    pU8_ok _ _ _ (by decide : (3:Nat) < 256), pU128_ok _ _ _ h7, h8, Bool.not_true,
    beq_iff_eq, hk, ↓reduceIte, pure, Except.pure]

theorem pTransition_encode (t : Transition) (h : transitionWf t = true) (rest : Bytes) :
    pTransition (encodeTransition t ++ rest) = .ok (t, rest) := by
  simp only [transitionWf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp only [pTransition, encodeTransition, encTr, List.append_assoc, pHash_ok _ _ _ (h32_len h1),
    bind, Except.bind, pU8_ok _ _ _ (by decide : (0:Nat) < 256), bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte,
    pVec_ok _ _ borshBytes _ _ h2 (fun v hv r => pBytes_ok _ v r (h3 v hv)),
    pHash_ok _ _ _ (h32_len h4), pure, Except.pure]

theorem pPathItem_encode (p : Bytes × Nat) (h : pathWf p = true) (rest : Bytes) :
    pPathItem (encodePathItem p ++ rest) = .ok (p, rest) := by
  obtain ⟨hh, d⟩ := p
  simp only [pathWf, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hn : ¬ d > 1 := by omega
  simp only [pPathItem, encodePathItem, List.append_assoc, pHash_ok _ _ _ (h32_len h1), bind,
    Except.bind, pU8_ok _ _ _ (by omega : d < 256), hn, ↓reduceIte, pure, Except.pure]

theorem pEntry_encode (e : ProofEntry) (h : entryWf e = true) (rest : Bytes) :
    pEntry (encodeEntry e ++ rest) = .ok (e, rest) := by
  obtain ⟨k, rs, ⟨f, t, path⟩⟩ := e
  simp only [entryWf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  simp only [pEntry, encodeEntry, List.append_assoc, pHash_ok _ _ _ (h32_len h1), bind,
    Except.bind, pVec_ok _ _ Receipt.encode _ _ h2 (fun x hx r => pReceipt_encode x (h3 x hx) r),
    pU64_ok _ _ _ h4, pU64_ok _ _ _ h5,
    pVec_ok _ _ encodePathItem _ _ h6 (fun x hx r => pPathItem_encode x (h7 x hx) r),
    pure, Except.pure]

theorem pCongestion_encode (c : Congestion) (h : congestionWf c = true) (rest : Bytes) :
    pCongestion (encodeCongestion c ++ rest) = .ok (c, rest) := by
  obtain ⟨d, b, r, a⟩ := c
  simp only [congestionWf, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp only [pCongestion, encodeCongestion, List.append_assoc,
    pU8_ok _ _ _ (by decide : (0:Nat) < 256), bind, Except.bind, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, pU128_ok _ _ _ h1, pU128_ok _ _ _ h2, pU64_ok _ _ _ h3,
    pU16_ok _ _ _ h4, pure, Except.pure]

theorem pBwRequest_encode (q : BwRequest) (h : bwRequestWf q = true) (rest : Bytes) :
    pBwRequest (encodeBwRequest q ++ rest) = .ok (q, rest) := by
  obtain ⟨s, m⟩ := q
  simp only [bwRequestWf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simp only [pBwRequest, encodeBwRequest, List.append_assoc, pU16_ok _ _ _ h.1, bind,
    Except.bind, pTake_ok _ _ _ _ h.2, pure, Except.pure]

theorem pBwRequests_encode (l : List BwRequest) (hn : l.length < 4294967296)
    (h : ∀ q ∈ l, bwRequestWf q = true) (rest : Bytes) :
    pBwRequests (encodeBwRequests l ++ rest) = .ok (l, rest) := by
  simp only [pBwRequests, encodeBwRequests, List.append_assoc,
    pU8_ok _ _ _ (by decide : (0:Nat) < 256), bind, Except.bind, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte,
    pVec_ok _ _ encodeBwRequest _ _ hn (fun x hx r => pBwRequest_encode x (h x hx) r)]

theorem pChunkInner_encode (ci : ChunkInner) (h : innerWf ci = true) (rest : Bytes) :
    pChunkInner (encodeChunkInner ci ++ rest) = .ok (ci, rest) := by
  obtain ⟨tag, pbh, psr, por, emr, el, hc, sid, pgu, gl, pbb, porr, txr, props, cong, bw, split⟩ := ci
  simp only [innerWf, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨htag, hsp⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩,
    h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩ := h
  have htag' : ¬ ((tag != 3 && tag != 4) = true) := by
    rcases htag with rfl | rfl <;> decide
  simp only [encodeChunkInner, List.append_assoc]
  simp only [pChunkInner, pU8_ok _ _ _ (by omega : tag < 256), bind, Except.bind, htag', ↓reduceIte,
    Bool.false_eq_true,
    pHash_ok _ _ _ (h32_len h1), pHash_ok _ _ _ (h32_len h2), pHash_ok _ _ _ (h32_len h3),
    pHash_ok _ _ _ (h32_len h4), pU64_ok _ _ _ h5, pU64_ok _ _ _ h6, pU64_ok _ _ _ h7,
    pU64_ok _ _ _ h8, pU64_ok _ _ _ h9, pU128_ok _ _ _ h10, pHash_ok _ _ _ (h32_len h11),
    pHash_ok _ _ _ (h32_len h12),
    pVec_ok _ _ (fun b => b) _ _ h13 (fun x hx r => pValidatorStake_ok x r (h14 x hx)),
    pCongestion_encode _ h15, pBwRequests_encode _ h16 h17, pure, Except.pure]
  rcases htag with rfl | rfl
  · have hs : split = none := by simpa using hsp
    subst hs; rfl
  · have ho := pOption_ok "proposed_split" pTrieSplit (fun b => b) split rest (fun s hs r' => by
      rw [hs] at h18; exact pTrieSplit_ok s r' h18)
    simp only [beq_self_eq_true, ↓reduceIte, ho]

theorem pChunkHeader_encode (ci : ChunkInner) (h : innerWf ci = true) (rest : Bytes) :
    pChunkHeader (u8 2 ++ encodeChunkInner ci ++ zeros8 ++ sig0 ++ rest) =
      .ok ((encodeChunkInner ci, ci), rest) := by
  simp only [List.append_assoc]
  simp only [pChunkHeader, pU8_ok _ _ _ (by decide : (2:Nat) < 256), bind, Except.bind,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pChunkInner_encode _ h,
    consumed_app, pU64_zeros8,
    pSignature_sig0, pure, Except.pure]

/-! ## The round trip -/

def EncodeWitnessStmt : Prop :=
  ∀ sw, D0Shape sw →
    decodeWitnessFile (encodeWitnessFile sw) = .ok (encodeSW sw, []) ∧
    decodeStateWitness (encodeSW sw) = .ok sw

theorem decodeStateWitness_encode (sw : StateWitness) (h : D0Shape sw) :
    decodeStateWitness (encodeSW sw) = .ok sw := by
  have hsize : ¬ lenT (encodeSW sw) > MAX_WITNESS := by
    have := h
    simp only [D0Shape, D0Shape.wf, Bool.and_eq_true, decide_eq_true_eq] at this
    exact Nat.not_lt.mpr this.2
  obtain ⟨eid, ib, ci, main, entries, arh, ntx, impl, nnew⟩ := sw
  simp only [D0Shape, D0Shape.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, -⟩ := h
  subst h2 h8 h11
  rw [decodeStateWitness]
  simp only [hsize, ↓reduceIte]
  simp only [encodeSW, List.append_assoc]
  have hch := pChunkHeader_encode ci h3
    (encodeTransition main ++ (encList encodeEntry entries ++ (arh ++ (u32 0 ++
      (encList encodeTransition impl ++ u32 0)))))
  simp only [List.append_assoc] at hch
  simp only [pU8_ok _ _ _ (by decide : (1:Nat) < 256), bind, Except.bind, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, pHash_ok _ _ _ (h32_len h1), hch,
    pTransition_encode _ h4,
    pVec_ok _ _ encodeEntry _ _ h5 (fun x hx r => pEntry_encode x (h6 x hx) r),
    pHash_ok _ _ _ (h32_len h7), pU32_ok _ _ _ (by decide : (0:Nat) < 4294967296),
    pVec_ok _ _ encodeTransition _ _ h9 (fun x hx r => pTransition_encode x (h10 x hx) r)]
  rfl

theorem decodeWitnessFile_encode (sw : StateWitness) (h : D0Shape sw) :
    decodeWitnessFile (encodeWitnessFile sw) = .ok (encodeSW sw, []) := by
  have hl : (encodeSW sw).length < 4294967296 := by
    simp only [D0Shape, D0Shape.wf, Bool.and_eq_true, decide_eq_true_eq, lenT_eq'] at h
    have := h.2; simp only [MAX_WITNESS] at this; omega
  simp only [decodeWitnessFile, encodeWitnessFile, List.append_assoc]
  rw [dTag_ok _ _ _ (by decide)]
  simp only [bind, Except.bind, pBytes_ok _ _ _ hl]
  have hv : pVec "contract_code" (pBytes "code") (u32 0 ++ []) =
      (.ok ([], []) : Except String (List Bytes × Bytes)) := by
    simp only [pVec, pU32_ok _ _ _ (by decide : (0:Nat) < 4294967296), bind, Except.bind, pMany]
  rw [List.append_nil] at hv
  simp only [hv]
  rfl

theorem encodeWitness_roundtrip : EncodeWitnessStmt := fun sw h =>
  ⟨decodeWitnessFile_encode sw h, decodeStateWitness_encode sw h⟩

/-! ## The reference candidate's normal form (`ReexecV3D0.normSW` / `normalW`)

`encodeSW` writes the header fields `normSW` fixes (`zeros8`, `sig0`) and transitions with
the reference's own `encTr`, so for a witness already in normal form (`normW K R s = s`:
zero transition block hashes, entries deduplicated and key-sorted, normal trie values)
its bytes are a fixed point of the byte normaliser. -/

theorem pTransition_encTr (t : Transition) (h : transitionWf t = true) (rest : Bytes) :
    pTransition (encTr t ++ rest) = .ok (t, rest) := pTransition_encode t h rest

/-- The receipt-proof entries of `encodeSW` as byte segments. -/
theorem segs_encodeEntry (es : List ProofEntry) (hw : ∀ e ∈ es, entryWf e = true) (x : Bytes) :
    segs pEntry es.length (concatAll (es.map encodeEntry) ++ x) =
      .ok (es.map (fun e => (e, encodeEntry e)), x) := by
  have h := segs_concat (p := pEntry) (es.map fun e => (e, encodeEntry e)) x (by
    intro q hq x'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
    exact pEntry_encode e (hw e he) x')
  have hm : (es.map fun e => (e, encodeEntry e)).map Prod.snd = es.map encodeEntry := by
    simp only [List.map_map]; rfl
  rw [hm, List.length_map] at h
  exact h

/-- Normal-form pairs of segments produced from an entry list in normal form. -/
theorem normPairs_encodeEntry (es : List ProofEntry) (hn : normEntries es = es) :
    u32 (normPairs (es.map fun e => (e, encodeEntry e))).length ++
      concatAll ((normPairs (es.map fun e => (e, encodeEntry e))).map Prod.snd) =
    encList encodeEntry es := by
  have hf : (normPairs (es.map fun e => (e, encodeEntry e))).map Prod.fst = es := by
    rw [normPairs_map]
    have : (es.map fun e => (e, encodeEntry e)).map Prod.fst = es := by
      simp only [List.map_map]; exact List.map_id' es
    rw [this, hn]
  have hs : (normPairs (es.map fun e => (e, encodeEntry e))).map Prod.snd =
      ((normPairs (es.map fun e => (e, encodeEntry e))).map Prod.fst).map encodeEntry := by
    apply segs_enc
    intro q hq
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp (mem_normPairs hq)
    rfl
  have hl : (normPairs (es.map fun e => (e, encodeEntry e))).length = es.length := by
    rw [← List.length_map (f := Prod.fst), hf]
  rw [hs, hf, hl]
  rfl

theorem normSW_encodeSW (K : List (List Nat)) (R : Bytes) (sw : StateWitness) (h : D0Shape sw)
    (hn : normW K R sw = sw) : normSW K R (encodeSW sw) = .ok (encodeSW sw) := by
  have hE : normEntries sw.entries = sw.entries := congrArg StateWitness.entries hn
  have hM : normMain K R sw.main = sw.main := congrArg StateWitness.main hn
  have hI : normImpl sw.main.postStateRoot sw.implicit = sw.implicit :=
    congrArg StateWitness.implicit hn
  obtain ⟨eid, ib, ci, main, entries, arh, ntx, impl, nnew⟩ := sw
  simp only [D0Shape, D0Shape.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, -⟩ := h
  subst h2 h8 h11
  dsimp only at hE hM hI
  have hsw : encodeSW ⟨eid, encodeChunkInner ci, ci, main, entries, arh, 0, impl, 0⟩ =
      (u8 1 ++ (eid ++ (u8 2 ++ encodeChunkInner ci))) ++ (zeros8 ++ (sig0 ++ (encTr main ++
      (u32 entries.length ++ (concatAll (entries.map encodeEntry) ++ ((arh ++ u32 0) ++
      (encList encTr impl ++ u32 0))))))) := by
    simp only [encodeSW, encodeTransition, encList, List.append_assoc]
    rfl
  rw [hsw]
  unfold normSW
  simp only [List.append_assoc, pU8_ok _ _ _ (by decide : (1:Nat) < 256), bind, Except.bind,
    pHash_ok _ _ _ (h32_len h1), pU8_ok _ _ _ (by decide : (2:Nat) < 256), pChunkInner_encode _ h3,
    pU64_zeros8, pSignature_sig0, pTransition_encTr _ h4, pU32_ok _ _ _ h5,
    segs_encodeEntry _ h6, pHash_ok _ _ _ (h32_len h7), pU32_ok _ _ _ (by decide : (0:Nat) < 4294967296),
    pVec_ok _ _ encTr _ _ h9 (fun x hx r => pTransition_encTr x (h10 x hx) r), pure, Except.pure]
  have c1 : ∀ y, consumed (u8 1 ++ (eid ++ (u8 2 ++ (encodeChunkInner ci ++ y)))) y =
      u8 1 ++ (eid ++ (u8 2 ++ encodeChunkInner ci)) := fun y => by
    rw [show u8 1 ++ (eid ++ (u8 2 ++ (encodeChunkInner ci ++ y))) =
      (u8 1 ++ (eid ++ (u8 2 ++ encodeChunkInner ci))) ++ y by simp only [List.append_assoc],
      consumed_app]
  have c2 : ∀ y, consumed (arh ++ (u32 0 ++ y)) y = arh ++ u32 0 := fun y => by
    rw [show arh ++ (u32 0 ++ y) = (arh ++ u32 0) ++ y by simp only [List.append_assoc], consumed_app]
  rw [c1, c2, hM, hI, ← List.append_assoc (u32 _), normPairs_encodeEntry _ hE]
  simp only [encList, List.append_assoc]

/-- The encoder meets the reference's normal form: on a D0-shaped witness that is a fixed
point of `normW K R`, `encodeSW` decodes back and is a fixed point of `normSW K R`. -/
def EncodeWitnessNormalStmt : Prop :=
  ∀ (K : List (List Nat)) (R : Bytes) (s : StateWitness), D0Shape s → normW K R s = s →
    decodeStateWitness (encodeSW s) = .ok s ∧ normSW K R (encodeSW s) = .ok (encodeSW s)

theorem encodeWitness_normal : EncodeWitnessNormalStmt := fun K R s h hn =>
  ⟨decodeStateWitness_encode s h, normSW_encodeSW K R s h hn⟩

/-- File level: if the reference's `keysD0` computes `(K, R)` on the encoded file, the file
is accepted by `normalW`. (`keysD0` reads the file only through its decoded witness and the
claim; the hypothesis is the one `normalW` itself evaluates.) -/
theorem normalW_encodeWitnessFile (cb : Bytes) (K : List (List Nat)) (R : Bytes) (s : StateWitness)
    (h : D0Shape s) (hn : normW K R s = s) (hk : keysD0 cb (encodeWitnessFile s) = .ok (K, R)) :
    normalW cb (encodeWitnessFile s) = true := by
  unfold normalW
  rw [decodeWitnessFile_encode s h]
  dsimp only
  rw [hk]
  dsimp only
  rw [normSW_encodeSW K R s h hn]
  simp

end ZkFormal.V3
