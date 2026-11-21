import NearSpecV3.E2E.Machine

/-!
# FinalM5d.Decode — the class-F1 chunk header layout decodes to its slices

`encF1` is the byte layout of a V5 `ShardChunkHeaderInner` with no proposals, a `CongestionInfo`
V1, no bandwidth requests and no proposed split (class `F1`, the FINAL template's pinned shape):
`[4] ‖ prev_block_hash ‖ prev_state_root ‖ prev_outcome_root ‖ encoded_merkle_root ‖ u64 ×5 ‖ u128 ‖
prev_outgoing_receipts_root ‖ tx_root ‖ u32 0 ‖ 0 ‖ u128 ‖ u128 ‖ u64 ‖ u16 ‖ 0 ‖ u32 0 ‖ 0`, with
every slice a raw byte string. `decode_F1`: the spec's own decoder `decodeChunkInner` returns the
header `hdrF1` whose fields are those slices (numbers as `leNat`).
-/

namespace FinalM5d.Decode

open NearSpec NearSpecV3

theorem takeN_app {n : Nat} {a : Bytes} (b : Bytes) (h : a.length = n) : takeN n (a ++ b) = some (a, b) := by
  subst h; exact NearSpec.takeN_append a b

theorem readLE_app {w : Nat} {a : Bytes} (b : Bytes) (h : a.length = w) :
    readLE w (a ++ b) = some (leNat a, b) := by
  simp only [readLE, takeN_app b h, Option.map_some]

theorem readLE1 (x : UInt8) (b : Bytes) : readLE 1 ([x] ++ b) = some (x.toNat, b) := by
  simp [readLE, takeN, leNat]

theorem readLE4z (b : Bytes) : readLE 4 ([0, 0, 0, 0] ++ b) = some (0, b) := by
  simp [readLE, takeN, leNat]

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem u4 : UInt8.toNat 4 = 4 := rfl
theorem u0 : UInt8.toNat 0 = 0 := rfl

theorem pMany_zero {α : Type} (p : NearSpecV3.P α) (bs : Bytes) : pMany p 0 bs = .ok ([], bs) := rfl

/-- The class-F1 layout. -/
def encF1 (pbh psr por emr el hc sid gu gl bb orr txr cd cb cr ca : Bytes) : Bytes :=
  [4] ++ pbh ++ psr ++ por ++ emr ++ el ++ hc ++ sid ++ gu ++ gl ++ bb ++ orr ++ txr ++
  [0, 0, 0, 0] ++ [0] ++ cd ++ cb ++ cr ++ ca ++ [0] ++ [0, 0, 0, 0] ++ [0]

/-- The decoded header. -/
def hdrF1 (pbh psr por emr el hc sid gu gl bb orr txr cd cb cr ca : Bytes) : ChunkInner :=
  { tag := 4, prevBlockHash := pbh, prevStateRoot := psr, prevOutcomeRoot := por,
    encodedMerkleRoot := emr, encodedLength := leNat el, heightCreated := leNat hc,
    shardId := leNat sid, prevGasUsed := leNat gu, gasLimit := leNat gl,
    prevBalanceBurnt := leNat bb, prevOutgoingReceiptsRoot := orr, txRoot := txr, proposals := [],
    congestion := ⟨leNat cd, leNat cb, leNat cr, leNat ca⟩, bwRequests := [], proposedSplit := none }

set_option maxHeartbeats 1000000 in
theorem decode_F1 (pbh psr por emr el hc sid gu gl bb orr txr cd cb cr ca : Bytes)
    (h1 : pbh.length = 32) (h2 : psr.length = 32) (h3 : por.length = 32) (h4 : emr.length = 32)
    (h5 : el.length = 8) (h6 : hc.length = 8) (h7 : sid.length = 8) (h8 : gu.length = 8)
    (h9 : gl.length = 8) (h10 : bb.length = 16) (h11 : orr.length = 32) (h12 : txr.length = 32)
    (h13 : cd.length = 16) (h14 : cb.length = 16) (h15 : cr.length = 8) (h16 : ca.length = 2) :
    decodeChunkInner (encF1 pbh psr por emr el hc sid gu gl bb orr txr cd cb cr ca) =
      .ok (hdrF1 pbh psr por emr el hc sid gu gl bb orr txr cd cb cr ca) := by
  unfold decodeChunkInner pChunkInner encF1
  simp only [List.append_assoc]
  simp only [pU8, pU16, pU32, pU64, pU128, pHash, lift, readU8, readU16, readU32, readU64, readU128,
    readHash, readLE1, readLE4z, ok_bind, takeN_app _ h1, takeN_app _ h2, takeN_app _ h3,
    takeN_app _ h4, takeN_app _ h11, takeN_app _ h12, readLE_app _ h5, readLE_app _ h6,
    readLE_app _ h7, readLE_app _ h8, readLE_app _ h9, readLE_app _ h10]
  simp only [pVec, pCongestion, pBwRequests, pOption, pU8, pU16, pU32, pU64, pU128, lift, readU8,
    readU16, readU32, readU64, readU128, readLE1, readLE4z, ok_bind, readLE_app _ h13,
    readLE_app _ h14, readLE_app _ h15, readLE_app _ h16, pMany_zero]
  simp only [u4, u0, pure_bind, ok_bind, readLE1, readLE4z, pMany_zero, List.append_nil]
  simp only [List.singleton_append, List.cons_append, List.nil_append, readLE, takeN, Option.map_some,
    leNat, u0, u4]
  simp only [Nat.reduceBNe, Nat.reduceBEq, Bool.and_false, Bool.and_true, Bool.false_eq_true,
    Bool.true_and, ↓reduceIte, ok_bind, pure_bind, readLE, takeN, Option.map_some, leNat, u0,
    Option.map, pMany_zero]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceBNe, Bool.false_eq_true, ↓reduceIte, ok_bind,
    pure_bind, takeN, leNat, u0, Option.map_some, pMany_zero, List.isEmpty_nil, Bool.not_true]
  rfl

end FinalM5d.Decode
