import FinalM5d.Decode
import FinalM5d.HeaderLink
import NearSpecV3.E2E.View
import NearSpec.ClaimCodec
import NearSpecV3.Logged.TrieHash

/-!
# FinalM5d.BOut — the `done` boundary's component commitments (lane G's proposal)

Lane E's view (`NearSpecV3.E2E.Bnd.ViewImpl`) commits `done H o` (phase 4) through
`ctxD (.header H)` (the `ctxRoot` field) and `outD (.done o)` (the four accumulator fields); the
other components of `done` are `stD .none`, `vmD []`, `wasmD none` (lanes B / A constants). The
FINAL template computes the two M5d components in-circuit (`Fin` messages `ID_HDR`, `ID_OUT` on
`S384`) and exposes them as public values; the FINAL leaf (lane D) assembles `h(B_out)` from them,
`claimDigest` and the view's constants.

* `ctxHeaderD H = bdigest (0x04 ‖ encCIF1 H)`: `encCIF1` is the class-F1 (V5, no proposals /
  bandwidth requests / split) chunk-inner encoding — the same bytes `decodeChunkInner` reads
  (`encCIF1_hdrF1`: on `hdrF1` of 8/16/32-byte slices it is `encF1` of the slices, and
  `Decode.decode_F1` decodes that back to `hdrF1`), i.e. the statement's own window;
* `outDoneD o = (bdigest (0x05 ‖ encOutputsF1 o), [], bdigest [], bdigest [])`: `encOutputsF1`
  is the fixed 252-byte layout of `Outputs` for class F1.

These are **[S] encodings** (no lane fixes them yet); the domain tags `0x04` / `0x05` keep them
apart from the other `bdigest` messages (`0x00` the intake context, `0x46` `FinIn`).
-/

namespace FinalM5d.BOut

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E FinalM5d FinalM5d.Decode

/-- Class-F1 chunk-inner bytes (`pChunkInner`'s V5 layout with empty proposals, bandwidth
requests and split). -/
def encCIF1 (H : ChunkInner) : Bytes :=
  encF1 H.prevBlockHash H.prevStateRoot H.prevOutcomeRoot H.encodedMerkleRoot (u64 H.encodedLength)
    (u64 H.heightCreated) (u64 H.shardId) (u64 H.prevGasUsed) (u64 H.gasLimit)
    (u128 H.prevBalanceBurnt) H.prevOutgoingReceiptsRoot H.txRoot
    (u128 H.congestion.delayedGas) (u128 H.congestion.bufferedGas)
    (u64 H.congestion.receiptBytes) (u16 H.congestion.allowedShard)

/-- **`ctxD (.header H)`** (proposal). -/
def ctxHeaderD (H : ChunkInner) : Bytes := Bnd.bdigest (4 :: encCIF1 H)

/-- Class-F1 `Outputs` bytes (252 B): state root, outcome root, `u64` gas limit, `u64` gas used,
`u128` balance burnt, outgoing root, congestion `0 ‖ u128 ‖ u128 ‖ u64 ‖ u16`, tx root,
encoded merkle root, `u64` encoded length, `u32` proposals count, `u32` bandwidth-requests count,
split tag. -/
def encOutputsF1 (o : Outputs) : Bytes :=
  o.stateRoot ++ o.outcomeRoot ++ u64 o.gasLimit ++ u64 o.gasUsed ++ u128 o.balanceBurnt ++
  o.outgoingRoot ++ [0] ++ u128 o.congestion.delayedGas ++
  u128 o.congestion.bufferedGas ++ u64 o.congestion.receiptBytes ++
  u16 o.congestion.allowedShard ++ o.txRoot ++ o.encodedMerkleRoot ++ u64 o.encodedLength ++
  u32 o.proposals.length ++ u32 o.bwRequests.length ++ [if o.proposedSplit.isSome then 1 else 0]

/-- **`outD (.done o)`** (proposal). -/
def outDoneD (o : Outputs) : Bytes × List Bytes × Bytes × Bytes :=
  (Bnd.bdigest (5 :: encOutputsF1 o), [], Bnd.bdigest [], Bnd.bdigest [])

theorem encOutputsF1_length (o : Outputs) (h1 : o.stateRoot.length = 32)
    (h2 : o.outcomeRoot.length = 32) (h3 : o.outgoingRoot.length = 32) (h4 : o.txRoot.length = 32)
    (h5 : o.encodedMerkleRoot.length = 32) : (encOutputsF1 o).length = 252 := by
  simp [encOutputsF1, h1, h2, h3, h4, h5, u16, u32, u64, u128, leN_length]

/-- On the decoded class-F1 header (`Decode.hdrF1` of slices of the right lengths), `encCIF1` is
the original window: the header commitment is `bdigest (0x04 ‖ window)`. -/
theorem encCIF1_hdrF1 (pbh psr por emr el hc sid gu gl bb orr txr cd cb cr ca : Bytes)
    (h5 : el.length = 8) (h6 : hc.length = 8) (h7 : sid.length = 8) (h8 : gu.length = 8)
    (h9 : gl.length = 8) (h10 : bb.length = 16) (h13 : cd.length = 16) (h14 : cb.length = 16)
    (h15 : cr.length = 8) (h16 : ca.length = 2) :
    encCIF1 (hdrF1 pbh psr por emr el hc sid gu gl bb orr txr cd cb cr ca) =
      encF1 pbh psr por emr el hc sid gu gl bb orr txr cd cb cr ca := by
  simp only [encCIF1, hdrF1, u64, u128, u16,
    Logged.leN_leNat' 8 _ h5, Logged.leN_leNat' 8 _ h6, Logged.leN_leNat' 8 _ h7,
    Logged.leN_leNat' 8 _ h8, Logged.leN_leNat' 8 _ h9, Logged.leN_leNat' 16 _ h10,
    Logged.leN_leNat' 16 _ h13, Logged.leN_leNat' 16 _ h14, Logged.leN_leNat' 8 _ h15,
    Logged.leN_leNat' 2 _ h16]

end FinalM5d.BOut
