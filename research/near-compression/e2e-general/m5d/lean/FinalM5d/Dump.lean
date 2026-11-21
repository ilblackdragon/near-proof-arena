import Lean.Data.Json
import NearSpecV3.E2E.Statement

/-!
# FinalM5d.Dump — the checker's own FINAL on a corpus case, for the trace generator

`m5d-tool dump CASE OUT.json` runs lane E's chunk machine `CM` (`NearSpecV3.E2E.CM.step`, the
`allFeatures` checker sliced, `cm_iff`) from `init claim witness` to the main transition's end
`fin I out`, then the checker's `FINAL` code verbatim: `finK` (post-state root, implicit
transitions, outgoing reassignment) with the continuation capturing `t = (root, congestion,
outgoing)`, and `tailNew` (the computed header outputs `o`), and `headerOk I.H o`.

It writes everything the M5d FINAL / INIT trace generator needs (hex byte strings):
* the public statement pieces: `pre` (the claim encoding's public prefix up to and including
  `borsh(chunk_inner)`), `blocks` (the private section B encoding), `post` (the public suffix);
  `pre ‖ blocks ‖ post = claim` is checked here; the witness bytes;
* the `FinIn` record (M5d leaf spec §2): root, congestion, gas, balance, gas limit, proposed split,
  the outcome leaves, the outgoing receipts with their routed shard, the transactions, the layout's
  shard ids;
* the computed outputs `o` and the header `H`, and **self-checks**: every output recomputed here
  from `FinIn` the way the AIR does it (Merkle roots, per-shard receipt hashes, Reed–Solomon parts)
  equals the checker's `o`.
-/

namespace FinalM5d.Dump

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.Successor

def hexOf (bs : List UInt8) : String :=
  let d := fun (n : Nat) => if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList (bs.flatMap fun b => [d (b.toNat / 16), d (b.toNat % 16)])

def hx (b : List UInt8) : Lean.Json := .str (hexOf b)
def num (n : Nat) : Lean.Json := .str (toString n)

/-- Run `CM` until the main transition's end (fuel-bounded). -/
def runToFin : Nat → Conf → Except String (Intake × MainOutD2)
  | 0, _ => .error "fuel"
  | n + 1, c => match c with
    | .fin I out => .ok (I, out)
    | .done .. | .doneG | .gfin _ => .error "no fin configuration (genesis path)"
    | c => do let c' ← CM.step c; runToFin n c'

/-- The public prefix of `Claim.encode` (everything before the blocks). -/
def claimPre (c : Claim) : Bytes :=
  borshBytes claimTag ++ borshBytes statementIdV3 ++ u32 c.protocolVersion ++
  borshBytes c.chainId ++ c.epochId ++ borshBytes c.chunkInner

/-- The public suffix of `Claim.encode` (everything after the blocks). -/
def claimPost (c : Claim) : Bytes :=
  u16 c.rsDataParts ++ u16 c.rsTotalParts ++
  encList EpochRec.encode c.epochs ++ borshBytes c.epochStartAfter ++
  encList ApplyFacts.encode c.applyFacts ++ borshBytes c.txValid ++
  encOpt borshBytes c.genesisChunkExtra

def congEnc (c : Congestion) : Bytes :=
  [0] ++ u128 c.delayedGas ++ u128 c.bufferedGas ++ u64 c.receiptBytes ++ u16 c.allowedShard

def dump (dir : String) (cb wb : Bytes) : Except String Lean.Json := do
  let (I, out) ← runToFin 100000000 (.init cb wb)
  if I.d2.isSome then throw "genesis-segment path (d2): not the M5d T1 shape"
  let t ← finK afDriver afCfg.gasCap I out (fun t => pure t)
  let (root, congestion, outgoing) := t
  let o ← tailNew afDriver I out t
  let c := I.c
  let pre := claimPre c
  let blocks := encList BlockRec.encode c.blocks
  let post := claimPost c
  let leaves := out.outcomes.map OutD1.leaf
  let shards := I.L.shardIds
  let rshard := fun (r : Rcpt) => r.routedShard I.L
  let txs := I.w.newTxs.map TxD2.raw
  let body := u32 txs.length ++ concatAll txs ++ encodeRcpts outgoing
  -- recomputation the way the AIR does it
  let shardMsg := fun s => u64 s ++ encodeRcpts (outgoing.filter fun r => rshard r == s)
  let outRoot := merkleRoot (shards.map fun s => sha256 (sha256 (shardMsg s)))
  let rs ← match RSCode.new c.rsDataParts c.rsTotalParts with
    | some rs => pure rs | none => throw "rs params"
  let parts ← match rs.encodeParts body with | some p => pure p | none => throw "rs parts"
  let mat ← match buildMatrix c.rsDataParts c.rsTotalParts with
    | some m => pure m | none => throw "rs matrix"
  let checks : List (String × Bool) :=
    [("claim = pre ++ blocks ++ post", cb == pre ++ blocks ++ post),
     ("headerOk", headerOk I.H o),
     ("decodeChunkInner public", match decodeChunkInner c.chunkInner with
        | .ok H => decide (H.prevStateRoot = I.H.prevStateRoot) | .error _ => false),
     ("stateRoot = root", o.stateRoot == root),
     ("outcomeRoot = merkleRoot leaves", o.outcomeRoot == merkleRoot leaves),
     ("outgoingRoot recomputed", o.outgoingRoot == outRoot),
     ("txRoot recomputed", o.txRoot == merkleRoot (txs.map sha256)),
     ("encoded root recomputed", o.encodedMerkleRoot == partsMerkleRoot parts),
     ("encoded length", o.encodedLength == body.length),
     ("parts = t", parts.length == c.rsTotalParts),
     ("gasUsed", o.gasUsed == out.gasUsed), ("balanceBurnt", o.balanceBurnt == out.balanceBurnt),
     ("gasLimit", o.gasLimit == I.slotB2.gasLimit),
     ("no reassignment", outgoing.length == out.outgoing.length)]
  let H := I.H
  pure <| Lean.Json.mkObj [
    ("case", .str dir),
    ("checks", Lean.Json.mkObj (checks.map fun (k, v) => (k, Lean.Json.bool v))),
    ("claim", hx cb), ("witness", hx wb),
    ("pre", hx pre), ("blocks", hx blocks), ("post", hx post),
    ("chunkInner", hx c.chunkInner),
    ("chunkInnerOffset", num (pre.length - c.chunkInner.length)),
    ("rsD", num c.rsDataParts), ("rsT", num c.rsTotalParts),
    ("matrix", Lean.Json.arr ((mat.map fun row => Lean.Json.arr (row.map num).toArray)).toArray),
    ("header", Lean.Json.mkObj [("tag", num H.tag), ("shardId", num H.shardId),
        ("heightCreated", num H.heightCreated), ("nProposals", num H.proposals.length),
        ("nBw", num H.bwRequests.length), ("split", Lean.Json.bool H.proposedSplit.isSome)]),
    ("finIn", Lean.Json.mkObj [
        ("root", hx root), ("congestion", hx (congEnc congestion)),
        ("gasUsed", num out.gasUsed), ("balanceBurnt", num out.balanceBurnt),
        ("gasLimit", num I.slotB2.gasLimit),
        ("proposed", hx (encOpt id I.proposed)),
        ("proposals", Lean.Json.arr ((out.proposals.map fun p => hx p.encode)).toArray),
        ("bwRequests", Lean.Json.arr ((out.bwRequests.map fun r =>
            hx (u16 r.toShard ++ r.bitmap))).toArray),
        ("outcomeLeaves", Lean.Json.arr (leaves.map hx).toArray),
        ("outgoing", Lean.Json.arr ((outgoing.map fun r => Lean.Json.mkObj
            [("shard", num (rshard r)), ("enc", hx r.encode)])).toArray),
        ("txs", Lean.Json.arr (txs.map hx).toArray),
        ("shardIds", Lean.Json.arr (shards.map num).toArray)]),
    ("body", hx body),
    ("parts", Lean.Json.arr (parts.map hx).toArray),
    ("outputs", Lean.Json.mkObj [
        ("stateRoot", hx o.stateRoot), ("outcomeRoot", hx o.outcomeRoot),
        ("outgoingRoot", hx o.outgoingRoot), ("txRoot", hx o.txRoot),
        ("encodedMerkleRoot", hx o.encodedMerkleRoot), ("encodedLength", num o.encodedLength),
        ("gasUsed", num o.gasUsed), ("gasLimit", num o.gasLimit),
        ("balanceBurnt", num o.balanceBurnt), ("congestion", hx (congEnc o.congestion))]),
    ("implicit", num I.w.implicit.length)]

end FinalM5d.Dump
