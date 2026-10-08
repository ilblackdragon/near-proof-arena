import ZkFormal.NearV3.Assembly.RcptSourceRcDigest

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Near Rcpt.Candidates Render.SrcpGen

/-- All RC preimages are hashed, but duplicate source occurrences have no
DIGEST consumer and therefore request no SHA digest output. -/
def sourceRcShaJobs (own : Nat) (sources : List SrcList) (entries : List ProofEntry) : List Sha.Gen.Msg :=
  (List.range sources.length).map fun j =>
    ⟨msgId K_RC j,(u64 own++encodeReceipts (DedupCompile.entryAt sources entries j).receipts).map UInt8.toNat,
      !(Public.sourceDup sources j)⟩

/-- Duplicate digest gating does not remove any receipt preimage byte. -/
theorem source_rc_bytes_unchanged (own : Nat) (sources : List SrcList) (entries : List ProofEntry) :
    Sha.Gen.expectedBytes (sourceRcShaJobs own sources entries)=
      Sha.Gen.expectedBytes ((sourceRcShaJobs own sources entries).map (fun m=>{m with dmult:=true})) := by
  simp only [Sha.Gen.expectedBytes,List.flatMap_map]

/-- Exact source RC digest conservation, including duplicate suppression. The
preimages of suppressed outputs remain present in the SHA job inventory. -/
theorem source_rc_digest_outputs {budget : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    {k : WalkD0} {w : StateWitness}
    (ha : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) :
    Sha.Gen.expectedDigests (sourceRcShaJobs k.H.shardId p.lists w.entries)=
      ((DedupCompile.blocks p.lists w.entries).filter (fun B=>!B.dup)).map
        (fun B=>digMsg (msgId K_RC B.j) B.L B.leaf) := by
  simp only [Sha.Gen.expectedDigests,sourceRcShaJobs,DedupCompile.blocks,List.filter_map,List.map_map]
  change (((List.range p.lists.length).filter (fun j=>!(Public.sourceDup p.lists j))).map
    (fun j=>Render.digestMsg ⟨msgId K_RC j,
      (u64 k.H.shardId++encodeReceipts (DedupCompile.entryAt p.lists w.entries j).receipts).map UInt8.toNat⟩))=_
  apply List.map_congr_left
  intro j hj
  have hbound : j<p.lists.length := List.mem_range.mp (List.mem_filter.mp hj).1
  exact (source_block_rc_digest ha hp hk hw j hbound).symm

end ZkFormal.NearV3.Assembly.RcptSkeleton
