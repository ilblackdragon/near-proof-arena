import ZkFormal.NearV3.Candidates.NativeSourcePackedAllocation
import ZkFormal.NearV3.Candidates.NativeSourceShaTraffic

namespace ZkFormal.NearV3.Candidates.NativeSourceByteBalance
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Assembly Render Rcpt.Candidates

/-- Actual native and original source senders discharge their entire portion
of the packed SHA byte inventory, preserving multiplicities. -/
theorem producers {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (hc : checkD0a B0 cb wb=.ok ()) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (ns : List NodeS3) (vs : List ValE) (hn : NodeOk ns) (hv : ValWf vs)
    (scheduler receipt : List Sha.Gen.Msg) (consumed tn tv : Nat) (pub : List Fp) (msg : List Fp)
    (hcount : consumed=((Sha.Gen.expectedBytes
      (scheduler++jobsToSha (nativeShaJobs ns vs)++receipt++sourceShaMessages p.lists w.entries)).map Msg.toFp).count msg) :
    consumed=
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_BYTES true msg+
      tableBusCount SizeCount.valTable.interactions (TrieCountHeight.value vs pub) tv pub B_BYTES true msg+
      SourceLog22.boundaryCount (NativeSourceFour.trace (DedupCompile.blocks p.lists w.entries)
        (sourceRepeated p.lists)) 0 1 2 3 pub B_BYTES true msg+
      ((Sha.Gen.expectedBytes (scheduler++receipt)).map Msg.toFp).count msg := by
  rw [NativePostShaTraffic.bytes ns vs hn hv tn tv pub msg,
    NativeSourceShaTraffic.bytes hc hp hf hw pub msg,hcount]
  simp only [Sha.Gen.expectedBytes,List.flatMap_append,List.map_append,List.count_append]
  omega

end ZkFormal.NearV3.Candidates.NativeSourceByteBalance
