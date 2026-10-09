import ZkFormal.NearV3.Candidates.NativeSourceFour
import ZkFormal.NearV3.Candidates.AcceptedSourceShaContract
import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22BoundarySound

namespace ZkFormal.NearV3.Candidates.NativeSourceShaTraffic
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Assembly Rcpt.Candidates

/-- Exact byte send count of the accepted original four source partitions,
including overlap suppression and duplicate source occurrence semantics. -/
theorem bytes {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (hc : checkD0a B0 cb wb=.ok ()) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (pub : List Fp) (msg : List Fp) :
    let bs:=DedupCompile.blocks p.lists w.entries
    SourceLog22.boundaryCount (NativeSourceFour.trace bs (sourceRepeated p.lists)) 0 1 2 3 pub B_BYTES true msg=
      ((Sha.Gen.expectedBytes (sourceShaMessages p.lists w.entries)).map Msg.toFp).count msg := by
  have h:=(relD0a_iff B0 cb wb).mpr hc
  have hR:=DedupCompile.relD0a_row_bound h hp hf hw
  have hm:=SourceLog22.honest_four_counted_messages
    (DedupCompile.blocks p.lists w.entries) (sourceRepeated p.lists)
    (DedupCompile.relD0a_blocks_nonempty h hp w.entries)
    (tr:=NativeSourceFour.trace (DedupCompile.blocks p.lists w.entries) (sourceRepeated p.lists))
    (t0:=0) (t1:=1) (t2:=2) (t3:=3) (H:=2^22) (pub:=pub)
    (by intro t ht;rfl) (by omega) (DedupCompile.relD0a_block_widths h hp hf hw)
    (by intro r hr x;simp [NativeSourceFour.trace])
    (by intro r hr x;simp [NativeSourceFour.trace])
    (by intro r hr x;simp [NativeSourceFour.trace])
    (by intro r hr x;simp [NativeSourceFour.trace])
    B_BYTES true (by decide) (by decide) (by decide)
  have he:=congrArg (fun xs : List (List Fp)=>xs.count msg) hm
  simp only [List.count_append,SourceLog22.physicalMessages,←tableBusCount_eq] at he
  change SourceLog22.boundaryCount _ 0 1 2 3 pub B_BYTES true msg=_ at he
  rw [←sourceViewJobs_compiled, jobsToSha_bytes]
  simp only [ite_true,DedupRender.traffic,source_jobs_bytes] at he
  have hid : (fun m : List Fp=>if B_BYTES=B_SIZE then m++[0] else m)=id := by
    funext m
    exact if_neg (by decide)
  rw [hid,List.map_id] at he
  exact he

end ZkFormal.NearV3.Candidates.NativeSourceShaTraffic
