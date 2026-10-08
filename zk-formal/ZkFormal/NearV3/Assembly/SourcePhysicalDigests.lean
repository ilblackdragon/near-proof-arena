import ZkFormal.NearV3.Assembly.SourceBatchDigests
import ZkFormal.NearV3.Assembly.RcptSourceRcOutputs
import ZkFormal.NearV3.Candidates.NativeSourceShaTraffic

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Rcpt.Candidates Candidates RcptSkeleton

theorem accepted_source_rc_digest_partition {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep} {k : WalkD0}
    (ha : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (repeated : Nat→Bool) :
    (Sha.Gen.expectedDigests (sourceShaMessages p.lists w.entries)++
      Sha.Gen.expectedDigests (sourceRcShaJobs k.H.shardId p.lists w.entries)).Perm
      (DedupRender.sourceMsgs (DedupCompile.blocks p.lists w.entries) repeated B_DIGEST false) := by
  have hd : decodeW wb=.ok w := by simp [decodeW,hf,hw,bind,Except.bind]
  rw [source_rc_digest_outputs ha hp hk hd]
  exact accepted_source_digest_partition ha hp hf hw repeated

/-- Full physical source DIGEST conservation: actual four log22 partitions consume
exactly the accepted path hash outputs plus duplicate-gated receipt-list outputs. -/
theorem physical_source_digest_balance {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep} {k : WalkD0}
    (hc : checkD0a B0 cb wb=.ok ()) (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (pub : List Fp) (msg : List Fp) :
    let bs:=DedupCompile.blocks p.lists w.entries
    cnt (Sha.Gen.expectedDigests (sourceShaMessages p.lists w.entries)) msg+
      cnt (Sha.Gen.expectedDigests (sourceRcShaJobs k.H.shardId p.lists w.entries)) msg=
    SourceLog22.boundaryCount (NativeSourceFour.trace bs (sourceRepeated p.lists))
      0 1 2 3 pub B_DIGEST false msg := by
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
    B_DIGEST false (by decide) (by decide) (by decide)
  have he:=congrArg (fun xs : List (List Fp)=>xs.count msg) hm
  simp only [List.count_append,SourceLog22.physicalMessages,←tableBusCount_eq] at he
  change SourceLog22.boundaryCount _ 0 1 2 3 pub B_DIGEST false msg=_ at he
  simp only [Bool.false_eq_true,ite_false,DedupRender.traffic] at he
  have hid : (fun m : List Fp=>if B_DIGEST=B_SIZE then m++[0] else m)=id := by
    funext m
    exact if_neg (by decide)
  rw [hid,List.map_id] at he
  have hd := ((accepted_source_rc_digest_partition h hp hk hf hw (sourceRepeated p.lists)).map Msg.toFp).count_eq msg
  dsimp only
  rw [he]
  simpa only [cnt,List.map_append,List.count_append,show B_DIGEST≠B_SIZE by decide,ite_false] using hd

end ZkFormal.NearV3.Assembly
