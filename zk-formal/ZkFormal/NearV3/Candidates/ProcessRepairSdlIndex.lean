import ZkFormal.NearV3.Candidates.ProcessRepairSdlIds
import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundIndexSdl
namespace ZkFormal.NearV3.Candidates.ProcessRepairSdlIndex
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec ProcPriorCodecSoundIndexSdl
open ProcPriorRoutedCodecProjection (codec)
theorem sender_index_bound {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (I:PubIdx AP pub Fp.ofNat) (ids : List Nat) (hn:ids.length≤64)
    (hrec:I.recs B_SDL true=dlRecs 0 ids)
    (r : Nat) (hr:r<tr.height 0) (hS:cv (codec tr) 0 r fS=1) :
    cv (codec tr) 0 r kidx<ids.length*ids.length := by
  have hL:=ProcessRepairCodecParameters.local_codec view
  have hrow:=ProcPriorCodecSoundSdlRows.sender_row hL hr hS
  obtain ⟨seed,_,hpublic⟩:=ProcessRepairSdlFinite.public_origin view r hr
    (by rw [hrow.1];decide)
  rw [I.count,hrec] at hpublic
  have hmem:=List.count_pos_iff.mp (Nat.pos_of_ne_zero hpublic)
  have hR:=(ProcPriorCodecSoundGeometry.sender_kind hL hr hS).1
  have hk:=ProcPriorCodecSoundSdlIds.record_index hL hr hR
  have ho:oE.eval (codec tr) 0 r pub=Fp.ofNat (cv (codec tr) 0 r g) := by
    have he:=hrow.2.2.1
    rw [(ProcPriorCodecSoundSdlDescent.messages (codec tr) 0 r pub).1] at he
    have hh:=congrArg (fun xs:List Fp=>xs[3]!) he
    simpa only [ProcPriorCodecSoundSdlDescent.payload,List.map_cons,List.map_nil,
      List.getElem!_cons_succ,List.getElem!_cons_zero] using hh
  exact dl_index (τ:=seed) (o:=cv (codec tr) 0 r g) (b:=cv (codec tr) 0 r bpost) hn hmem (cv_lt r klo) (cv_lt r khi) hk
    (by simp only [ProcPriorCodecSoundSdlDescent.payload,List.map_cons,List.map_nil,ho])
end ZkFormal.NearV3.Candidates.ProcessRepairSdlIndex
