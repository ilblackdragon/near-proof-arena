import ZkFormal.NearV3.Candidates.PostNodeLocal
import ZkFormal.NearV3.Candidates.NodeUseSize
import ZkFormal.NearV3.Candidates.PairedStoreKeys

namespace ZkFormal.NearV3.Candidates.PostNodeSize
open ZkFormal.Near ZkFormal.Algebra Rcpt.Candidates.NodePostUpdate

theorem occurrences (u : Inputs) (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE) :
    CombinedStoreOccurrences.allOccurrences (records u vs) tau es=
      CombinedStoreOccurrences.allOccurrences vs tau es := by
  apply PairedStoreKeys.occurrences_of_keys
  simp [records,record,StoreDuplicateMetadata.nodeKey,List.map_map,Function.comp_def,node_pre]

theorem selected_payload (u : Inputs) (vs : List NodeS3) :
    ((records u vs).filter fun s=>!s.dup).map (fun s=>(s.v.ser false).length)=
      (vs.filter fun s=>!s.dup).map (fun s=>(s.v.ser false).length) := by
  simp [records,record,List.filter_map,List.map_map,Function.comp_def,node_pre]

theorem selected_count (u : Inputs) (vs : List NodeS3) :
    ((records u vs).filter fun s=>!s.dup).length=(vs.filter fun s=>!s.dup).length := by
  have h:=congrArg List.length (selected_payload u vs)
  simpa only [List.length_map] using h

theorem view (u : Inputs) (vs : List NodeS3) (es : List ValE) (bs : List SrcpB) :
    SizeComponents.view (records u vs) es bs=SizeComponents.view vs es bs := by
  simp only [SizeComponents.view,selected_payload]

theorem counts (u : Inputs) (vs : List NodeS3) (es : List ValE) :
    SizeComponents.counts (records u vs) es=SizeComponents.counts vs es := by
  simp only [SizeComponents.counts,selected_count]

theorem receiver (u : Inputs) (vs : List NodeS3) (es : List ValE) (bs : List SrcpB)
    (pub : List Fp) (h : SizeCountReceiver.Valid pub (SizeComponents.view vs es bs) (SizeComponents.counts vs es)) :
    SizeCountReceiver.Valid pub (SizeComponents.view (records u vs) es bs)
      (SizeComponents.counts (records u vs) es) := by
  simpa only [view,counts] using h

theorem chain_commute (u : Inputs) (cs : List StoreDuplicateChain.Entry)
    (vs : List NodeS3) (n : Nat) :
    ChainMetadata.assign cs n (records u vs)=records u (ChainMetadata.assign cs n vs) := by
  induction vs generalizing n with
  | nil => rfl
  | cons s ss ih =>
    simp only [records,List.map_cons,ChainMetadata.assign]
    change ChainMetadata.patch cs n (record u s)::ChainMetadata.assign cs (n+1) (records u ss)=
      record u (ChainMetadata.patch cs n s)::records u (ChainMetadata.assign cs (n+1) ss)
    rw [ih];rfl

end ZkFormal.NearV3.Candidates.PostNodeSize
