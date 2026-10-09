import ZkFormal.NearV3.Candidates.NodeUseLocal
import ZkFormal.NearV3.Candidates.SizeComponents
namespace ZkFormal.NearV3.Candidates.NodeUseSize
open ZkFormal.Near ZkFormal.Algebra Rcpt.Candidates.NodePostUpdate

theorem selected_payload (q : UseRequests) (vs : List NodeS3) (n : Nat) :
    ((assignList q n vs).filter fun s=>!s.dup).map (fun s=>(s.v.ser false).length)=
      (vs.filter fun s=>!s.dup).map (fun s=>(s.v.ser false).length) := by
  induction vs generalizing n with
  | nil => rfl
  | cons s ss ih =>
    cases hd : s.dup <;> simp [assignList,assignUses,hd,ih]

theorem selected_count (q : UseRequests) (vs : List NodeS3) (n : Nat) :
    ((assignList q n vs).filter fun s=>!s.dup).length=(vs.filter fun s=>!s.dup).length := by
  have hh:=congrArg List.length (selected_payload q vs n)
  simpa only [List.length_map] using hh

theorem view (q : UseRequests) (vs : List NodeS3) (es : List ValE) (bs : List SrcpB) :
    SizeComponents.view (assignList q 0 vs) es bs=SizeComponents.view vs es bs := by
  simp only [SizeComponents.view,selected_payload]

theorem counts (q : UseRequests) (vs : List NodeS3) (es : List ValE) :
    SizeComponents.counts (assignList q 0 vs) es=SizeComponents.counts vs es := by
  simp only [SizeComponents.counts,selected_count]

/-- Provider usage assignment preserves the exact same SIZE receiver cells and
all previously established byte/count budget facts. -/
theorem receiver (q : UseRequests) (vs : List NodeS3) (es : List ValE) (bs : List SrcpB)
    (pub : List Fp) (h : SizeCountReceiver.Valid pub (SizeComponents.view vs es bs) (SizeComponents.counts vs es)) :
    SizeCountReceiver.Valid pub (SizeComponents.view (assignList q 0 vs) es bs)
      (SizeComponents.counts (assignList q 0 vs) es) := by
  simpa only [view,counts] using h
/-- Duplicate-chain metadata and provider-use assignment commute at the same
node index, so both constructions retain their checked meaning. -/
theorem patch_commute (q : UseRequests) (cs : List StoreDuplicateChain.Entry)
    (i j : Nat) (s : NodeS3) :
    ChainMetadata.patch cs i (assignUses q j s)=assignUses q j (ChainMetadata.patch cs i s) := by
  rfl

theorem chain_commute (q : UseRequests) (cs : List StoreDuplicateChain.Entry)
    (vs : List NodeS3) (i j : Nat) :
    ChainMetadata.assign cs i (assignList q j vs)=assignList q j (ChainMetadata.assign cs i vs) := by
  induction vs generalizing i j with
  | nil => rfl
  | cons s ss ih => simp only [ChainMetadata.assign,assignList,patch_commute,ih]

end ZkFormal.NearV3.Candidates.NodeUseSize
