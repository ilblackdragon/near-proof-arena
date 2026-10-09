import ZkFormal.NearV3.Candidates.WindowProviderMetadata

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near

theorem nodeWindowKeys_assigned (q : UseRequests) (vs : List NodeS3) :
    nodeWindowKeys (assignList q 0 vs)=nodeWindowKeys vs := by
  unfold nodeWindowKeys
  rw [assignList_length,List.range_eq_range',assignList_zip,List.flatMap_map]
  simp [List.range_eq_range',assignUses,windowKey]

theorem nodeWindowKeys_chain_member (cs : List Candidates.StoreDuplicateChain.Entry)
    (u : Inputs) (vs : List NodeS3) (key : Msg) (hk : key∈nodeWindowKeys (records u vs)) :
    key∈nodeWindowKeys (records u (Candidates.ChainMetadata.assign cs 0 vs)) := by
  have h:=Candidates.WindowProviderMetadata.member cs ⟨[],[],[]⟩ u vs key hk
  rwa [nodeWindowKeys_assigned] at h

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
