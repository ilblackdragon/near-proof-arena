import ZkFormal.NearV3.Rcpt.Extract.V.BytesViewProof

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem view_rcl_receive_empty (ls : RcptV3Vs) : rcptRecvs3 ls B_RCL=[] := by
  simp [rcptRecvs3,rRecvs,B_RCL,B_DIGEST,B_FINAL,B_MEM,B_SREC,B_AKC,B_BND]

theorem view_rcl_sends (pub : List Fp) (ls : RcptV3Vs) :
    rcptSends3 pub ls B_RCL=(List.range ls.length).map
      (fun j => [j,lOffs (ls.getD j default).rs (ls.getD j default).rs.length]) := by
  simp only [rcptSends3,show B_RCL≠B_BYTES by decide,ite_false,ite_true,List.nil_append,rSends,
    show B_RCL≠B_KEYNIB by decide,show B_RCL≠B_MEM by decide,show B_RCL≠B_RIDS by decide,
    show B_RCL≠B_MPOS by decide,show B_RCL≠B_SREC by decide,show B_RCL≠B_AKC by decide,
    show B_RCL≠B_BND by decide,flatMap_nil_fun,List.append_nil]
  exact (map_eq_flatMap _ _).symm

variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Extracted RCL records equal the existing view's indexed list-length records. -/
theorem ListChain.rcl_view_records {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    bs.map (listRclRecord tr tt)=
      (rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_RCL).map Msg.toFp := by
  rw [view_rcl_sends]
  simp only [List.length_map,List.map_map]
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    have hk : k<bs.length := by simpa using hk
    simp only [List.getElem_map,List.getElem_range,Function.comp_def]
    have hg : (bs.map (ListBlock.view tr tt)).getD k default=bs[k].view tr tt := by
      rw [getD_eq_getElem' _ default (by simpa using hk),List.getElem_map]
    rw [hg]
    simp only [listRclRecord,h.zero_indices hL k hk,ListBlock.view,Msg.toFp,List.map_cons,List.map_nil,natCast_eq]

/-- Complete RCL counts in both directions match the unchanged receipt-view API. -/
theorem ListChain.rcl_view_traffic {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e)
    (m : List Fp) :
    tableBusCount RcptV3.interactions tr tt pub B_RCL true m=
      ((rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_RCL).map Msg.toFp).count m ∧
    tableBusCount RcptV3.interactions tr tt pub B_RCL false m=
      ((rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_RCL).map Msg.toFp).count m := by
  constructor
  · rw [tableBusCount_eq,h.rcl_full hL,h.rcl_view_records hL]
  · rw [tableBusCount_eq,rcl_receive_empty,view_rcl_receive_empty]
    rfl

end ZkFormal.NearV3.RcptV3Proof
