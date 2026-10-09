import ZkFormal.NearV3.Rcpt.Candidates.SharedPhysicalEdgeBalance

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near

theorem assigned_bitmap_recv (q : UseRequests) (vs : List NodeS3) :
    nodeRecvs3 (assignList q 0 vs) B_BMAP=(nodeBitmapKeys vs).map (fun e=>e++[q.bmaps.count e]) := by
  rw [assigned_bmaps]
  unfold nodeBitmapKeys
  generalize vs.zip (List.range vs.length)=xs
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    obtain ⟨s,n⟩:=x
    cases hb:s.v.bmap with
    | none=>simp [hb,ih]
    | some p=>obtain ⟨bm,hv⟩:=p;simp [hb,ih]

theorem assigned_bitmap_send (q : UseRequests) (vs : List NodeS3) :
    nodeSends3 (assignList q 0 vs) B_BMAP=(nodeBitmapKeys vs).map (·++[0]) := by
  simp only [nodeSends3,show B_BMAP≠B_BYTES by decide,show B_BMAP≠B_PARENT by decide,
    show B_BMAP≠B_VPARENT by decide,show B_BMAP≠B_EDGE by decide,ite_false,ite_true]
  rw [assignList_length,List.range_eq_range',assignList_zip,List.flatMap_map]
  unfold nodeBitmapKeys
  rw [List.range_eq_range']
  generalize vs.zip (List.range' 0 vs.length)=xs
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    obtain ⟨s,n⟩:=x
    cases hb:s.v.bmap with
    | none=>simp [assignUses] at ih
            simp [assignUses,hb,ih]
    | some p=>
      obtain ⟨bm,hv⟩:=p
      simp [assignUses] at ih
      simp [assignUses,hb,ih]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
