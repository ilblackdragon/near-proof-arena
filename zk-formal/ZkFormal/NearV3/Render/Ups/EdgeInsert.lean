import ZkFormal.NearV3.Render.Ups.RdbCopy
import ZkFormal.Near.Link.NodeSer
import ZkFormal.Near.Render.Proof.NodeSeq

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render NearSpec

theorem kidBitmap_cons (kid : NKid) (kids : List NKid) :
    kidBitmap (kid::kids)=(if kid.present then 1 else 0)+2*kidBitmap kids := by
  rw [Link.kidBitmap_eq,List.map_cons,NodeSeq.bitmapOf_cons,←Link.kidBitmap_eq]
  cases kid <;> simp [NKid.present,NKid.toRec,kidBit]

theorem kidBitmap_last_insert (kids : List NKid) (new : NKid) (hn : new≠.none) :
    kidBitmap (kids++[new])=kidBitmap (kids++[.none])+2^kids.length := by
  induction kids with
  | nil => cases new <;> simp_all [kidBitmap,NKid.present]
  | cons k ks ih =>
    simp only [List.cons_append,kidBitmap_cons,List.length_cons,ih,Nat.pow_succ]
    omega

theorem edge_insert_bitmap (sd : Nat) (kids : List NKid) (new : NKid)
    (hn : new≠.none) (hlen : kids.length=15) :
    kidBitmap (edgeKids sd new (kids.map snapshotKid))=
      kidBitmap (edgeKids sd .none kids)+2^(if sd=1 then 15 else 0) := by
  rw [←bitmap_eq_of_occupancy (edge_occupancy sd new new kids hn hn)]
  by_cases h : sd=1
  · simpa [edgeKids,h,hlen] using kidBitmap_last_insert kids new hn
  · have hp := (kid_present_none new).2 hn
    simp [edgeKids,h,kidBitmap_cons,NKid.present,hp]
    omega

theorem filter_zip_length (bs : List Bool) (ix : List Nat) (h : bs.length≤ix.length) :
    ((bs.zip ix).filter (fun (b,_) => b)).length=(bs.filter id).length := by
  induction bs generalizing ix with
  | nil => simp
  | cons b bs ih =>
    cases ix with
    | nil => simp at h
    | cons i ix =>
      have hh : bs.length≤ix.length := by simpa using h
      cases b <;> simp [ih ix hh]

theorem windows_present_count (kids : List NKid) :
    (NodeGen3.branchWins kids).length=((kidOccupancy kids).filter id).length := by
  rw [windows_occupancy]
  exact filter_zip_length _ _ (by simp [kidOccupancy])

theorem edge_insert_windows (sd : Nat) (kids : List NKid) (new : NKid) (hn : new≠.none) :
    (NodeGen3.branchWins (edgeKids sd new (kids.map snapshotKid))).length=
      (NodeGen3.branchWins (edgeKids sd .none kids)).length+1 := by
  have hp := (kid_present_none new).2 hn
  rw [←windows_eq_of_occupancy (edge_occupancy sd new new kids hn hn)]
  rw [windows_present_count,windows_present_count]
  by_cases h : sd=1 <;> simp [edgeKids,h,kidOccupancy,List.map_map,Function.comp_def,NKid.present,hp]

end ZkFormal.NearV3.Render.UpsGen
