import ZkFormal.NearV3.Render.Ups.PostSnapshot

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def kidOccupancy (kids : List NKid) : List Bool := kids.map NKid.present

@[simp] theorem kid_present_none (k : NKid) : (k.present=true) ↔ k≠.none := by
  cases k <;> simp [NKid.present]

theorem bitmap_occupancy (kids : List NKid) : kidBitmap kids=
    (((kidOccupancy kids).zip (List.range kids.length)).map fun (b,j) => if b then 2^j else 0).sum := by
  simp [kidBitmap,kidOccupancy,List.zip_map_left,Function.comp_def]

theorem bitmap_eq_of_occupancy {ks ds : List NKid} (h : kidOccupancy ks=kidOccupancy ds) :
    kidBitmap ks=kidBitmap ds := by
  have hl : ks.length=ds.length := by simpa [kidOccupancy] using congrArg List.length h
  rw [bitmap_occupancy,bitmap_occupancy,h,hl]

theorem windows_occupancy (kids : List NKid) :
    (NodeGen3.branchWins kids).length=
      (((kidOccupancy kids).zip (List.range kids.length)).filter (fun (b,_) => b)).length := by
  simp only [NodeGen3.branchWins,List.length_map,List.length_zip,List.length_range,Nat.min_self]
  have hp : ∀k : NKid, (!decide (k=.none))=k.present := by intro k; cases k <;> rfl
  simp [kidOccupancy,List.zip_map_left,List.filter_map,Function.comp_def,hp]

theorem windows_eq_of_occupancy {ks ds : List NKid} (h : kidOccupancy ks=kidOccupancy ds) :
    (NodeGen3.branchWins ks).length=(NodeGen3.branchWins ds).length := by
  have hl : ks.length=ds.length := by simpa [kidOccupancy] using congrArg List.length h
  rw [windows_occupancy,windows_occupancy,h,hl]

end ZkFormal.NearV3.Render.UpsGen
