import ZkFormal.NearV3.Rcpt.Candidates.UpsInteractionCells

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Algebra Render.UpsGen UpsRows

def reduceMessage (m : Msg) : Msg := m.map (fun n=>(Fp.ofNat n).toNat)
/-- Exact interaction rows W0 through W3, in physical instance order. -/
def upsWalkMessages (Is : List Render.UpsInst) (bus : Nat) (sd : Bool) : List Msg :=
  Is.flatMap (fun I=>(List.ofFn (fun i : Fin 4=>i)).flatMap
    (fun (i : Fin 4)=>uMsgs (upsCellRow I i) (fun _=>0) bus sd))

private theorem select_flat {α : Type} (xs : List α) (p : α→Prop) [DecidablePred p]
    (f : α→Msg) :
    (xs.filterMap (fun x=>if p x then some (f x) else none)).map reduceMessage=
      xs.flatMap (fun x=>if p x then [reduceMessage (f x)] else []) := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>by_cases h : p x <;> simp [h,ih]

private theorem flat_congr {α β : Type} (xs : List α) (f g : α→List β)
    (h : ∀x∈xs,f x=g x) : xs.flatMap f=xs.flatMap g := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp only [List.flatMap_cons];rw [h x (by simp),ih (fun y hy=>h y (by simp [hy]))]

theorem synced_instance_edges (I : Render.UpsInst)
    (hl : ∀t<4,(step I t).mode≤1→(step I t).e.length=6) (sd : Bool) :
    upsWalkMessages [syncUps I] B_EDGE sd=(edgeTraffic (fourSteps I) sd).map reduceMessage := by
  simp only [upsWalkMessages,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [edgeTraffic,select_flat]
  have he : fourSteps I=(List.ofFn (fun i : Fin 4=>i)).map (fun (i : Fin 4)=>step I i) := by
    simp only [List.map_ofFn,fourSteps,Function.comp_def]
  rw [he,List.flatMap_map]
  apply flat_congr
  intro i hi
  exact synced_edge_interaction I i (fun _=>0) sd (hl i i.isLt)

theorem synced_instance_bitmaps (I : Render.UpsInst) (sd : Bool) :
    upsWalkMessages [syncUps I] B_BMAP sd=(bitmapTraffic (fourSteps I) sd).map reduceMessage := by
  simp only [upsWalkMessages,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [bitmapTraffic,select_flat]
  have he : fourSteps I=(List.ofFn (fun i : Fin 4=>i)).map (fun (i : Fin 4)=>step I i) := by
    simp only [List.map_ofFn,fourSteps,Function.comp_def]
  rw [he,List.flatMap_map]
  apply flat_congr
  intro i hi
  exact synced_bitmap_interaction I i (fun _=>0) sd

theorem synced_list_edges (Is : List Render.UpsInst)
    (hl : ∀I∈Is,∀t<4,(step I t).mode≤1→(step I t).e.length=6) (sd : Bool) :
    upsWalkMessages (Is.map syncUps) B_EDGE sd=
      (edgeTraffic (Is.flatMap fourSteps) sd).map reduceMessage := by
  induction Is with
  | nil=>rfl
  | cons I Is ih=>
    have h:=synced_instance_edges I (hl I (by simp)) sd
    have ht:=ih (fun J hJ=>hl J (by simp [hJ]))
    simpa only [upsWalkMessages,List.map_cons,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      edgeTraffic,List.filterMap_append,List.map_append] using congr (congrArg (fun (a b : List Msg)=>a++b) h) ht

theorem synced_list_bitmaps (Is : List Render.UpsInst) (sd : Bool) :
    upsWalkMessages (Is.map syncUps) B_BMAP sd=
      (bitmapTraffic (Is.flatMap fourSteps) sd).map reduceMessage := by
  induction Is with
  | nil=>rfl
  | cons I Is ih=>
    have h:=synced_instance_bitmaps I sd
    simpa only [upsWalkMessages,List.map_cons,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      bitmapTraffic,List.filterMap_append,List.map_append] using congr (congrArg (fun (a b : List Msg)=>a++b) h) ih

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
