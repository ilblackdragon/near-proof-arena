import ZkFormal.NearV3.Rcpt.Candidates.UpsSharedTraffic

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near Render.UpsGen

/-- Actual EDGE interaction columns, including the shared use column. -/
def upsEdgeCells (I : Render.UpsInst) (t : Nat) (sd : Bool) : List Int :=
  [wCell I t 49,wCell I t 50,wCell I t 51,wCell I t 52,wCell I t 53,
   wCell I t 54,wCell I t 105+(if sd then 1 else 0)]
/-- Actual BMAP interaction columns, including the shared use column. -/
def upsBitmapCells (I : Render.UpsInst) (t : Nat) (sd : Bool) : List Int :=
  [wCell I t 49,wCell I t 57,wCell I t 56,wCell I t 105+(if sd then 1 else 0)]

private theorem six_getD (es : List Nat) (h : es.length=6) :
    [es.getD 0 0,es.getD 1 0,es.getD 2 0,es.getD 3 0,es.getD 4 0,es.getD 5 0]=es := by
  match es with
  | [a,b,c,d,e,f] => rfl
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | _::_::_::_::_::_::_::_ => simp_all

theorem ups_edge_cells (I : Render.UpsInst) (t : Nat) (sd : Bool)
    (hl : (step I t).e.length=6) :
    upsEdgeCells I t sd=((step I t).e++[(step I t).u+(if sd then 1 else 0)]).map (fun (n : Nat)=>(n:Int)) := by
  have he:=six_getD (step I t).e hl
  change ([(step I t).e.getD 0 0,(step I t).e.getD 1 0,(step I t).e.getD 2 0,
      (step I t).e.getD 3 0,(step I t).e.getD 4 0,(step I t).e.getD 5 0].map (fun (n : Nat)=>(n:Int)))++
      [((step I t).u:Int)+(if sd then 1 else 0)]=_
  rw [he,List.map_append]
  cases sd <;> simp

theorem ups_bitmap_cells (I : Render.UpsInst) (t : Nat) (sd : Bool)
    (hm : (step I t).mode=2) :
    upsBitmapCells I t sd=
      [((step I t).e.getD 0 0:Int),(step I t).bm,(step I t).hv,
        ((step I t).u:Int)+(if sd then 1 else 0)] := by
  simp [upsBitmapCells,wCell,hm]

theorem synced_edge_cells (I : Render.UpsInst) (t : Nat) (sd : Bool)
    (hm : (step I t).mode≤1) (hl : (step I t).e.length=6) :
    upsEdgeCells (syncUps I) t sd=
      ((step I t).e++[(step I t).u+(if sd then 1 else 0)]).map (fun (n : Nat)=>(n:Int)) := by
  rw [ups_edge_cells _ _ _ (by simpa using hl),syncUps_edge,syncUps_counter]
  simp [show (step I t).mode≠2 by omega]

theorem synced_bitmap_cells (I : Render.UpsInst) (t : Nat) (sd : Bool)
    (hm : (step I t).mode=2) :
    upsBitmapCells (syncUps I) t sd=
      [((step I t).e.getD 0 0:Int),(step I t).bm,(step I t).hv,
        ((step I t).ub:Int)+(if sd then 1 else 0)] := by
  rw [ups_bitmap_cells _ _ _ (by simpa using hm)]
  simp [syncUps_counter,hm]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
