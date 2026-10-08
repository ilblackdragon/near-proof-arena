import ZkFormal.NearV3.Render.Ups.NodeByteTraffic

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Algebra UpsRows

def nodeOffset (I : UpsInst) (k p : Nat) : Nat :=
  4+L I+((List.range k).map fun j=>(part I j).q.length).sum+p

theorem nodeOffset_lt (I : UpsInst) {k p : Nat} (hk : k<nQ I) (hp : p<(part I k).q.length) :
    nodeOffset I k p<(recsI I).length := by
  have hh := sum_mono (g:=fun j=>(part I j).q.length) (i:=k+1) (n:=nQ I) (by omega)
  simp only [List.range_succ,List.map_append,List.sum_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Nat.add_zero] at hh
  simp only [nodeOffset,recsI,List.length_append,List.length_map,List.length_range,List.length_flatMap]
  omega

theorem recsI_node (I : UpsInst) {k p : Nat} (hk : k<nQ I) (hp : p<(part I k).q.length) :
    (recsI I).getD (nodeOffset I k p) default=RK.q k p := by
  have hh := flatMap_getD_pre (fun j=>(List.range (part I j).q.length).map (RK.q j))
    (default : RK) (nQ I) k p hk (by simpa using hp)
  simp only [List.length_map,List.length_range] at hh
  have hprefix : ((List.range 4).map RK.w ++ (List.range (L I)).map RK.v).length≤nodeOffset I k p := by
    simp only [nodeOffset,List.length_append,List.length_map,List.length_range]
    omega
  unfold recsI
  rw [List.getD_eq_getElem?_getD,List.getElem?_append_right hprefix]
  simp only [List.length_append,List.length_map,List.length_range,nodeOffset]
  rw [show 4+L I+((List.range k).map fun j=>(part I j).q.length).sum+p-(4+L I)=
    ((List.range k).map fun j=>(part I j).q.length).sum+p by omega]
  rw [←List.getD_eq_getElem?_getD,hh]
  simp [List.getD_eq_getElem?_getD,hp]

theorem physical_node_cell {insts : List UpsInst} {i k p : Nat}
    (hi : i<insts.length) (hk : k<nQ (inst insts i)) (hp : p<(part (inst insts i) k).q.length)
    (x : Nat) :
    cell insts (start insts i+nodeOffset (inst insts i) k p) x=
      (if isSeg x then segCell (inst insts i) x else
        qCell (inst insts i) k p (uU insts (start insts i+nodeOffset (inst insts i) k p)) x) := by
  have hd := nodeOffset_lt (inst insts i) hk hp
  have hend : start insts i+(recsI (inst insts i)).length≤R insts := by
    rw [←start_succ,←start_len]
    exact sum_mono (by omega)
  rw [cell,ite_eq_left (by omega),recs_seg hi hd,recsI_node _ hk hp]
  rfl

/-- The BYTES send at the physical node-byte row. -/
theorem physical_node_bytes {insts : List UpsInst} {i k p : Nat}
    (hi : i<insts.length) (hk : k<nQ (inst insts i)) (hp : p<(part (inst insts i) k).q.length)
    (D : URow) :
    uMsgs (fun x=>((cell insts (start insts i+nodeOffset (inst insts i) k p) x : Int) : Fp).toNat)
      D B_BYTES true=
      [[upsIdN (inst insts i).tau (k+1),p%P,((part (inst insts i) k).q.getD p 0)%P]] := by
  simp only [physical_node_cell hi hk hp]
  exact nodeRow_bytes _ _ _ _ _
end ZkFormal.NearV3.Render.UpsGen
