import ZkFormal.NearV3.Render.Ups.CompactAllocated
import ZkFormal.NearV3.Render.Ups.NativeShaByteTraffic
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Near ZkFormal.Algebra ZkFormal.Air UpsRows UpsGen

def compactMsgs (C D : URow) (b : Nat) (sd : Bool) : List Msg :=
  compactInteractions.flatMap fun i=>
    if i.bus=b ∧ i.send=sd then List.replicate (uMult C D i) (i.msg.map fun e=>(uev C D e).toNat) else []

theorem compactMsgs_bytes (C D : URow) (sd : Bool) :
    compactMsgs C D B_BYTES sd=uMsgs C D B_BYTES sd := by
  simp [compactMsgs,compactInteractions,uMsgs,UpsV3.interactions,Dsl.send,Dsl.recv,
    B_BYTES,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_SPOST,B_EDGE,B_BMAP,B_UPB,B_MEMD]

theorem compactRowCell_bytes (insts : List UpsInst) (q i : Nat) (rk : RK) (D : URow) :
    uMsgs (fun x=>((compactRowCell insts q (i,rk) x : Int):Fp).toNat) D B_BYTES true=
      byteRowMsgs (inst insts i) rk := by
  cases rk with
  | w t => exact bytes_zero_row rfl rfl
  | v p =>
    have h:=valueRow_messages (inst insts i) p B_BYTES D true
    simp only [B_SPOST,B_BYTES,Bool.false_eq_true,and_false,ite_false,and_self,ite_true,List.nil_append] at h
    exact h
  | q k p => exact nodeRow_bytes (inst insts i) k p _ D
private theorem range_getD {α : Type} (xs : List α) (d : α) :
    (List.range xs.length).map (fun k=>xs.getD k d)=xs := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2,Option.getD_some]

private theorem flatMap_congr_mem {α β : Type} (xs : List α) (f g : α→List β)
    (h : ∀ x∈xs,f x=g x) : xs.flatMap f=xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,h x (by simp)]
    rw [ih (fun y hy=>h y (by simp [hy]))]

/-- All active physical BYTES sends, in table row order. -/
def compactGeneratedBytes (insts : List UpsInst) : List Msg :=
  (List.range (compactR insts)).flatMap fun q=>
    compactMsgs (fun x=>((compactCell insts q x : Int) : Fp).toNat) (fun _=>0) B_BYTES true

theorem compactGeneratedBytes_recs (insts : List UpsInst) :
    compactGeneratedBytes insts=(compactRecs insts).flatMap (fun r=>byteRowMsgs (inst insts r.1) r.2) := by
  unfold compactGeneratedBytes
  apply Eq.trans (b := (List.range (compactR insts)).flatMap fun q=>
    byteRowMsgs (inst insts ((compactRecs insts).getD q default).1) ((compactRecs insts).getD q default).2)
  · apply flatMap_congr_mem
    intro q hq
    have hq := List.mem_range.mp hq
    simp only [compactCell,hq,ite_true]
    rw [compactMsgs_bytes]
    exact compactRowCell_bytes insts q _ _ _
  · conv => rhs; rw [←range_getD (compactRecs insts) default]
    rw [List.flatMap_map]
    rw [compactRecs_length]

/-- Every physical compact BYTES send is an output-node byte; fresh bytes are
provided separately by the codec relay. -/
theorem compactGeneratedBytes_exact (insts : List UpsInst) :
    compactGeneratedBytes insts=(List.range insts.length).flatMap
      (fun i=>nodeByteMsgs (inst insts i)) := by
  rw [compactGeneratedBytes_recs]
  simp only [compactRecs,List.flatMap_assoc,List.flatMap_map]
  apply flatMap_congr_mem
  intro i hi
  simp [inst,show List.range 4=[0,1,2,3] from rfl,compactRecsI,byteRowMsgs,nodeByteMsgs,
    List.flatMap_append,List.flatMap_map,List.flatMap_assoc,List.map_eq_flatMap,Function.comp_def]
end ZkFormal.NearV3.Render.UpsRelay
