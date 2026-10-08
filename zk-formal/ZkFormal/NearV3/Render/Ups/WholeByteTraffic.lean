import ZkFormal.NearV3.Render.Ups.AllocatedNodeTraffic
import ZkFormal.NearV3.Render.Ups.AllocatedValueTraffic

set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Algebra ZkFormal.Air UpsRows

theorem bytes_zero_row {C D : URow} (hv : C UpsV3.vb=0) (hq : C UpsV3.qb=0) :
    uMsgs C D B_BYTES true=[] := by
  have hz : ¬ Fp.ofNat 0+Fp.ofNat 0=(1:Fp) := by decide
  have hz0 : ¬ Fp.ofNat 0=(1:Fp) := by decide
  simp [hz0,uMsgs,UpsV3.interactions,Dsl.send,Dsl.recv,uMult,uev,Expr.evalWith,uEnv,
    Dsl.c,hv,hq,hz,B_BYTES,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_SPOST,B_EDGE,B_BMAP,B_UPB,B_MEMD]

def byteRowMsgs (I : UpsInst) : RK→List Msg
  | .w _ => []
  | .v p => [[upsIdN I.tau 0,p%P,(I.v.getD p 0)%P]]
  | .q k p => [[upsIdN I.tau (k+1),p%P,((part I k).q.getD p 0)%P]]

theorem rowCell_bytes (insts : List UpsInst) (q i : Nat) (rk : RK) (D : URow) :
    uMsgs (fun x=>((rowCell insts q (i,rk) x : Int) : Fp).toNat) D B_BYTES true=
      byteRowMsgs (inst insts i) rk := by
  cases rk with
  | w t =>
    apply bytes_zero_row
    · rfl
    · rfl
  | v p =>
    have h := valueRow_messages (inst insts i) p B_BYTES D true
    simp only [B_SPOST,B_BYTES,Bool.false_eq_true,and_false,ite_false,
      and_self,ite_true,List.nil_append] at h
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
def generatedBytes (insts : List UpsInst) : List Msg :=
  (List.range (R insts)).flatMap fun q=>
    uMsgs (fun x=>((cell insts q x : Int) : Fp).toNat) (fun _=>0) B_BYTES true

theorem generatedBytes_recs (insts : List UpsInst) :
    generatedBytes insts=(recs insts).flatMap (fun r=>byteRowMsgs (inst insts r.1) r.2) := by
  unfold generatedBytes
  apply Eq.trans (b := (List.range (R insts)).flatMap fun q=>
    byteRowMsgs (inst insts ((recs insts).getD q default).1) ((recs insts).getD q default).2)
  · apply flatMap_congr_mem
    intro q hq
    have hq := List.mem_range.mp hq
    simp only [cell,hq,ite_true]
    exact rowCell_bytes insts q _ _ _
  · conv => rhs; rw [←range_getD (recs insts) default]
    rw [List.flatMap_map]
    rfl

def valueByteMsgs (I : UpsInst) : List Msg :=
  (List.range (L I)).map fun p=>[upsIdN I.tau 0,p%P,(I.v.getD p 0)%P]
def nodeByteMsgs (I : UpsInst) : List Msg :=
  (List.range (nQ I)).flatMap fun k=>
    (List.range (part I k).q.length).map fun p=>[upsIdN I.tau (k+1),p%P,((part I k).q.getD p 0)%P]

/-- The entire generated table sends exactly the fresh-value and output-node
byte streams. Walk rows send none; no physical byte row is omitted or duplicated. -/
theorem generatedBytes_exact (insts : List UpsInst) :
    generatedBytes insts=(List.range insts.length).flatMap
      (fun i=>valueByteMsgs (inst insts i)++nodeByteMsgs (inst insts i)) := by
  rw [generatedBytes_recs]
  simp only [recs,List.flatMap_assoc,List.flatMap_map]
  apply flatMap_congr_mem
  intro i hi
  simp [inst,show List.range 4=[0,1,2,3] from rfl,recsI,byteRowMsgs,valueByteMsgs,nodeByteMsgs,List.flatMap_append,
    List.flatMap_map,List.flatMap_assoc,List.map_eq_flatMap,Function.comp_def]
end ZkFormal.NearV3.Render.UpsGen
