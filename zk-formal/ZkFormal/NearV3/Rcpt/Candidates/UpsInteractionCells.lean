import ZkFormal.NearV3.Rcpt.Candidates.UpsEdgeArity

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render.UpsGen UpsRows

/-- Canonical row obtained from the actual integer generator. -/
def upsCellRow (I : Render.UpsInst) (t : Nat) : URow :=
  fun c=>((wCell I t c : Int):Fp).toNat

theorem upsCellRow_eval (I : Render.UpsInst) (t c : Nat) :
    Fp.ofNat (upsCellRow I t c)=((wCell I t c : Int):Fp) :=
  Fp.ofNat_toNat _

theorem ups_bitmap_interaction (I : Render.UpsInst) (t : Nat) (D : URow) (sd : Bool) :
    uMsgs (upsCellRow I t) D B_BMAP sd=
      if (step I t).mode=2 then
        [(upsBitmapCells I t sd).map (fun (z : Int)=>(z:Fp).toNat)] else [] := by
  have h0 : ((0:Int):Fp)=0 := rfl
  have h1 : ((1:Int):Fp)=1 := rfl
  have hn : ¬((0:Fp)=1) := by decide
  cases sd <;> by_cases hm : (step I t).mode=2 <;>
    simp [uMsgs,UpsV3.interactions,Dsl.send,Dsl.recv,uMult,uev,Expr.evalWith,uEnv,
      Dsl.c,Dsl.k,UpsV3.bmapMsg,UpsV3.mB,UpsV3.nN,UpsV3.wbm,UpsV3.hv,UpsV3.u,
      B_BMAP,B_EDGE,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_SPOST,B_BYTES,B_UPB,B_MEMD,
      upsCellRow_eval,upsBitmapCells,wCell,hm,ind,h0,h1,hn]
  change _ = _
  rw [show (((step I t).u : Int)+1 : Int)=(↑((step I t).u+1):Int) by omega]
  change (Fp.ofNat (step I t).u+Fp.ofNat 1).toNat=(Fp.ofNat ((step I t).u+1)).toNat
  exact congrArg Fp.toNat (ofNat_add' _ _)

theorem ups_edge_interaction (I : Render.UpsInst) (t : Nat) (D : URow) (sd : Bool) :
    uMsgs (upsCellRow I t) D B_EDGE sd=
      if (step I t).mode≤1 then
        [(upsEdgeCells I t sd).map (fun (z : Int)=>(z:Fp).toNat)] else [] := by
  have h0 : ((0:Int):Fp)=0 := rfl
  have h1 : ((1:Int):Fp)=1 := rfl
  have hn : ¬((0:Fp)=1) := by decide
  have z0 : (0:Fp)+0=0 := by decide
  have z1 : (0:Fp)+1=1 := by decide
  have z2 : (1:Fp)+0=1 := by decide
  have hadd (n : Nat) : (((n:Int):Fp)+((1:Nat):Fp)).toNat=(((n:Int)+1:Int):Fp).toNat := by
    rw [show ((n:Int)+1:Int)=(↑(n+1):Int) by omega]
    change (Fp.ofNat n+Fp.ofNat 1).toNat=(Fp.ofNat (n+1)).toNat
    exact congrArg Fp.toNat (ofNat_add' _ _)
  cases sd <;> by_cases hm0 : (step I t).mode=0 <;> by_cases hm1 : (step I t).mode=1 <;>
    have hle : ((step I t).mode≤1) ↔ ((step I t).mode=0 ∨ (step I t).mode=1) := by omega
  all_goals
    simp [uMsgs,UpsV3.interactions,Dsl.send,Dsl.recv,uMult,uev,Expr.evalWith,uEnv,
      Dsl.c,Dsl.k,UpsV3.edgeMsg,UpsV3.mS,UpsV3.mK,UpsV3.nN,UpsV3.nI,UpsV3.nib,
      UpsV3.nN2,UpsV3.nI2,UpsV3.ek,UpsV3.u,
      B_BMAP,B_EDGE,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_SPOST,B_BYTES,B_UPB,B_MEMD,
      upsCellRow_eval,upsEdgeCells,wCell,hm0,hm1,ind,h0,h1,hn,hle,z0,z1,z2,hadd] <;> omega

theorem synced_edge_interaction (I : Render.UpsInst) (t : Nat) (D : URow) (sd : Bool)
    (hl : (step I t).mode≤1 → (step I t).e.length=6) :
    uMsgs (upsCellRow (syncUps I) t) D B_EDGE sd=
      if (step I t).mode≤1 then
        [((step I t).e++[(step I t).u+(if sd then 1 else 0)]).map
          (fun (n : Nat)=>(Fp.ofNat n).toNat)] else [] := by
  rw [ups_edge_interaction,syncUps_mode]
  by_cases hm : (step I t).mode≤1
  · simp only [ite_eq_left hm]
    rw [synced_edge_cells I t sd hm (hl hm)]
    simp only [List.map_map,Function.comp_def]
    rfl
  · simp [hm]

theorem synced_bitmap_interaction (I : Render.UpsInst) (t : Nat) (D : URow) (sd : Bool) :
    uMsgs (upsCellRow (syncUps I) t) D B_BMAP sd=
      if (step I t).mode=2 then
        [[(step I t).e.getD 0 0,(step I t).bm,(step I t).hv,
          (step I t).ub+(if sd then 1 else 0)].map
            (fun (n : Nat)=>(Fp.ofNat n).toNat)] else [] := by
  rw [ups_bitmap_interaction,syncUps_mode]
  by_cases hm : (step I t).mode=2
  · simp only [ite_eq_left hm]
    rw [synced_bitmap_cells I t sd hm]
    cases sd <;> simp only [Bool.false_eq_true,if_false,if_true,List.map_cons,List.map_nil,Nat.add_zero,Int.add_zero]
    · rfl
    · rw [show (((step I t).ub:Int)+1:Int)=(↑((step I t).ub+1):Int) by omega]
      rfl
  · simp [hm]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
