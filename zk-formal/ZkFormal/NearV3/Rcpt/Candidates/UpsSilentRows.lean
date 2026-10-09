import ZkFormal.NearV3.Rcpt.Candidates.UpsInteractionBalance

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render.UpsGen UpsRows

theorem interaction_modes_zero (C D : URow)
    (hS : C UpsV3.mS=0) (hK : C UpsV3.mK=0) (hB : C UpsV3.mB=0)
    (bus : Nat) (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    uMsgs C D bus sd=[] := by
  have hz : Fp.ofNat 0=(0:Fp) := rfl
  have hn : ¬((0:Fp)=1) := by decide
  have ha : (0:Fp)+0=0 := by decide
  rcases hb with rfl|rfl <;> cases sd <;>
    simp [uMsgs,UpsV3.interactions,Dsl.send,Dsl.recv,uMult,uev,Expr.evalWith,uEnv,
      Dsl.c,Dsl.k,B_BMAP,B_EDGE,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_SPOST,B_BYTES,B_UPB,B_MEMD,
      hS,hK,hB,hz,hn,ha]

def generatedRow (Is : List Render.UpsInst) (q : Nat) (r : Nat×RK) : URow :=
  fun c=>((rowCell Is q r c : Int):Fp).toNat

theorem value_modes_zero (Is : List Render.UpsInst) (q i p : Nat) :
    generatedRow Is q (i,.v p) UpsV3.mS=0 ∧
    generatedRow Is q (i,.v p) UpsV3.mK=0 ∧
    generatedRow Is q (i,.v p) UpsV3.mB=0 := by
  exact ⟨rfl,rfl,rfl⟩

theorem part_modes_zero (Is : List Render.UpsInst) (q i k p : Nat) :
    generatedRow Is q (i,.q k p) UpsV3.mS=0 ∧
    generatedRow Is q (i,.q k p) UpsV3.mK=0 ∧
    generatedRow Is q (i,.q k p) UpsV3.mB=0 := by
  exact ⟨rfl,rfl,rfl⟩

theorem value_interactions_silent (Is : List Render.UpsInst) (q i p : Nat) (D : URow)
    (bus : Nat) (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    uMsgs (generatedRow Is q (i,.v p)) D bus sd=[] := by
  have h:=value_modes_zero Is q i p
  exact interaction_modes_zero _ D h.1 h.2.1 h.2.2 bus hb sd

theorem part_interactions_silent (Is : List Render.UpsInst) (q i k p : Nat) (D : URow)
    (bus : Nat) (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    uMsgs (generatedRow Is q (i,.q k p)) D bus sd=[] := by
  have h:=part_modes_zero Is q i k p
  exact interaction_modes_zero _ D h.1 h.2.1 h.2.2 bus hb sd

theorem padding_interactions_silent (D : URow)
    (bus : Nat) (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    uMsgs (fun _=>0) D bus sd=[] :=
  interaction_modes_zero _ D rfl rfl rfl bus hb sd

set_option maxHeartbeats 2000000 in
theorem walk_generated_interactions (Is : List Render.UpsInst) (q i t : Nat) (D : URow)
    (bus : Nat) (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    uMsgs (generatedRow Is q (i,.w t)) D bus sd=
      uMsgs (upsCellRow (inst Is i) t) (fun _=>0) bus sd := by
  rcases hb with rfl|rfl <;> cases sd <;>
    simp [uMsgs,UpsV3.interactions,Dsl.send,Dsl.recv,uMult,uev,Expr.evalWith,uEnv,Dsl.c,Dsl.k,UpsV3.edgeMsg,UpsV3.bmapMsg,
      generatedRow,rowCell,isSeg,upsCellRow,UpsV3.mS,UpsV3.mK,UpsV3.mB,UpsV3.nN,UpsV3.nI,
      UpsV3.nib,UpsV3.nN2,UpsV3.nI2,UpsV3.ek,UpsV3.u,UpsV3.wbm,UpsV3.hv,List.flatMap_cons,List.flatMap_nil,
      B_BMAP,B_EDGE,B_MIDROOT,B_ROOT,B_DIGEST,B_S0F,B_SPLEN,B_SPOST,B_BYTES,B_UPB,B_MEMD,
      Bool.false_eq_true,Bool.true_eq_false,and_self,ite_true,ite_false,
      false_and,true_and,and_false,and_true,List.nil_append,List.append_nil]


end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
