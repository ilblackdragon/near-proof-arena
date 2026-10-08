import ZkFormal.NearV3.Render.Ups.AllocatedConstraints
import ZkFormal.NearV3.Extract.Ups.MsgRows

set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Algebra ZkFormal.Air UpsRows

/-- Canonical field cells of the native fresh-value rows. -/
def valueRow (I : UpsInst) (p : Nat) : URow := fun x=>((VC I p x : Int) : Fp).toNat

/-- Every fresh scheduler byte is received on SPOST and sent to its actual UPS
SHA job. The statement includes all buses and requires no capacity premise. -/
theorem valueRow_messages (I : UpsInst) (p bb : Nat) (D : URow) (sd : Bool) :
    uMsgs (valueRow I p) D bb sd =
      (if B_SPOST=bb ∧ false=sd then [[I.tau%P,p%P,(I.v.getD p 0)%P]] else []) ++
      (if B_BYTES=bb ∧ true=sd then
        [[upsIdN I.tau 0,p%P,(I.v.getD p 0)%P]] else []) := by
  simp only [uMsgs,UpsV3.interactions,Dsl.send,Dsl.recv,List.flatMap_cons,List.flatMap_nil,
    uMult,uev,Expr.evalWith,uEnv,Dsl.c,Dsl.k,Dsl.smul,UpsV3.upsId,Dsl.mid,
    UpsV3.regs,UpsV3.edgeMsg,UpsV3.bmapMsg,UpsV3.upbMsg,UpsV3.Lexpr,
    List.map_cons,List.map_nil,List.map_append,List.map_map,Function.comp_def]
  have hz : ¬ ((0 : Int) : Fp)=1 := by decide
  have hzz : ¬ (((0 : Int) : Fp)+((0 : Int) : Fp))=1 := by decide
  have hone : (((1 : Int) : Fp)+((0 : Int) : Fp))=1 := by decide
  have hz2 : ¬ (0 : Fp)+0=1 := by decide
  have ho2 : (1 : Fp)+0=1 := rfl
  simp [hz2,ho2,hz,hzz,hone,valueRow,VC,isSeg,segCell,vCell,UpsV3.sf,UpsV3.wt3,UpsV3.gD,UpsV3.vb,
    UpsV3.qb,UpsV3.mS,UpsV3.mK,UpsV3.mB,UpsV3.rd,UpsV3.gMs,UpsV3.gMr,
    UpsV3.tau,UpsV3.j,UpsV3.qpos,UpsV3.b,UpsRows.toNat_id,
    Fp.ofNat_toNat,toNat_natCast,Lean.Grind.Ring.intCast_natCast,Lean.Grind.Ring.intCast_zero,Lean.Grind.Ring.intCast_one]
  have ht : Fp.ofNat (I.tau%P)=Fp.ofNat I.tau := by
    simpa only [Fp.toNat_ofNat] using Fp.ofNat_toNat (Fp.ofNat I.tau)
  rw [ht]
  have hi := UpsRows.toNat_id I.tau 0
  rw [show Fp.ofNat 0=(0:Fp) from rfl] at hi
  rw [hi]
end ZkFormal.NearV3.Render.UpsGen
